{-# LANGUAGE NamedFieldPuns #-}

module PToI where

import Data.List (nub)
import qualified Data.Map as M
import ITypes
import PTypes

trTm :: PTm -> ITm
trTm (PTmNat n) = ITmNat n
trTm (PTmPlus t1 t2) = ITmPlus (trTm t1) (trTm t2)
trTm (PTmBool b) = ITmBool b
trTm PTmUnit = ITmUnit
trTm (PTmNot t) = ITmNot (trTm t)
trTm (PTmPTy t) = ITmTy (trTy t)
trTm (PTmVar x) = ITmVar x
trTm (PTmCon x cs) = ITmCon x (map trTm cs)
-- trTm (PTmFunc f) = ITmFunc $ unLoopFunc f
trTm (PTmFuncCall f args) = ITmFuncCall (trTm f) (map trTm args)
trTm (PTmIf c t e) = ITmIf (trTm c) (trTm t) (trTm e)
trTm (PTmMinus t1 t2) = ITmMinus (trTm t1) (trTm t2)
trTm (PTmMult t1 t2) = ITmMult (trTm t1) (trTm t2)
trTm (PTmDiv t1 t2) = ITmDiv (trTm t1) (trTm t2)
trTm (PTmMod t1 t2) = ITmMod (trTm t1) (trTm t2)
trTm (PTmBEq t1 t2) = ITmBEq (trTm t1) (trTm t2)
trTm (PTmBLT t1 t2) = ITmBLT (trTm t1) (trTm t2)
trTm (PTmList t1 xs) = ITmList (trTy t1) (map trTm xs)
trTm (PTmFunc f) = ITmFunc (trFunc f)

convIf :: ITm -> ITm -> ITm -> ITm
convIf c t e = ITmMatch [c] [([ITmCon "No" [ITmVar "noprf"]], e), ([ITmCon "Yes" [ITmVar "yesprf"]], t)]

trBody :: Stmt -> Func -> (ITm, List ITm)
trBody x f = case x of
  StBlock ls -> trListStmt ls (mapFromFuncArgs (funcArgs f) M.empty) f []
  _ -> trListStmt [x] (mapFromFuncArgs (funcArgs f) M.empty) f []

mapFromFuncArgs :: List AnnParam -> M.Map String PTy -> M.Map String PTy
mapFromFuncArgs [] m = m
mapFromFuncArgs ((AnnParam (ty, var) _) : xs) m = mapFromFuncArgs xs (M.insert var ty m)

mapToAnnParam :: M.Map String PTy -> List AnnParam
mapToAnnParam m = map (\(v, ty) -> AnnParam (ty, v) True) (M.toList m)

trListStmt :: List Stmt -> M.Map String PTy -> Func -> List ITm -> (ITm, List ITm)
trListStmt [StSkip] _ _ _ = error "cannot end with skip i think"
trListStmt (StSkip : xs) m f i = trListStmt xs m f i
trListStmt [] _ _ i = (ITmUnit, i)
trListStmt [StBlock s] m f i = trListStmt s m f i
trListStmt (StBlock s : xs) m f i = trListStmt (s ++ xs) m f i
trListStmt [StReturn t] _ _ i = (trTm t, i)
trListStmt (StReturn t : _ : _) _ _ _ = error "return should be the last statement in the block"
trListStmt (StIf t s1 s2 : xs) m f i =
  let (t1, i1) = trListStmt (s1 : xs) m f i
      (t2, i2) = trListStmt (s2 : xs) m f i
   in (convIf (trTm t) t1 t2, i ++ i1 ++ i2)
trListStmt (StDeclAssign (Just ty) x t : xs) m f i =
  let (t', i') = trListStmt xs (M.insert x ty m) f i
   in (ITmLet x (Just (trTy ty)) (trTm t) t', i ++ i')
trListStmt (StDeclAssign Nothing x t : xs) m f i =
  let (t', i') = trListStmt xs (M.insert x PTyHole m) f i
   in (ITmLet x Nothing (trTm t) t', i ++ i')
trListStmt (StAssign x t : xs) m f i =
  let (t', i') = trListStmt xs m f i
   in (ITmLet x (trTy <$> M.lookup x m) (trTm t) t', i ++ i')
trListStmt (StWhile t s : xs) m f i =
  let (body, innerName, innerParams) = defOuter (funcName f) (funcArgs f ++ mapToAnnParam m) (length i)
      innerFunc = defInner t s innerName (funcRetTy f) xs innerParams
   in (\(x, y) -> (x, (ITmFunc $ trFunc innerFunc) : y)) (trBody body f)
trListStmt (StSwitch Switch {switchOn, cases} : xs) m f i =
  let tmp = map (\(Case {caseOn, caseBody}) -> (map trTm caseOn, trListStmt (caseBody : xs) m f i)) cases
      branches = map (\(tm, (st, i)) -> ((tm, st), i)) tmp
   in ( ITmMatch
          (map trTm switchOn)
          (map fst branches),
        i ++ concatMap snd branches
      )

getHVars :: List Stmt -> M.Map String (Maybe PTy) -> List (String, Maybe PTy)
getHVars [] m = M.toList m
getHVars (x : xs) m = case x of
  StDeclAssign ty v _ -> getHVars xs (M.insert v ty m)
  StAssign _ _ -> error "assignment should have been transformed"
  StBlock _ -> error "todo"
  _ -> getHVars xs m

-- todo may have to add the header
defOuter :: String -> List AnnParam -> Int -> (Stmt, String, List AnnParam)
defOuter funcName funcArgs i =
  let funcInner = funcName ++ "_rec" ++ show i
      ps = nubAnnParam M.empty funcArgs []
   in ( StBlock [StReturn (PTmFuncCall (PTmVar funcInner) (nub $ map (PTmVar . getAnnParamVar) ps))],
        funcInner,
        ps
      )

defInner :: PTm -> Stmt -> String -> PTy -> List Stmt -> List AnnParam -> Func
defInner condition body fname retty tl ps =
  Func
    { funcName = fname,
      funcArgs = ps,
      funcRetTy = retty,
      funcBody =
        StSwitch
          Switch
            { switchOn = [condition],
              cases =
                [ Case
                    { caseOn = [PTmCon "No" [PTmVar "noprf"]],
                      caseBody = StBlock tl
                    },
                  Case
                    { caseOn = [PTmCon "Yes" [PTmVar "yesprf"]],
                      caseBody = StBlock $ body : [StReturn (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) ps))]
                    }
                ]
            }
    }

trTy :: PTy -> ITy
trTy PTyNat = ITyNat
trTy PTyBool = ITyBool
trTy PTyUnit = ITyUnit
trTy PTyTy = ITyTy
trTy PTyFunc {tyFuncArgs, tyFuncRetTy} = ITyFunc $ map (\(x, y) -> (Just y, trTy x)) tyFuncArgs ++ [(Nothing, trTy tyFuncRetTy)]
trTy PTyCustom {tyName, tyParams} = ITyCustom tyName (map trTm tyParams)
trTy (PTyPTm t) = ITyTm (trTm t)
trTy (PTyList t) = ITyList (trTy t)
trTy PTyHole = ITyHole

trDecl :: Decl -> IDecl
trDecl (PTy tydecl) = ITy $ trTyDecl tydecl
trDecl (Rec recdecl) = IRec $ trRecDecl recdecl

trTyDecl :: TyDecl -> ITyDecl
trTyDecl
  TyDecl
    { tyDeclName,
      tyDeclParams,
      tyDeclConstructors
    } =
    ITyDecl
      { iTyDeclName = tyDeclName,
        iTyDeclParams = map trAnnParam tyDeclParams,
        iTyDeclConstructors = map trConstructor tyDeclConstructors
      }

trRecDecl :: RecDecl -> IRecDecl
trRecDecl
  RecDecl
    { recDeclName,
      recDeclParams,
      recDeclFields
    } =
    IRecDecl
      { iRecDeclName = recDeclName,
        iRecDeclParams = map trAnnParam recDeclParams,
        iRecDeclConstructor = "mk" ++ recDeclName,
        iRecDeclFields = map (trAnnParam . (`AnnParam` True)) recDeclFields
      }

trFunc :: Func -> IFunc
trFunc
  f@Func
    { funcName,
      funcRetTy,
      funcArgs,
      funcBody
    } =
    let (b, w) = trBody funcBody f
     in IFunc
          { iFuncName = funcName,
            iFuncRetTy = trTy funcRetTy,
            iFuncArgs = map trAnnParam funcArgs,
            iFuncBody = b,
            iWhere = w
          }

trConstructor :: Constructor -> IConstructor
trConstructor
  Constructor
    { conName,
      conArgs,
      conTy
    } =
    IConstructor
      { iConName = conName,
        iConArgs = map trAnnParam conArgs,
        iConTy = trTy conTy
      }

trAnnParam :: AnnParam -> IAnnParam
trAnnParam (AnnParam (ty, str) vis) = IAnnParam (str, trTy ty) vis

getAnnParamVar :: AnnParam -> String
getAnnParamVar (AnnParam (_, str) _) = str

getAnnParamPTy :: AnnParam -> PTy
getAnnParamPTy (AnnParam (ty, _) _) = ty

nubAnnParam :: M.Map String (PTy, Bool) -> List AnnParam -> List AnnParam -> List AnnParam
nubAnnParam m [] lnew = lnew
nubAnnParam m (x@(AnnParam (ty, v) vis) : xs) lnew = case M.lookup v m of
  Nothing -> nubAnnParam (M.insert v (ty, vis) m) xs (lnew ++ [x])
  Just _ -> nubAnnParam m xs lnew