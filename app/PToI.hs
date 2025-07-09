{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use if" #-}

module PToI where

import Data.List (nub, unsnoc)
import qualified Data.Map as M
import Data.Tuple (swap)
import ITypes
import PTypes

trTm :: PTm -> ITm
trTm (PTmNat n) = ITmNat n
trTm (PTmPlus t1 t2) =
  let t1' = trTm t1
      t2' = trTm t2
      tS = ITmCon "S"
   in if t1' == ITmNat 1 then tS [t2'] else ITmPlus t1' t2'
trTm (PTmBool b) = ITmBool b
trTm PTmUnit = ITmUnit
trTm (PTmNot t) = ITmNot (trTm t)
trTm (PTmPTy t) = ITmTy (trTy t)
trTm (PTmVar x) = ITmVar x
trTm PTmWildCard = ITmWildCard
trTm (PTmCon x cs) = ITmCon x (map trTm cs)
trTm (PTmFuncCall f args) = ITmFuncCall (trTm f) (map trTm args)
trTm (PTmIf c t e) = ITmIf (trTm c) (trTm t) (trTm e)
trTm (PTmMinus t1 t2) = ITmMinus (trTm t1) (trTm t2)
trTm (PTmMult t1 t2) = ITmMult (trTm t1) (trTm t2)
trTm (PTmDiv t1 t2) = ITmDiv (trTm t1) (trTm t2)
trTm (PTmMod t1 t2) = ITmMod (trTm t1) (trTm t2)
trTm (PTmBEq t1 t2) = ITmBEq (trTm t1) (trTm t2)
trTm (PTmBAnd t1 t2) = ITmBAnd (trTm t1) (trTm t2)
trTm (PTmBOr t1 t2) = ITmBOr (trTm t1) (trTm t2)
trTm (PTmBLT t1 t2) = ITmBLT (trTm t1) (trTm t2)
trTm (PTmList t1 xs) = ITmList (trTy t1) (map trTm xs)
trTm (PTmFunc f) = ITmFunc (trFunc f)

trBool :: ITm -> ITm
trBool (ITmBLT t1 t2) = ITmFuncCall (ITmVar "isLT") [t1, t2]
trBool (ITmBEq t1 t2) = ITmFuncCall (ITmVar "decEq") [t1, t2]
trBool (ITmBAnd t1 t2) = ITmBAnd (trBool t1) (trBool t2)
trBool (ITmBOr t1 t2) = ITmBOr (trBool t1) (trBool t2)
trBool (ITmNot t) = ITmNot (trBool t)
trBool x = x

trPBool :: PTm -> PTm
trPBool (PTmBLT t1 t2) = PTmFuncCall (PTmVar "isLT") [t1, t2]
trPBool (PTmBEq t1 t2) = PTmFuncCall (PTmVar "decEq") [t1, t2]
trPBool (PTmBAnd t1 t2) = PTmBAnd (trPBool t1) (trPBool t2)
trPBool (PTmBOr t1 t2) = PTmBOr (trPBool t1) (trPBool t2)
trPBool (PTmNot t) = PTmNot (trPBool t)
trPBool x = x

convIf :: ITm -> ITm -> ITm -> ITm
convIf c t e = ITmMatch [trBool c] [([ITmCon "No" [ITmVar "noprf"]], e), ([ITmCon "Yes" [ITmVar "yesprf"]], t)]

trBody :: Stmt -> Func -> (ITm, List ITm)
trBody x f = case x of
  StBlock ls -> trListStmt ls (mapFromFuncArgs (funcArgs f) M.empty) (map (\x -> (getAnnParamVar x, getAnnParamPTy x)) (funcArgs f)) f []
  _ -> trListStmt [x] (mapFromFuncArgs (funcArgs f) M.empty) (map (\x -> (getAnnParamVar x, getAnnParamPTy x)) (funcArgs f)) f []

mapFromFuncArgs :: List AnnParam -> M.Map String PTy -> M.Map String PTy
mapFromFuncArgs [] m = m
mapFromFuncArgs ((AnnParam (ty, var) _) : xs) m = mapFromFuncArgs xs (M.insert var ty m)

mapToAnnParam :: M.Map String PTy -> List AnnParam
mapToAnnParam m = map (\(v, ty) -> AnnParam (ty, v) True) (M.toList m)

trListStmt :: List Stmt -> M.Map String PTy -> List (String, PTy) -> Func -> List ITm -> (ITm, List ITm)
trListStmt [StSkip] _ _ _ _ = error "cannot end with skip i think"
trListStmt (StSkip : xs) m ls f i = trListStmt xs m ls f i
trListStmt [] _ _ _ i = (ITmUnit, i)
trListStmt [StBlock s] m ls f i = trListStmt s m ls f i
trListStmt (StBlock s : xs) m ls f i = trListStmt (s ++ xs) m ls f i
trListStmt [StReturn t] _ _ _ i = (trTm t, i)
trListStmt (StReturn t : _ : _) _ _ _ _ = error "return should be the last statement in the block"
trListStmt (StIf t s1 s2 : xs) m ls f i =
  let (t1, i1) = trListStmt (s1 : xs) m ls f i
      (t2, i2) = trListStmt (s2 : xs) m ls f (i ++ i1)
   in (ITmIf (trTm t) t1 t2, i ++ i2)
trListStmt (StEIf t s1 s2 : xs) m ls f i =
  let (t1, i1) = trListStmt (s1 : xs) m ls f i
      (t2, i2) = trListStmt (s2 : xs) m ls f (i ++ i1)
   in (convIf (trTm t) t1 t2, i ++ i2)
trListStmt (StDeclAssign (Just ty) x t : xs) m ls f i =
  let (t', i') = trListStmt xs (M.insert x ty m) (ls ++ [(x, ty)]) f i
   in (ITmLet x (Just (trTy ty)) (trTm t) t', i ++ i')
trListStmt (StDeclAssign Nothing x t : xs) m ls f i =
  let (t', i') = trListStmt xs (M.insert x PTyHole m) (ls ++ [(x, PTyHole)]) f i
   in (ITmLet x Nothing (trTm t) t', i ++ i')
trListStmt (StAssign x t : xs) m ls f i =
  let (t', i') = trListStmt xs m ls f i
   in (ITmLet x (trTy <$> M.lookup x m) (trTm t) t', i ++ i')
trListStmt (StWhile t s : xs) m ls f i =
  let (body, innerName, innerParams) = defOuter (funcName f) (funcArgs f ++ map ((`AnnParam` True) . swap) ls) (length i)
      innerFunc = defInner t s innerName (funcRetTy f) xs innerParams False
   in (\(x, y) -> (x, (ITmFunc $ trFunc innerFunc) : y)) (trBody body f)
trListStmt (StEWhile t s : xs) m ls f i =
  let (body, innerName, innerParams) = defOuter (funcName f) (funcArgs f ++ map ((`AnnParam` True) . swap) ls) (length i)
      innerFunc = defInner t s innerName (funcRetTy f) xs innerParams True
   in (\(x, y) -> (x, (ITmFunc $ trFunc innerFunc) : y)) (trBody body f)
trListStmt (StSwitch Switch {switchOn, cases, defaultCase} : xs) m ls f i =
  let def = case defaultCase of
        Nothing -> []
        Just c -> [c]
      tmp = map (\(Case {caseOn, caseBody}) -> (if null caseOn then replicate (length switchOn) ITmWildCard else map trTm caseOn, trListStmt (caseBody : xs) m ls f i)) (cases ++ def)
      branches = map (\(tm, (st, i)) -> ((tm, st), i)) tmp
   in ( ITmMatch
          (map trTm switchOn)
          (map fst branches),
        i ++ concatMap snd branches
      )

defOuter :: String -> List AnnParam -> Int -> (Stmt, String, List AnnParam)
defOuter funcName funcArgs i =
  let funcInner = funcName ++ "_rec" ++ show i
      ps = nubAnnParam M.empty funcArgs []
   in ( StBlock [StReturn (PTmFuncCall (PTmVar funcInner) (nub $ map (PTmVar . getAnnParamVar) ps))],
        funcInner,
        ps
      )

defInner :: PTm -> Stmt -> String -> PTy -> List Stmt -> List AnnParam -> Bool -> Func
defInner condition body fname retty tl ps e =
  let ebdy =
        StSwitch
          Switch
            { switchOn = [trPBool condition],
              cases =
                [ Case
                    { caseOn = [PTmCon "No" [PTmVar "noprf"]],
                      caseBody = StBlock tl
                    },
                  Case
                    { caseOn = [PTmCon "Yes" [PTmVar "yesprf"]],
                      caseBody = StBlock $ body : [StReturn (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) ps))]
                    }
                ],
              defaultCase = Nothing
            }
      bdy = StIf condition (StBlock $ body : [StReturn (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) ps))]) (StBlock tl)
   in Func
        { funcName = fname,
          funcArgs = ps,
          funcRetTy = retty,
          funcBody = if e then ebdy else bdy
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
        iRecDeclConstructor = "Mk" ++ recDeclName,
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
nubAnnParam _ [] lnew = lnew
nubAnnParam m (x@(AnnParam (ty, v) vis) : xs) lnew = case M.lookup v m of
  Nothing -> nubAnnParam (M.insert v (ty, vis) m) xs (lnew ++ [x])
  Just _ -> nubAnnParam m xs lnew

getIAnnParamVar :: IAnnParam -> String
getIAnnParamVar (IAnnParam (str, _) _) = str

dontDoTheseTypes :: [ITy]
dontDoTheseTypes =
  [ -- ITyNat,
    -- ITyBool,
    -- ITyUnit,
    ITyTy
  ]

inConTyTm :: String -> ITm -> Bool
inConTyTm vname (ITmVar x) = vname == x
inConTyTm vname (ITmCon _ xs) = any (inConTyTm vname) xs
inConTyTm vname (ITmFuncCall _ xs) = any (inConTyTm vname) xs
inConTyTm _ _ = False

inConTy :: String -> ITy -> Bool
inConTy vname (ITyCustom _ tms) = any (inConTyTm vname) tms
inConTy vname (ITyTm tm) = inConTyTm vname tm
inConTy _ _ = False

deriveDecEq :: IDecl -> IImplementation
deriveDecEq
  ( ITy
      ( ITyDecl
          { iTyDeclName,
            iTyDeclParams,
            iTyDeclConstructors
          }
        )
    ) =
    let cases = generateCases iTyDeclConstructors
        hasTyTy c = map (\(IAnnParam (v, ty) _) -> (v, ty `notElem` dontDoTheseTypes && not (inConTy v (iConTy c)))) $ filter (\(IAnnParam (_, _) b) -> b) (iConArgs c)
        tms i c = ITmCon (iConName c) (map (\(v, b) -> if b then ITmVar (v ++ i) else ITmVar v) (hasTyTy c))
        implicits = map (\(IAnnParam (v, ty) _) -> IAnnParam (v, ty) False) iTyDeclParams
     in Impl
          { iImplicits = implicits,
            iConstraints = getConstraints iTyDeclParams,
            iSubject = ITmCon iTyDeclName (map (ITmVar . getIAnnParamVar) iTyDeclParams),
            iBody = concatMap (getCases . \(x, y) -> (tms "1" x, tms "2" y)) cases
          }
deriveDecEq
  ( IRec
      ( IRecDecl
          { iRecDeclName,
            iRecDeclParams,
            iRecDeclConstructor,
            iRecDeclFields
          }
        )
    ) =
    let asTyDecl =
          ITyDecl
            { iTyDeclName = iRecDeclName,
              iTyDeclParams = iRecDeclParams,
              iTyDeclConstructors =
                [ IConstructor
                    { iConName = iRecDeclConstructor,
                      iConArgs = iRecDeclFields,
                      iConTy = ITyCustom iRecDeclName (map (ITmVar . getIAnnParamVar) iRecDeclParams)
                    }
                ]
            }
     in deriveDecEq (ITy asTyDecl)

getConstraints :: List IAnnParam -> List ITm
getConstraints [] = []
getConstraints (IAnnParam (v, ITyTy) _ : xs) = ITmCon "DecEq" [ITmVar v] : getConstraints xs
getConstraints (IAnnParam (v, ITyFunc args) _ : xs) = getFuncConstraint v args [] [] : getConstraints xs
getConstraints (_ : xs) = getConstraints xs

getFuncConstraint :: String -> List (Maybe String, ITy) -> List (Maybe String, ITy) -> List String -> ITm
getFuncConstraint fv args acc facc = case unsnoc args of
  Just (xs, x@(Just v, _)) -> getFuncConstraint fv xs (x : acc) (v : facc)
  Just (xs, (Nothing, _)) -> getFuncConstraint fv xs acc facc
  Nothing -> ITmTy (ITyFunc (acc ++ [(Nothing, ITyTm $ ITmCon "DecEq" [ITmFuncCall (ITmVar fv) (map ITmVar facc)])]))

-- args to match on
getCases :: (ITm, ITm) -> List IImplCase
getCases (c1@(ITmCon v1 args1), c2@(ITmCon v2 args2)) = case v1 == v2 of
  True -> case length args1 == length args2 of
    True -> case null args1 of
      True -> [mkCase (c1, c2) [] Nothing (Tm $ ITmCon "Yes" [ITmVar "Refl"])]
      False ->
        let pairedargs = zip args1 args2
         in doEverything v1 [] ([], Nothing) pairedargs
    False -> error "dawg dis is Wrong"
  False -> [mkCase (c1, c2) [] Nothing (Tm noImpossible)]
getCases _ = error "pls no"

noImpossible :: ITm
noImpossible = ITmCon "No" [ITmLam "h" (ITmMatchImpossible [ITmVar "h"] [ITmCon "Refl" []])]

yesCon :: ITm
yesCon = ITmCon "Yes" [ITmVar "Refl"]

noCon :: String -> ITm
noCon prf = ITmCon "No" [ITmVar prf]

noConPrf :: String -> ITm
noConPrf prf = ITmCon "No" [ITmLam "h" (ITmFuncCall (ITmVar prf) [ITmMatch [ITmVar "h"] [([ITmCon "Refl" []], ITmCon "Refl" [])]])]

mkCons :: String -> List (ITm, ITm) -> (ITm, ITm)
mkCons c args = (ITmCon c (map fst args), ITmCon c (map snd args))

--              cname     prevargs            curBar with last prf   remaining
doEverything :: String -> List (ITm, ITm) -> (List ITm, Maybe String) -> List (ITm, ITm) -> IImplBody
doEverything cname prevargs (curbar, Nothing) [] = [mkCase (mkCons cname prevargs) curbar Nothing (Tm yesCon)]
doEverything cname prevargs (curbar, Just prf) _ = [mkCase (mkCons cname prevargs) curbar Nothing (Tm $ noConPrf prf)]
doEverything cname prevargs (curbar, Nothing) ((x1, x2) : xs) =
  if x1 == x2
    then doEverything cname (prevargs ++ [(x1, x2)]) (curbar, Nothing) xs
    else
      let yesCase = doEverything cname (prevargs ++ [(x1, x1)]) (curbar ++ [yesCon], Nothing) xs
          noCase = mkCase (mkCons cname (prevargs ++ [(x1, x2)] ++ xs)) (curbar ++ [noCon "prf"]) Nothing (Tm $ noConPrf "prf")
       in [mkCase (mkCons cname (prevargs ++ [(x1, x2)] ++ xs)) curbar (Just (ITmFuncCall (ITmVar "decEq") [x1, x2])) (Nest (yesCase ++ [noCase]))]

mkCase :: (ITm, ITm) -> List ITm -> Maybe ITm -> IImplCaseBody -> IImplCase
mkCase iArgs iBarArgs iWith iCaseBody =
  IImplCase
    { iArgs,
      iWith,
      iBarArgs,
      iCaseBody
    }

-- takes in a list of constructors, returns the constructor pairs for each case
generateCases :: List IConstructor -> List (IConstructor, IConstructor)
generateCases [] = []
generateCases [x] = [(x, x)]
generateCases (x : y : xs) =
  let xfst = (x, x) : map ((,) x) (filter (\x' -> iConTy x' == iConTy x) (y : xs))
      xfst' = if iConTy y == iConTy x then xfst ++ [(y, x)] else xfst
   in xfst' ++ (if null xs then [(y, y)] else generateCases (y : xs))
