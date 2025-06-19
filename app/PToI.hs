{-# LANGUAGE NamedFieldPuns #-}

module PToI where

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
trTm (PTmFunc f) = ITmFunc $ unLoopFunc f
trTm (PTmFuncCall f args) = ITmFuncCall (trTm f) (map trTm args)
trTm (PTmBlock xs t) = trStmt xs (trTm t)
trTm (PTmIf c t e) = ITmIf (trTm c) (trTm t) (trTm e)
trTm (PTmReturn t) = trTm t -- todo
trTm (PTmSwitch s) = trSwitch s
trTm (PTmMinus t1 t2) = ITmMinus (trTm t1) (trTm t2)
trTm (PTmBEq t1 t2) = ITmBEq (trTm t1) (trTm t2)
trTm (PTmBLT t1 t2) = ITmBLT (trTm t1) (trTm t2)

trStmt :: List Stmt -> ITm -> ITm
trStmt [] tm = tm
trStmt (DeclAssign ty v tm : xs) tm2 = ITmLet v (trTy ty) (trTm tm) (trStmt xs tm2)
trStmt _ _ = error "should be transformed"

trTy :: PTy -> ITy
trTy PTyNat = ITyNat
trTy PTyBool = ITyBool
trTy PTyUnit = ITyUnit
trTy PTyTy = ITyTy
trTy PTyFunc {tyFuncArgs, tyFuncRetTy} = ITyFunc $ map (\(x, y) -> (Just y, trTy x)) tyFuncArgs ++ [(Nothing, trTy tyFuncRetTy)]
trTy PTyCustom {tyName, tyParams} = ITyCustom tyName (map trTm tyParams)
trTy (PTyPTm t) = ITyTm (trTm t)

trSwitch :: Switch -> ITm
trSwitch Switch {switchOn, cases} =
  let branches = map (\(Case {caseOn, caseBody}) -> (map trTm caseOn, trTm caseBody)) cases
   in ITmMatch
        (map trTm switchOn)
        branches

trProg :: Prog -> IProg
trProg = map trProgEl

trProgEl :: ProgEl -> IProgEl
trProgEl (PDecl decl) = IIDecl $ trDecl decl
trProgEl (PFunc func) = IIFunc $ trFunc (doShadowing func)

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
  Func
    { funcName,
      funcRetTy,
      funcArgs,
      funcBody
    } =
    IFunc
      { iFuncName = funcName,
        iFuncRetTy = trTy funcRetTy,
        iFuncArgs = map trAnnParam funcArgs,
        iFuncBody = trTm funcBody,
        iWhere = []
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

doShadowing :: Func -> Func
doShadowing f =
  let tm = funcBody f
   in f {funcBody = doPTms (M.fromList (map (\(AnnParam (t, v) _) -> (v, t)) (funcArgs f))) tm}

doPTms :: M.Map String PTy -> PTm -> PTm
doPTms m (PTmBlock stmts tm) = PTmBlock (doStmts m stmts) tm
doPTms m (PTmPlus t1 t2) = PTmPlus (doPTms m t1) (doPTms m t2)
doPTms m (PTmCon v tms) = PTmCon v (map (doPTms m) tms)
doPTms m (PTmFunc f) = PTmFunc f {funcBody = doPTms m (funcBody f)}
doPTms m (PTmFuncCall t ts) = PTmFuncCall (doPTms m t) (map (doPTms m) ts)
doPTms m (PTmIf t1 t2 t3) = PTmIf (doPTms m t1) (doPTms m t2) (doPTms m t3)
doPTms m (PTmReturn t) = PTmReturn (doPTms m t)
doPTms m (PTmSwitch s) =
  PTmSwitch
    s
      { switchOn = map (doPTms m) (switchOn s),
        cases = map (\c -> Case {caseOn = map (doPTms m) (caseOn c), caseBody = doPTms m (caseBody c)}) (cases s)
      }
doPTms _ tm = tm

doStmts :: M.Map String PTy -> List Stmt -> List Stmt
doStmts _ [] = []
doStmts vars (x : xs) = case x of
  Assign var tm -> case M.lookup var vars of
    Nothing -> error "assign before declare"
    Just ty -> DeclAssign ty var tm : doStmts vars xs
  DeclAssign ty var tm -> DeclAssign ty var tm : doStmts (M.insert var ty vars) xs
  While {condition, body} -> While {condition, body = doStmts vars body} : doStmts vars xs

-- only works for one loop stmt currently
getLoopStmt :: List Stmt -> List Stmt -> List Stmt -> Maybe (List Stmt, PTm, List Stmt, List Stmt)
getLoopStmt [] _ _ = Nothing
getLoopStmt (x : xs) hdr tl = case x of
  While {condition, body} -> Just (hdr, condition, body, xs ++ tl)
  _ -> getLoopStmt xs (hdr ++ [x]) []

unLoopFunc :: Func -> IFunc
unLoopFunc
  f@( Func
        { funcName,
          funcRetTy,
          funcArgs,
          funcBody
        }
      ) = case funcBody of
    PTmBlock stmts tm -> case getLoopStmt stmts [] [] of
      Nothing -> trFunc f
      Just (hdr, condition, body, tl) ->
        let (outer, innerName) = defOuter hdr tl funcName funcArgs funcRetTy tm
            inner = defInner condition tm body innerName funcArgs funcRetTy 
            in 
              (unLoopFunc outer) {iWhere = [ITmFunc (unLoopFunc inner)]}
    _ -> trFunc f 

-- the inner function needs to return all updated variables so any updates can be reflected in the outer function 
-- or all the tail statements need to be part of the inner function 
defOuter :: List Stmt -> List Stmt -> String -> List AnnParam -> PTy -> PTm -> (Func, String)
defOuter hdr tl funcName funcArgs funcRetTy retTm =
  let funcInner = funcName ++ "_rec"
      recLet = DeclAssign funcRetTy (funcName ++ "_recVal") (PTmFuncCall (PTmVar funcInner) (map (PTmVar . getAnnParamVar) funcArgs))
  in 
    (Func
        { funcName,
          funcArgs,
          funcRetTy,
          funcBody = PTmBlock (hdr ++ [recLet] ++ tl ) retTm
        }, funcInner)

defInner :: PTm -> PTm -> List Stmt -> String -> List AnnParam -> PTy -> Func
defInner condition tl body fname params retty = Func
        { funcName = fname,
          funcArgs = params,
          funcRetTy = retty,
          funcBody = PTmIf (PTmNot condition) tl (PTmBlock body (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) params)))
        }

getAnnParamVar :: AnnParam -> String
getAnnParamVar (AnnParam (_, str) _) = str

getAnnParamPTy :: AnnParam -> PTy
getAnnParamPTy (AnnParam (ty, _) _) = ty
