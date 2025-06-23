{-# LANGUAGE NamedFieldPuns #-}

module PToI where

import Data.List (nub)
import qualified Data.Map as M
import Data.Maybe (fromJust, isJust, fromMaybe)
import Data.Tuple (swap)
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
trTm (PTmReturn t) = trTm t
trTm (PTmSwitch s) = trSwitch s
trTm (PTmMinus t1 t2) = ITmMinus (trTm t1) (trTm t2)
trTm (PTmBEq t1 t2) = ITmBEq (trTm t1) (trTm t2)
trTm (PTmBLT t1 t2) = ITmBLT (trTm t1) (trTm t2)

trStmt :: List Stmt -> ITm -> ITm
trStmt [] tm = tm
trStmt (DeclAssign (Just ty) v tm : xs) tm2 = ITmLet v (Just (trTy ty)) (trTm tm) (trStmt xs tm2)
trStmt (DeclAssign Nothing v tm : xs) tm2 = ITmLet v Nothing (trTm tm) (trStmt xs tm2)
trStmt stmts _ = error $ "should be transformed, " ++ show stmts

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

-- for now, you cannot reassign to the same variable if it changes types. 
doShadowing :: Func -> Func
doShadowing f =
  let tm = funcBody f
   in f {funcBody = doPTms (M.fromList (map (\(AnnParam (t, v) _) -> (v, t)) (funcArgs f))) tm}

doPTms :: M.Map String PTy -> PTm -> PTm
doPTms m (PTmBlock stmts tm) = PTmBlock (doStmts stmts) (doPTms m tm)
doPTms m (PTmPlus t1 t2) = PTmPlus (doPTms m t1) (doPTms m t2)
doPTms m (PTmMinus t1 t2) = PTmMinus (doPTms m t1) (doPTms m t2)
doPTms m (PTmBEq t1 t2) = PTmBEq (doPTms m t1) (doPTms m t2)
doPTms m (PTmBLT t1 t2) = PTmBLT (doPTms m t1) (doPTms m t2)
doPTms m (PTmNot t1) = PTmNot (doPTms m t1)
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

doStmts :: List Stmt -> List Stmt
doStmts [] = []
doStmts (x : xs) = case x of
  Assign var tm -> DeclAssign Nothing var tm : doStmts xs
  DeclAssign ty var tm -> DeclAssign ty var tm : doStmts xs
  While {condition, body} -> While {condition, body = doStmts body} : doStmts xs

-- only works for one loop stmt currently
getLoopStmt :: List Stmt -> List Stmt -> List Stmt -> Maybe (List Stmt, PTm, List Stmt, List Stmt)
getLoopStmt [] _ _ = Nothing
getLoopStmt (x : xs) hdr tl = case x of
  While {condition, body} -> Just (hdr, condition, body, xs ++ tl)
  _ -> getLoopStmt xs (hdr ++ [x]) []

unLoopFuncPFunc :: Func -> (Func, [Func]) 
unLoopFuncPFunc f@( Func
        { funcName,
          funcRetTy,
          funcArgs,
          funcBody
        }
      ) =
    let (body, inner) = unLoopTm funcName funcArgs funcRetTy funcBody []
      in (f {funcBody = body}, inner)

unLoopFunc :: Func -> IFunc
unLoopFunc f = let (fNew, inner) = unLoopFuncPFunc f in 
  (trFunc fNew) {iWhere = map (ITmFunc . trFunc) inner}

unLoopTm :: String -> List AnnParam -> PTy -> PTm -> List Func -> (PTm, List Func)
unLoopTm fname fparams fretty tm innerFuncs = case tm of
  PTmBlock stmts tm -> case getLoopStmt stmts [] [] of
    Nothing ->
      let (newTm, newInner) = unLoopTm fname (fparams ++  map (\(x,y) -> AnnParam (fromMaybe PTyHole y, x) True) (getHVars stmts M.empty)) fretty tm innerFuncs
       in (PTmBlock stmts newTm, innerFuncs ++ newInner)
    Just (hdr, condition, body, tl) ->
      let (outer, innerName) = defOuter hdr fname fparams (length innerFuncs)
          inner = defInner condition tm body innerName fparams fretty tl hdr
       in (outer, uncurry (:) (unLoopFuncPFunc inner) ++ innerFuncs)
  PTmPlus tm1_ tm2_ ->
    let (tm1, tm1_inner) = unLoopTm fname fparams fretty tm1_ innerFuncs
        (tm2, tm2_inner) = unLoopTm fname fparams fretty tm2_ innerFuncs
     in (PTmPlus tm1 tm2, nub (innerFuncs ++ tm1_inner ++ tm2_inner))
  PTmMinus tm1_ tm2_ ->
    let (tm1, tm1_inner) = unLoopTm fname fparams fretty tm1_ innerFuncs
        (tm2, tm2_inner) = unLoopTm fname fparams fretty tm2_ innerFuncs
     in (PTmMinus tm1 tm2, nub (innerFuncs ++ tm1_inner ++ tm2_inner))
  PTmBEq tm1_ tm2_ ->
    let (tm1, tm1_inner) = unLoopTm fname fparams fretty tm1_ innerFuncs
        (tm2, tm2_inner) = unLoopTm fname fparams fretty tm2_ innerFuncs
     in (PTmBEq tm1 tm2, nub (innerFuncs ++ tm1_inner ++ tm2_inner))
  PTmBLT tm1_ tm2_ ->
    let (tm1, tm1_inner) = unLoopTm fname fparams fretty tm1_ innerFuncs
        (tm2, tm2_inner) = unLoopTm fname fparams fretty tm2_ innerFuncs
     in (PTmBLT tm1 tm2, nub (innerFuncs ++ tm1_inner ++ tm2_inner))
  PTmNot tm1_ ->
    let (tm1, tm1_inner) = unLoopTm fname fparams fretty tm1_ innerFuncs
     in (PTmNot tm1, nub (innerFuncs ++ tm1_inner))
  PTmIf tm1_ tm2_ tm3_ ->
    let (tm1, tm1_inner) = unLoopTm fname fparams fretty tm1_ innerFuncs
        (tm2, tm2_inner) = unLoopTm fname fparams fretty tm2_ innerFuncs
        (tm3, tm3_inner) = unLoopTm fname fparams fretty tm3_ innerFuncs
     in (PTmIf tm1 tm2 tm3, nub (innerFuncs ++ tm1_inner ++ tm2_inner ++ tm3_inner))
  _ -> (tm, innerFuncs)

getHVars :: List Stmt -> M.Map String (Maybe PTy) -> List (String, Maybe PTy)
getHVars [] m = M.toList m
getHVars (x : xs) m = case x of
  DeclAssign ty v _ -> getHVars xs (M.insert v ty m)
  Assign _ _ -> error "assignment should have been transformed"
  While {condition, body} -> getHVars xs m -- TODO

defOuter :: List Stmt -> String -> List AnnParam -> Int -> (PTm, String)
defOuter hdr funcName funcArgs i =
  let funcInner = funcName ++ "_rec" ++ show i 
      vars = getHVars hdr M.empty
   in ( PTmBlock hdr (PTmReturn (PTmFuncCall (PTmVar funcInner) (map (PTmVar . getAnnParamVar) funcArgs ++ map (PTmVar . fst) vars))),
        funcInner
      )

defInner :: PTm -> PTm -> List Stmt -> String -> List AnnParam -> PTy -> List Stmt -> List Stmt -> Func
defInner condition ret body fname params retty tl hdr =
  let ps = params ++ map (\(v, ty) -> AnnParam (fromMaybe PTyHole ty, v) True) (getHVars hdr M.empty)
   in Func
        { funcName = fname,
          funcArgs = ps,
          funcRetTy = retty,
          funcBody = PTmIf (PTmNot condition) (PTmBlock tl ret) (PTmBlock body (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) ps)))
        }

getAnnParamVar :: AnnParam -> String
getAnnParamVar (AnnParam (_, str) _) = str

getAnnParamPTy :: AnnParam -> PTy
getAnnParamPTy (AnnParam (ty, _) _) = ty
