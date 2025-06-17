{-# LANGUAGE NamedFieldPuns #-}

module PToI where

import ITypes
import PTypes
import qualified Data.Map as M


trTm :: PTm -> ITm
trTm (PTmNat n) = ITmNat n
trTm (PTmPlus t1 t2) = ITmPlus (trTm t1) (trTm t2)
trTm (PTmBool b) = ITmBool b
trTm PTmUnit = ITmUnit
trTm (PTmNot t) = ITmNot (trTm t)
trTm (PTmPTy t) = ITmTy (trTy t)
trTm (PTmVar x) = ITmVar x
trTm (PTmCon x cs) = ITmCon x (map trTm cs)
trTm (PTmFunc f) = ITmFunc (trFunc f)
trTm (PTmFuncCall f args) = ITmFuncCall (trTm f) (map trTm args)
trTm (PTmBlock ls t) = error "should have been transformed"
trTm (PTmIf c t e) = ITmIf (trTm c) (trTm t) (trTm e)
trTm (PTmReturn t) = trTm t -- todo
trTm (PTmSwitch s) = trSwitch s

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
    let branches = map (\(Case {caseOn, caseBody}) -> (map trTm caseOn, trTm caseBody)) cases in  
  ITmMatch
    (map trTm switchOn) branches 

trProg :: Prog -> IProg 
trProg = map trProgEl 

trProgEl :: ProgEl -> IProgEl 
trProgEl (PDecl decl) = IIDecl $ trDecl decl
trProgEl (PFunc func) = IIFunc $ trFunc (doShadowing func)

trDecl :: Decl -> IDecl 
trDecl (PTy tydecl) = ITy $ trTyDecl tydecl 
trDecl (Rec recdecl) = IRec $ trRecDecl recdecl

trTyDecl :: TyDecl -> ITyDecl 
trTyDecl TyDecl {
  tyDeclName, tyDeclParams, tyDeclConstructors
} = ITyDecl {
  iTyDeclName = tyDeclName, 
  iTyDeclParams = map trAnnParam tyDeclParams, 
  iTyDeclConstructors = map trConstructor tyDeclConstructors
}

trRecDecl :: RecDecl -> IRecDecl 
trRecDecl RecDecl {
  recDeclName, recDeclParams, recDeclFields
} = IRecDecl {
  iRecDeclName = recDeclName, 
  iRecDeclParams = map trAnnParam recDeclParams, 
  iRecDeclConstructor = "mk" ++ recDeclName, 
  iRecDeclFields = map (trAnnParam . (`AnnParam` True)) recDeclFields
} 

trFunc :: Func -> IFunc 
trFunc Func {
  funcName, funcRetTy, funcArgs, funcBody
} = IFunc {
  iFuncName = funcName, 
  iFuncRetTy = trTy funcRetTy, 
  iFuncArgs = map trAnnParam funcArgs, 
  iFuncBody = trTm funcBody, 
  iWhere = []
} 

trConstructor :: Constructor -> IConstructor 
trConstructor Constructor {
  conName, conArgs, conTy
} = IConstructor {
  iConName = conName, 
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
  _ -> x : doStmts vars xs

unLoop :: Func -> IFunc 
unLoop f = undefined 

defOuter :: List Stmt -> String -> List AnnParam -> PTy -> IFunc
defOuter hdr fname params ty =
  let funcName = fname ++ "_reco"
      funcInner = fname ++ "_reci"
      iFunc = trFunc 
   in undefined 


defInner :: PTm -> PTm -> List Stmt -> String -> List AnnParam -> List (PTy, String) -> PTy -> Func
defInner condition tl body fname params vars retty =
  let funcName = fname ++ "_reci"
      hvars = map (`AnnParam` True) vars
   in Func
        { funcName = funcName,
          funcArgs = params ++ hvars,
          funcRetTy = retty,
          funcBody = PTmIf (PTmNot condition) (PTmReturn tl) (PTmBlock body (PTmFuncCall (PTmVar funcName) (map (PTmVar . getAnnParamVar) (params ++ hvars))))
        }

getAnnParamVar :: AnnParam -> String
getAnnParamVar (AnnParam (_, str) _) = str

getAnnParamPTy :: AnnParam -> PTy
getAnnParamPTy (AnnParam (ty, _) _) = ty
