module Spec where

-- main :: IO ()
-- main = putStrLn "Test suite not yet implemented"

import ITypes
import PTypes

store :: PTy
store = PTyCustom "Store" []

access :: PTy
access = PTyCustom "Access" []

-- init :: Func
-- init = Func {
--     funcName = mkStore,
--     funcRetTy =
-- }

storeFSM :: FSM
storeFSM =
  FSM
    { resourceTy = store,
      stateTy = access,
      initCons = [],
      actions = []
    }

-- store5 parse output

store5 = [
    PFSM (FSM {resourceTy = PTyCustom {tyName = "Store", tyParams = []}, stateTy = PTyCustom {tyName = "Access", tyParams = []}, initCons = [Func {funcName = "mkStore", funcRetTy = PTyCustom {tyName = "Store", tyParams = []}, funcArgs = [AnnParam (PTyCustom {tyName = "String", tyParams = []}, "secret") True, AnnParam (PTyCustom {tyName = "String", tyParams = []}, "pub") True], funcBody = StBlock [StReturn (PTmFuncCall (PTmVar "Store") [PTmVar "secret", PTmVar "pub"])], funcEff = Nothing, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) DInit)}], actions = [Action {actionName = "Login", actionRetTy = (PTyCustom {tyName = "LoginResult", tyParams = []}, Just "r"), actionStTrans = (PTmCon "LoggedOut" [], PTmTernary (PTmBEq (PTmVar "r") (PTmVar "OK")) (PTmVar "LoggedIn") (PTmVar "LoggedOut"))}, Action {actionName = "Logout", actionRetTy = (PTyUnit, Nothing), actionStTrans = (PTmCon "LoggedIn" [], PTmCon "LoggedOut" [])}, Action {actionName = "ReadSecret", actionRetTy = (PTyCustom {tyName = "String", tyParams = []}, Nothing), actionStTrans = (PTmCon "LoggedIn" [], PTmCon "LoggedIn" [])}]}), 

    PDecl (PTy (TyDecl {tyDeclName = "Access", tyDeclParams = [], tyDeclConstructors = [Constructor {conName = "LoggedIn", conArgs = [], conTy = PTyCustom {tyName = "Access", tyParams = []}}, Constructor {conName = "LoggedOut", conArgs = [], conTy = PTyCustom {tyName = "Access", tyParams = []}}]})), 
    
    PDecl (PTy (TyDecl {tyDeclName = "LoginResult", tyDeclParams = [], tyDeclConstructors = [Constructor {conName = "OK", conArgs = [], conTy = PTyCustom {tyName = "LoginResult", tyParams = []}}, Constructor {conName = "BadPassword", conArgs = [], conTy = PTyCustom {tyName = "LoginResult", tyParams = []}}]})), 
    
    PDecl (Rec (RecDecl {recDeclName = "Store", recDeclParams = [], recDeclFields = [(PTyCustom {tyName = "String", tyParams = []}, "secret"), (PTyCustom {tyName = "String", tyParams = []}, "pub")]})), 
    
    PFunc (Func {funcName = "login", funcRetTy = PTyCustom {tyName = "LoginResult", tyParams = []}, funcArgs = [], funcBody = StBlock [StIODot (PTmVar "print") [PTmString "enter password"], StDeclAssign (Just (PTyCustom {tyName = "String", tyParams = []})) "pw" (PTmFuncCall (PTmVar "getLine") []), StIf (PTmBEq (PTmVar "pw") (PTmString "password123")) (StBlock [StReturn (PTmCon "OK" [])]) (StBlock [StReturn (PTmCon "BadPassword" [])])], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DAction {directiveReturns = (PTyCustom {tyName = "LoginResult", tyParams = []}, Just "r"), directiveStTrans = (PTmCon "LoggedOut" [], PTmTernary (PTmBEq (PTmVar "r") (PTmVar "OK")) (PTmVar "LoggedIn") (PTmVar "LoggedOut"))}))}), 
    
    PFunc (Func {funcName = "logout", funcRetTy = PTyUnit, funcArgs = [], funcBody = StBlock [StIODot (PTmVar "print") [PTmString "logging out"]], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DAction {directiveReturns = (PTyUnit, Nothing), directiveStTrans = (PTmCon "LoggedIn" [], PTmCon "LoggedOut" [])}))}), 
    
    PFunc (Func {funcName = "readSecret", funcRetTy = PTyCustom {tyName = "String", tyParams = []}, funcArgs = [], funcBody = StBlock [StReturn (PTmDotRec (PTmVar "this") (PTmVar "secret"))], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DAction {directiveReturns = (PTyCustom {tyName = "String", tyParams = []}, Nothing), directiveStTrans = (PTmCon "LoggedIn" [], PTmCon "LoggedIn" [])}))}), 
    
    PFunc (Func {funcName = "mkStore", funcRetTy = PTyCustom {tyName = "Store", tyParams = []}, funcArgs = [AnnParam (PTyCustom {tyName = "String", tyParams = []}, "secret") True, AnnParam (PTyCustom {tyName = "String", tyParams = []}, "pub") True], funcBody = StBlock [StReturn (PTmFuncCall (PTmVar "Store") [PTmVar "secret", PTmVar "pub"])], funcEff = Nothing, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) DInit)}), 
    
    PFunc (Func {funcName = "main", funcRetTy = PTyUnit, funcArgs = [], funcBody = StBlock [StDeclAssign (Just (PTyCustom {tyName = "LoginResult", tyParams = []})) "res" (PTmDot (PTmVar "this") (PTmVar "login") []), StEIf (PTmBEq (PTmVar "res") (PTmVar "OK")) (StBlock [StDeclAssign (Just (PTyCustom {tyName = "String", tyParams = []})) "secret" (PTmDot (PTmVar "this") (PTmVar "readSecret") []), StIODot (PTmVar "print") [PTmVar "secret"], StDot (PTmVar "this") (PTmVar "logout") []]) (StBlock [StIODot (PTmVar "print") [PTmString "bad password"]])], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DRun {directiveReturns = (PTyUnit, Nothing), directiveWith = ("this", PTmFuncCall (PTmVar "mkStore") [PTmString "secret", PTmString "pub"]), directiveStTrans = (PTmCon "LoggedOut" [], PTmCon "LoggedOut" [])}))})]