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


store5' = [
    PFSM (FSM {resourceTy = PTyCustom {tyName = "Store", tyParams = []}, stateTy = PTyCustom {tyName = "Access", tyParams = []}, initCons = [Func {funcName = "mkStore", funcRetTy = PTyCustom {tyName = "Store", tyParams = []}, funcArgs = [AnnParam (PTyCustom {tyName = "String", tyParams = []},"secret") True,AnnParam (PTyCustom {tyName = "String", tyParams = []},"pub") True], funcBody = StBlock [StReturn (PTmFuncCall (PTmVar "Store") [PTmVar "secret",PTmVar "pub"])], funcEff = Nothing, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) DInit)}], actions = [Action {actionName = "Login", actionRetTy = (PTyCustom {tyName = "LoginResult", tyParams = []},Just "r"), actionStTrans = (PTmCon "LoggedOut" [],PTmTernary (PTmBEq (PTmVar "r") (PTmVar "OK")) (PTmVar "LoggedIn") (PTmVar "LoggedOut"))},Action {actionName = "Logout", actionRetTy = (PTyUnit,Nothing), actionStTrans = (PTmCon "LoggedIn" [],PTmCon "LoggedOut" [])},Action {actionName = "ReadSecret", actionRetTy = (PTyCustom {tyName = "String", tyParams = []},Nothing), actionStTrans = (PTmCon "LoggedIn" [],PTmCon "LoggedIn" [])}]}),
    
    PDecl (PTy (TyDecl {tyDeclName = "Access", tyDeclParams = [], tyDeclConstructors = [Constructor {conName = "LoggedIn", conArgs = [], conTy = PTyCustom {tyName = "Access", tyParams = []}},Constructor {conName = "LoggedOut", conArgs = [], conTy = PTyCustom {tyName = "Access", tyParams = []}}]})),
    
    PDecl (PTy (TyDecl {tyDeclName = "LoginResult", tyDeclParams = [], tyDeclConstructors = [Constructor {conName = "OK", conArgs = [], conTy = PTyCustom {tyName = "LoginResult", tyParams = []}},Constructor {conName = "BadPassword", conArgs = [], conTy = PTyCustom {tyName = "LoginResult", tyParams = []}}]})),
    
    PDecl (Rec (RecDecl {recDeclName = "Store", recDeclParams = [], recDeclFields = [(PTyCustom {tyName = "String", tyParams = []},"secret"),(PTyCustom {tyName = "String", tyParams = []},"pub")]})),
    
    PFunc (Func {funcName = "login", funcRetTy = PTyCustom {tyName = "LoginResult", tyParams = []}, funcArgs = [], funcBody = StBlock [StIODot (PTmVar "print") [PTmString "enter password"],StDeclAssign (Just (PTyCustom {tyName = "String", tyParams = []})) "pw" (PTmDot PTmIO (PTmVar "getLine") []),StIf (PTmBEq (PTmVar "pw") (PTmString "password123")) (StBlock [StReturn (PTmCon "OK" [])]) (StBlock [StReturn (PTmCon "BadPassword" [])])], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DAction {directiveReturns = (PTyCustom {tyName = "LoginResult", tyParams = []},Just "r"), directiveStTrans = (PTmCon "LoggedOut" [],PTmTernary (PTmBEq (PTmVar "r") (PTmVar "OK")) (PTmVar "LoggedIn") (PTmVar "LoggedOut"))}))}),
    
    PFunc (Func {funcName = "logout", funcRetTy = PTyUnit, funcArgs = [], funcBody = StBlock [StIODot (PTmVar "print") [PTmString "logging out"]], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DAction {directiveReturns = (PTyUnit,Nothing), directiveStTrans = (PTmCon "LoggedIn" [],PTmCon "LoggedOut" [])}))}),
    
    PFunc (Func {funcName = "readSecret", funcRetTy = PTyCustom {tyName = "String", tyParams = []}, funcArgs = [], funcBody = StBlock [StReturn (PTmDotRec (PTmVar "this") (PTmVar "secret"))], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DAction {directiveReturns = (PTyCustom {tyName = "String", tyParams = []},Nothing), directiveStTrans = (PTmCon "LoggedIn" [],PTmCon "LoggedIn" [])}))}),
    
    PFunc (Func {funcName = "mkStore", funcRetTy = PTyCustom {tyName = "Store", tyParams = []}, funcArgs = [AnnParam (PTyCustom {tyName = "String", tyParams = []},"secret") True,AnnParam (PTyCustom {tyName = "String", tyParams = []},"pub") True], funcBody = StBlock [StReturn (PTmFuncCall (PTmVar "Store") [PTmVar "secret",PTmVar "pub"])], funcEff = Nothing, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) DInit)}),
    
    PFunc (Func {funcName = "main", funcRetTy = PTyUnit, funcArgs = [], funcBody = StBlock [StDeclAssign (Just (PTyCustom {tyName = "LoginResult", tyParams = []})) "res" (PTmDot PTmThis (PTmVar "login") []),StEIf (PTmBEq (PTmVar "res") (PTmVar "OK")) (StBlock [StDeclAssign (Just (PTyCustom {tyName = "String", tyParams = []})) "secret" (PTmDot PTmThis (PTmVar "readSecret") []),StIODot (PTmVar "print") [PTmVar "secret"],StDot (PTmVar "this") (PTmVar "logout") []]) (StBlock [StIODot (PTmVar "print") [PTmString "bad password"]])], funcEff = Just IO, funcDirective = Just (Directive (DFSM (PTyCustom {tyName = "Store", tyParams = []}) (PTyCustom {tyName = "Access", tyParams = []})) (DRun {directiveReturns = (PTyUnit,Nothing), directiveWith = ("this",PTmFuncCall (PTmVar "mkStore") [PTmString "secret",PTmString "pub"]), directiveStTrans = (PTmCon "LoggedOut" [],PTmCon "LoggedOut" [])}))})]

istore5 = [
    IIFSM (IFSM {
        idxm = ITyDecl {
            iTyDeclName = "IdxmStore_Access", 
            iTyDeclParams = [IAnnParam ("ty",ITyTy) True,IAnnParam ("",ITyApp (ITyVar "Access") []) True,IAnnParam ("",ITyFunc [(Nothing,ITyTm (ITmVar "ty")),(Nothing,ITyApp (ITyVar "Access") [])]) True], 
            iTyDeclConstructors = [
                IConstructor {iConName = "Login", iConArgs = [], iConTy = ITyApp (ITyVar "IdxmStore_Access") [ITmTy (ITyApp (ITyVar "LoginResult") []),ITmCon "LoggedOut" [],ITmLam [ITmVar "r"] (ITmMatch [ITmFuncCall (ITmVar "decEq") [ITmVar "r",ITmVar "OK"]] [([ITmCon "Yes" [ITmVar "yesprf"]],ITmVar "LoggedIn"),([ITmCon "No" [ITmVar "noprf"]],ITmVar "LoggedOut")])]},
                
                IConstructor {iConName = "Logout", iConArgs = [], iConTy = ITyApp (ITyVar "IdxmStore_Access") [ITmTy ITyUnit,ITmCon "LoggedIn" [],ITmFuncCall (ITmVar "const") [ITmCon "LoggedOut" []]]},
                
                IConstructor {iConName = "ReadSecret", iConArgs = [], iConTy = ITyApp (ITyVar "IdxmStore_Access") [ITmTy (ITyApp (ITyVar "String") []),ITmCon "LoggedIn" [],ITmFuncCall (ITmVar "const") [ITmCon "LoggedIn" []]]},
                
                IConstructor {iConName = "PureStore_Access", iConArgs = [IAnnParam ("x",ITyTm (ITmVar "ty")) True], iConTy = ITyApp (ITyVar "Store") [ITmVar "ty",ITmFuncCall (ITmVar "st") [ITmVar "x"],ITmVar "st"]},
                
                IConstructor {iConName = "(>>=)", iConArgs = [IAnnParam ("",ITyApp (ITyVar "Store") [ITmVar "a",ITmVar "st1",ITmVar "st2"]) True,IAnnParam ("",ITyFunc [(Just "x",ITyTm (ITmVar "a")),(Nothing,ITyApp (ITyVar "Store") [ITmVar "b",ITmFuncCall (ITmVar "st2") [ITmVar "x"]])]) True], iConTy = ITyApp (ITyVar "Store") [ITmVar "b",ITmVar "st1",ITmVar "st3"]},
                
                IConstructor {iConName = "LiftStore_Access", iConArgs = [IAnnParam ("",ITyIO (ITyTm (ITmVar "ty"))) True], iConTy = ITyApp (ITyVar "Store") [ITmVar "ty",ITmVar "st",ITmFuncCall (ITmVar "const") [ITmVar "st"]]}]}, 
        
        conc = ITyApp (ITyVar "Store") [], 
        
        run = IFunc {iFuncName = "runStore_Access", iFuncArgs = [IAnnParam ("",ITyApp (ITyVar "Store") []) True,IAnnParam ("",ITyApp (ITyVar "IdxmStore_Access") [ITmVar "ty",ITmVar "",ITmVar ""]) True], iFuncBody = [(ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmFuncCall (ITmVar "PureIdxmStore_Access") [ITmVar "x"]],ITmFuncCall (ITmVar "pure") [ITmVar "x"]),(ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmBind (ITmVar "action") (ITmVar "cont")],ITmDo [ITmDoBind [ITmVar "res"] (ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmVar "action"]),ITmDoIO (ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmFuncCall (ITmVar "cont") [ITmVar "res"]])]),(ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmFuncCall (ITmVar "LiftIdxmStore_Access") [ITmVar "io"]],ITmVar "io"),(ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmCon "Login" []],ITmFuncCall (ITmVar "login") [ITmVar "resource"]),(ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmCon "Logout" []],ITmFuncCall (ITmVar "logout") [ITmVar "resource"]),(ITmFuncCall (ITmVar "runStore_Access") [ITmVar "resource",ITmCon "ReadSecret" []],ITmFuncCall (ITmVar "readSecret") [ITmVar "resource"])], iFuncRetTy = ITyIO (ITyPair (ITyTm (ITmVar "ty")) (ITyApp (ITyVar "Store") [])), iWhere = []}}),
    
    IIDecl (ITy (ITyDecl {iTyDeclName = "Access", iTyDeclParams = [], iTyDeclConstructors = [IConstructor {iConName = "LoggedIn", iConArgs = [], iConTy = ITyApp (ITyVar "Access") []},IConstructor {iConName = "LoggedOut", iConArgs = [], iConTy = ITyApp (ITyVar "Access") []}]})),
    
    IIDecl (ITy (ITyDecl {iTyDeclName = "LoginResult", iTyDeclParams = [], iTyDeclConstructors = [IConstructor {iConName = "OK", iConArgs = [], iConTy = ITyApp (ITyVar "LoginResult") []},IConstructor {iConName = "BadPassword", iConArgs = [], iConTy = ITyApp (ITyVar "LoginResult") []}]})),
    
    IIDecl (IRec (IRecDecl {iRecDeclName = "Store", iRecDeclParams = [], iRecDeclConstructor = "MkStore", iRecDeclFields = [IAnnParam ("secret",ITyApp (ITyVar "String") []) True,IAnnParam ("pub",ITyApp (ITyVar "String") []) True]})),
    
    IIFunc (IFunc {iFuncName = "login", iFuncArgs = [IAnnParam ("this",ITyApp (ITyVar "Store") []) True], iFuncBody = [(ITmFuncCall (ITmVar "login") [ITmVar "this"],ITmDo [ITmDoBind [ITmWildCard] (ITmFuncCall (ITmVar "print") [ITmString "enter password"]),ITmDoBind [ITmVar "pw"] (ITmFuncCall (ITmVar "LiftStore_Access") [ITmFuncCall (ITmVar "getLine") []]),ITmDoIf (ITmBEq (ITmVar "pw") (ITmString "password123")) (ITmDo [ITmDoPure (ITmCon "OK" [])]) (ITmDo [ITmDoPure (ITmCon "BadPassword" [])])])], iFuncRetTy = ITyIO (ITyPair (ITyApp (ITyVar "LoginResult") []) (ITyApp (ITyVar "Store") [])), iWhere = []}),
    
    IIFunc (IFunc {iFuncName = "logout", iFuncArgs = [IAnnParam ("this",ITyApp (ITyVar "Store") []) True], iFuncBody = [(ITmFuncCall (ITmVar "logout") [ITmVar "this"],ITmDo [ITmDoBind [ITmWildCard] (ITmFuncCall (ITmVar "print") [ITmString "logging out"])])], iFuncRetTy = ITyIO (ITyPair ITyUnit (ITyApp (ITyVar "Store") [])), iWhere = []}),
    
    IIFunc (IFunc {iFuncName = "readSecret", iFuncArgs = [IAnnParam ("this",ITyApp (ITyVar "Store") []) True], iFuncBody = [(ITmFuncCall (ITmVar "readSecret") [ITmVar "this"],ITmDo [ITmDoPure (ITmDot (ITmVar "this") (ITmVar "secret"))])], iFuncRetTy = ITyIO (ITyPair (ITyApp (ITyVar "String") []) (ITyApp (ITyVar "Store") [])), iWhere = []}),
    
    IIFunc (IFunc {iFuncName = "mkStore", iFuncArgs = [IAnnParam ("secret",ITyApp (ITyVar "String") []) True,IAnnParam ("pub",ITyApp (ITyVar "String") []) True], iFuncBody = [(ITmFuncCall (ITmVar "mkStore") [ITmVar "secret",ITmVar "pub"],ITmFuncCall (ITmVar "Store") [ITmVar "secret",ITmVar "pub"])], iFuncRetTy = ITyApp (ITyVar "Store") [], iWhere = []}),
    
    IIFunc (IFunc {iFuncName = "main", iFuncArgs = [], iFuncBody = [(ITmFuncCall (ITmVar "main") [],ITmDo [ITmDoLet "this" Nothing (ITmFuncCall (ITmVar "mkStore") [ITmString "secret",ITmString "pub"]),ITmDoBind [ITmVar "resVal",ITmVar "resConc"] (ITmFuncCall (ITmVar "runStore_Access") [ITmVar "this",ITmVar "main'"]),ITmDoPure (ITmVar "resVal")])], iFuncRetTy = ITyIO ITyUnit, iWhere = [ITmFunc (IFunc {iFuncName = "main'", iFuncArgs = [], iFuncBody = [(ITmFuncCall (ITmVar "main'") [],ITmDo [ITmDoBind [ITmVar "res",ITmVar "this"] (ITmFuncCall (ITmVar "login") [ITmVar "this"]),ITmDoCase [ITmBEq (ITmVar "res") (ITmVar "OK")] [([ITmCon "Yes" [ITmVar "yesprf"]],ITmDo [ITmDoBind [ITmVar "secret",ITmVar "this"] (ITmFuncCall (ITmVar "readSecret") [ITmVar "this"]),ITmDoBind [ITmWildCard] (ITmFuncCall (ITmVar "print") [ITmVar "secret"]),ITmDoBind [ITmWildCard,ITmVar "this"] (ITmFuncCall (ITmVar "logout") [ITmVar "this"])]),([ITmCon "No" [ITmVar "noprf"]],ITmDo [ITmDoBind [ITmWildCard] (ITmFuncCall (ITmVar "print") [ITmString "bad password"])])]])], iFuncRetTy = ITyApp (ITyVar "IdxmStore_Access") [ITmTy ITyUnit,ITmCon "LoggedOut" [],ITmFuncCall (ITmVar "const") [ITmCon "LoggedOut" []]], iWhere = []})]})]
