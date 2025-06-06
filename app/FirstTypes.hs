module FirstTypes where

    type List a = [a]
    data Ty = TyNat 
        | TyTy 
        | TyVoid
        | TyVar String
        | TyFunctionCall String (List Tm)
        | TyCustom {
            tyName :: String, 
            tyErasedParams :: List Tm, 
            tyParams :: List Tm
        } 
        | TyFunc {
            tyFuncArgs :: List (Ty, String),
            tyFuncRetTy :: Ty 
        }
        deriving (Show, Eq)

    data Tm = TmNat Int
            | TmPlus Tm Tm 
            | TmVar String
            | TmTyVar String
            | TmFunctionCall String (List Tm)
            | TmCon String (List Tm)
            deriving (Show, Eq)

    data Prog = Prog {
        types :: List Decl, 
        funcs :: List Func
    }
        deriving (Show, Eq)

    data Func = Func {
        funcName :: String, 
        funcRetType :: Ty, 
        funcErasedArgs :: List (Ty, String),
        funcArgs :: List (Ty, String),
        funcBody :: List Stmt
    }
        deriving (Show, Eq)

    data TyDecl = TyDecl {
        tyDeclName :: String, 
        tyDeclErasedParams :: List (Ty, String),
        tyDeclParams :: List (Ty, String), 
        tyDeclConstructors :: List Constructor
    }
        deriving (Show, Eq)

    data RecDecl = RecDecl {
        recDeclName :: String, 
        recDeclErasedParams :: List (Ty, String),
        recDeclParams :: List (Ty, String), 
        recDeclFields :: List (Ty, String)
    }
        deriving (Show, Eq)

    data Constructor = Constructor {
        conName :: String, 
        conArgs :: List (Ty, String), 
        conTy :: Ty
    }
        deriving (Show, Eq)

    data Stmt = Assign String Tm
            | Decl Ty String 
            | DeclAssign Ty String Tm 
            | Return Tm
            | Blank
            | Switch {
                switchOn :: List Tm,
                cases :: List Case
            }
            deriving (Show, Eq)

    data Case = Case {
        caseOn :: List Tm, 
        caseBody :: List Stmt
    }
        deriving (Show, Eq) 

    data Decl = Ty TyDecl | Rec RecDecl 
        deriving (Show, Eq)