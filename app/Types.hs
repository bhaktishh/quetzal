module Types where

import GHC.TypeLits (Nat)

type List a = [a]

data Prog = PDecl Decl | PFunc Func

data Ty
  = TyNat
  | TyBool
  | TyUnit
  | TyTy
  | TyCustom
      { tyName :: String,
        tyParams :: List Tm
      }
  | TyTm Tm
  deriving (Show, Eq)

data Tm
  = TmNat Nat
  | TmPlus Tm Tm
  | TmBool Bool
  | TmUnit
  | TmVar String
  | TmCon String (List Tm)
  | TmFunc Func
  | TmFuncCall Tm (List Tm)
  | TmBlock (List Stmt) Tm
  | TmIf Tm Tm Tm
  | TmReturn Tm
  | TmSwitch
      { switchOn :: List Tm,
        cases :: List Case
      }
  deriving (Show, Eq)

data Case = Case
  { caseOn :: List Tm,
    caseBody :: Tm
  }
  deriving (Show, Eq)

data Stmt
  = DeclAssign Ty String Tm
  | Assign String Tm
  | While
      { condition :: Tm,
        body :: Tm
      }
  deriving (Show, Eq)

data Func = Func
  { funcName :: String,
    funcRetTy :: Ty,
    funcArgs :: List AnnParam,
    funcBody :: Tm
  }
  deriving (Show, Eq)

data Decl = Ty TyDecl | Rec RecDecl

data TyDecl = TyDecl
  { tyDeclName :: String,
    tyDeclParams :: List AnnParam,
    tyDeclConstructors :: List Constructor
  }
  deriving (Show, Eq)

data RecDecl = RecDecl
  { recDeclName :: String,
    recDeclParams :: List AnnParam,
    recDeclFields :: List (Ty, String)
  }
  deriving (Show, Eq)

data Constructor = Constructor
  { conName :: String,
    conArgs :: List AnnParam,
    conTy :: Ty
  }
  deriving (Show, Eq)

data AnnParam = AnnParam (Ty, String) Bool deriving (Show, Eq) -- explicit = true or false. default true
