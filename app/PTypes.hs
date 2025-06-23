module PTypes where

import GHC.TypeLits (Nat)

type List a = [a]

data ProgEl = PDecl Decl | PFunc Func
  deriving (Show, Eq)

type Prog = List ProgEl

data PTy
  = PTyNat
  | PTyBool
  | PTyUnit
  | PTyTy
  | PTyFunc
      { tyFuncArgs :: List (PTy, String),
        tyFuncRetTy :: PTy
      }
  | PTyCustom
      { tyName :: String,
        tyParams :: List PTm
      }
  | PTyList PTy
  | PTyPTm PTm
  | PTyHole 
  deriving (Show, Eq)

data PTm
  = PTmNat Nat
  | PTmPlus PTm PTm
  | PTmMinus PTm PTm
  | PTmBEq PTm PTm
  | PTmBLT PTm PTm
  | PTmBool Bool
  | PTmUnit
  | PTmNot PTm
  | PTmPTy PTy
  | PTmVar String
  | PTmCon String (List PTm)
  | PTmFunc Func
  | PTmFuncCall PTm (List PTm)
  | PTmBlock (List Stmt) PTm
  | PTmIf PTm PTm PTm
  | PTmReturn PTm
  | PTmSwitch Switch
  deriving (Show, Eq)

data Switch = Switch
  { switchOn :: List PTm,
    cases :: List Case
  }
  deriving (Show, Eq)

data Case = Case
  { caseOn :: List PTm,
    caseBody :: PTm
  }
  deriving (Show, Eq)

data Stmt
  = DeclAssign (Maybe PTy) String PTm
  | Assign String PTm
  | While
      { condition :: PTm,
        body :: List Stmt
      }
  deriving (Show, Eq)

data Func = Func
  { funcName :: String,
    funcRetTy :: PTy,
    funcArgs :: List AnnParam,
    funcBody :: PTm
  }
  deriving (Show, Eq)

data Decl = PTy TyDecl | Rec RecDecl
  deriving (Show, Eq)

data TyDecl = TyDecl
  { tyDeclName :: String,
    tyDeclParams :: List AnnParam,
    tyDeclConstructors :: List Constructor
  }
  deriving (Show, Eq)

data RecDecl = RecDecl
  { recDeclName :: String,
    recDeclParams :: List AnnParam,
    recDeclFields :: List (PTy, String)
  }
  deriving (Show, Eq)

data Constructor = Constructor
  { conName :: String,
    conArgs :: List AnnParam,
    conTy :: PTy
  }
  deriving (Show, Eq)

data AnnParam = AnnParam (PTy, String) Bool deriving (Show, Eq) -- explicit = true or false. default true
