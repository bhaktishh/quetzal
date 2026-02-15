module PTypes where

import GHC.TypeLits (Nat)

type List a = [a]

data ProgEl = PDecl Decl | PFunc Func | PImport String | PFSM FSM
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
  | PTmDot PTm PTm
  | PTmPlus PTm PTm
  | PTmMinus PTm PTm
  | PTmMult PTm PTm
  | PTmDiv PTm PTm
  | PTmMod PTm PTm
  | PTmBEq PTm PTm
  | PTmBLT PTm PTm
  | PTmBAnd PTm PTm
  | PTmBOr PTm PTm
  | PTmBool Bool
  | PTmList PTy (List PTm)
  | PTmUnit
  | PTmNot PTm
  | PTmPTy PTy
  | PTmVar String
  | PTmWildCard
  | PTmTernary PTm PTm PTm
  | PTmCon String (List PTm)
  | PTmFunc Func
  | PTmFuncCall PTm (List PTm)
  | PTmIf PTm PTm PTm
  deriving (Show, Eq)

data Switch = Switch
  { switchOn :: List PTm,
    cases :: List Case,
    defaultCase :: Maybe Case
  }
  deriving (Show, Eq)

data Case = Case
  { caseOn :: List PTm,
    caseBody :: Stmt
  }
  deriving (Show, Eq)

data Stmt
  = StDeclAssign (Maybe PTy) String PTm
  | StAssign String PTm
  | StWhile
      { condition :: PTm,
        body :: Stmt
      }
  | StEWhile
      { condition :: PTm,
        body :: Stmt
      }
  | StReturn PTm
  | StIf PTm Stmt Stmt
  | StEIf PTm Stmt Stmt
  | StBlock (List Stmt)
  | StSwitch Switch
  | StSkip
  deriving (Show, Eq)

data Eff = IO | Other deriving (Show, Eq)

data Func = Func
  { funcName :: String,
    funcRetTy :: PTy,
    funcArgs :: List AnnParam,
    funcBody :: Stmt,
    funcEff :: Maybe Eff
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

data Action = Action
  { actionName :: String,
    actionRetTy :: AnnParam,
    actionStTrans :: (PTm, PTm),
    actionFunc :: Func
  }
  deriving (Show, Eq)

data FSM = FSM
  { resource :: AnnParam,
    stateTy :: String,
    initCons :: List Func,
    actions :: List Action
  }
  deriving (Show, Eq)