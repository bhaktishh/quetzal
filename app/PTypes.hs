{-# LANGUAGE NamedFieldPuns #-}

module PTypes where

import qualified Data.Map as M
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
  | PTyPair PTy PTy
  | PTyHole
  deriving (Show, Eq, Ord)

data PTm
  = PTmNat Nat
  | PTmThis
  | PTmDotRec PTm PTm -- a.b = b field of record a
  | PTmDot PTm PTm (List PTm) -- a.f() ---> let a = f a ; x = a.f(b, c) ---> (x, a) <- f a b c
  | PTmPlus PTm PTm
  | PTmPair PTm PTm
  | PTmString String
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
  | PTmIO
  | PTmPTy PTy
  | PTmVar String
  | PTmWildCard
  | PTmTernary PTm PTm PTm
  | PTmCon String (List PTm)
  | PTmFuncCall PTm (List PTm)
  | PTmIf PTm PTm PTm
  deriving (Show, Eq, Ord)

-- when we need to use some term as a variable binding
-- only applies to certain typeformers, others should not be used for implicit variable binding
myShowTm :: PTm -> String
myShowTm (PTmNat x) = show x
myShowTm PTmThis = "this"
myShowTm (PTmString s) = s
myShowTm (PTmVar s) = s
myShowTm (PTmCon c []) = c
myShowTm PTmWildCard = "_"
myShowTm (PTmPTy t) = myShowTy t
myShowTm x = show x

myShowTy :: PTy -> String
myShowTy (PTyPTm t) = myShowTm t
myShowTy (PTyCustom {tyName, tyParams = []}) = tyName
myShowTy x = show x

data Switch = Switch
  { switchOn :: List PTm,
    cases :: List Case,
    defaultCase :: Maybe Case
  }
  deriving (Show, Eq, Ord)

data Case = Case
  { caseOn :: List PTm,
    caseBody :: Stmt
  }
  deriving (Show, Eq, Ord)

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
  | StDot PTm PTm (List PTm)
  deriving (Show, Eq, Ord)

data Eff = IO | Other deriving (Show, Eq, Ord)

data Func = Func
  { funcName :: String,
    funcRetTy :: PTy,
    funcArgs :: List AnnParam,
    funcBody :: Stmt,
    funcEff :: Maybe Eff,
    funcDirective :: Maybe Directive
  }
  deriving (Show, Eq, Ord)

data Decl = PTy TyDecl | Rec RecDecl
  deriving (Show, Eq)

data TyDecl = TyDecl
  { tyDeclName :: String,
    tyDeclParams :: List AnnParam,
    tyDeclConstructors :: List Constructor
  }
  deriving (Show, Eq)

data RecDecl = RecDecl
  { recDeclTyName :: String,
    recDeclConName :: String,
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

data AnnParam = AnnParam (PTy, String) Bool deriving (Show, Eq, Ord) -- explicit = true or false. default true

data Action = Action
  { actionName :: String,
    actionRetTy :: (PTy, Maybe String),
    actionStTrans :: (PTm, PTm)
  }
  deriving (Show, Eq)

data FSM = FSM
  { resourceTy :: PTy,
    stateTy :: PTy,
    initCons :: List Func,
    actions :: List Action
  }
  deriving (Show, Eq)

data DirectiveSub = DFSM PTy PTy deriving (Show, Eq, Ord) -- FSM(Store, Access) = DFSM Store Access

data DirectiveTy
  = DAction
      { directiveReturns :: (PTy, Maybe String), -- eg returns LoginResult r
        directiveStTrans :: (PTm, PTm)
      }
  | DInit
  | DRun
      { directiveReturns :: (PTy, Maybe String),
        directiveWith :: PTm, -- eg with this = mkStore("secret", "pub")
        directiveStTrans :: (PTm, PTm)
      }
  deriving (Show, Eq, Ord)

data Directive = Directive DirectiveSub DirectiveTy
  deriving (Show, Eq, Ord)
