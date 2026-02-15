module ITypes where

import GHC.TypeLits
import PTypes

data ITy
  = ITyNat
  | ITyBool
  | ITyUnit
  | ITyTy
  | ITyFunc (List (Maybe String, ITy))
  | ITyCustom String (List ITm)
  | ITyList ITy
  | ITyPair (ITy, ITy)
  | ITyIO ITy
  | ITyTm ITm
  | ITyHole
  deriving (Show, Eq)

data ITm
  = ITmNat Nat
  | ITmWildCard
  | ITmPlus ITm ITm
  | ITmMinus ITm ITm
  | ITmMult ITm ITm
  | ITmDiv ITm ITm
  | ITmMod ITm ITm
  | ITmBEq ITm ITm
  | ITmBLT ITm ITm
  | ITmBAnd ITm ITm
  | ITmBOr ITm ITm
  | ITmBool Bool
  | ITmPair ITm ITm
  | ITmUnit
  | ITmNot ITm
  | ITmList ITy (List ITm)
  | ITmTy ITy
  | ITmVar String
  | ITmCon String (List ITm)
  | ITmFunc IFunc -- where clause
  | ITmFuncCall ITm (List ITm)
  | ITmIf ITm ITm ITm
  | ITmMatch (List ITm) (List (List ITm, ITm))
  | ITmMatchImpossible (List ITm) (List ITm)
  | ITmLet String (Maybe ITy) ITm ITm
  | ITmLam (List ITm) ITm
  | ITmBind ITm ITm -- ITmBind a b = a >>= b
  deriving (Show, Eq)

data IConstructor = IConstructor
  { iConName :: String,
    iConArgs :: List IAnnParam,
    iConTy :: ITy
  }
  deriving (Show, Eq)

data IAnnParam = IAnnParam (String, ITy) Bool -- explicit = true or false. default true
  deriving (Show, Eq)

data IParam = IParam ITy Bool

data IRecDecl = IRecDecl
  { iRecDeclName :: String,
    iRecDeclParams :: List IAnnParam,
    iRecDeclConstructor :: String,
    iRecDeclFields :: List IAnnParam
  }
  deriving (Show, Eq)

data ITyDecl = ITyDecl
  { iTyDeclName :: String,
    iTyDeclParams :: List IAnnParam,
    iTyDeclConstructors :: List IConstructor
  }
  deriving (Show, Eq)

data IDecl = ITy ITyDecl | IRec IRecDecl
  deriving (Show, Eq)

type IProg = List IProgEl

data IProgEl = IIDecl IDecl | IIFunc IFunc | IIImport String
  deriving (Show, Eq)

data IFunc = IFunc
  { iFuncName :: String,
    iFuncArgs :: List IAnnParam,
    iFuncBody :: List (ITm, ITm),
    iFuncRetTy :: ITy,
    iWhere :: List ITm
  }
  deriving (Show, Eq)

data IImplementation = Impl
  { iImplicits :: List IAnnParam,
    iConstraints :: List ITm,
    iSubject :: ITm,
    iBody :: IImplBody
  }
  deriving (Show, Eq)

type IImplBody = List IImplCase

data IImplCase = IImplCase
  { iArgs :: (ITm, ITm),
    iBarArgs :: List ITm,
    iWith :: Maybe ITm,
    iCaseBody :: IImplCaseBody
  }
  deriving (Show, Eq)

data IImplCaseBody = Tm ITm | Nest (List IImplCase) deriving (Show, Eq)

data IFSM = IFSM
  { idxm :: ITyDecl,
    conc :: IAnnParam,
    funcs :: List IFunc,
    run :: IFunc
  }