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
  | ITyTm ITm
  | ITyHole 
  deriving (Show, Eq)

data ITm
  = ITmNat Nat
  | ITmPlus ITm ITm
  | ITmMinus ITm ITm
  | ITmBEq ITm ITm
  | ITmBLT ITm ITm
  | ITmBool Bool
  | ITmUnit
  | ITmNot ITm
  | ITmTy ITy
  | ITmVar String
  | ITmCon String (List ITm)
  | ITmFunc IFunc -- where clause
  | ITmFuncCall ITm (List ITm)
  | ITmIf ITm ITm ITm
  | ITmMatch (List ITm) (List (List ITm, ITm))
  | ITmLet String (Maybe ITy) ITm ITm
  deriving (Show, Eq)

data IConstructor = IConstructor
  { iConName :: String,
    iConArgs :: List IAnnParam,
    iConTy :: ITy
  }
  deriving (Show, Eq)

data IAnnParam = IAnnParam (String, ITy) Bool -- explicit = true or false. default true
  deriving (Show, Eq)

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

data IProgEl = IIDecl IDecl | IIFunc IFunc
  deriving (Show, Eq)

data IFunc = IFunc
  { iFuncName :: String,
    iFuncArgs :: List IAnnParam,
    iFuncBody :: ITm,
    iFuncRetTy :: ITy,
    iWhere :: List ITm
  }
  deriving (Show, Eq)