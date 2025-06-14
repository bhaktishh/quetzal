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
  | ITyTm ITm
  deriving (Show, Eq)

data ITm
  = ITmNat Nat
  | ITmPlus ITm ITm
  | ITmBool Bool
  | ITmUnit
  | ITmNot ITm
  | ITmTy ITy 
  | ITmVar String 
  | ITmCon String (List ITm)
  | ITmFunc Func (List ITm) -- where clause 
  | ITmFuncCall ITm (List ITm)
  | ITmIf ITm ITm ITm 
  | ITmMatch (List ITm) (List ITm, ITm)
  | ITmLet ITm ITy ITm 
  deriving (Show, Eq)