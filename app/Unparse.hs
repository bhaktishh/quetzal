{-# LANGUAGE NamedFieldPuns #-}

module Unparse where 

import Control.Monad.State.Lazy 
import ITypes 

type Indent a = State (Int, Bool) a

uProg :: IProg -> Indent String 
uProg [] = pure ""
uProg (x : xs) = case x of
  IIDecl decl -> do
    dec <- uTypes decl
    prog <- uProg xs
    pure $ dec ++ "\n\n" ++ prog
  IIFunc func -> do
    f <- uFuncs func
    pr <- uProg xs
    pure $ f ++ "\n\n" ++ pr
 
uTypes :: IDecl -> Indent String 
uTypes = undefined 

uFuncs :: IFunc -> Indent String 
uFuncs IFunc {iFuncName, iFuncRetTy, iFuncArgs, iFuncBody} = undefined 