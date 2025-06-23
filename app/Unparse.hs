{-# LANGUAGE NamedFieldPuns #-}

module Unparse where

import Control.Monad.State.Lazy
import Data.List (intercalate, intersperse)
import ITypes

type Indent a = State (Int, Bool) a

indent :: Bool -> Int -> String
indent b n = if b then replicate n '\t' else ""

unparse :: IProg -> String
unparse x = evalState (uProg x) (0, False)

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
uTypes (ITy tdecl) = uTyDecl tdecl
uTypes (IRec recdecl) = uRecDecl recdecl

uRecDecl :: IRecDecl -> Indent String
uRecDecl
  IRecDecl
    { iRecDeclName,
      iRecDeclParams,
      iRecDeclFields
    } =
    do
      params <- mapM (uAnnParam False) iRecDeclParams
      fields <- mapM uRecDeclField iRecDeclFields
      pure $
        "record"
          ++ " "
          ++ iRecDeclName
          ++ " "
          ++ concat params
          ++ "where \n"
          ++ "\tconstructor Mk"
          ++ iRecDeclName
          ++ "\n"
          ++ concat fields

uRecDeclField :: IAnnParam -> Indent String
uRecDeclField (IAnnParam (var, ty) _) = do
  t <- uTy ty
  pure $ "\t" ++ var ++ " : " ++ t ++ "\n"

uTyDecl :: ITyDecl -> Indent String
uTyDecl
  ITyDecl
    { iTyDeclName,
      iTyDeclParams,
      iTyDeclConstructors
    } = do
    params <- mapM (uAnnParam True) iTyDeclParams
    constructors <- mapM uTyDeclConstructor iTyDeclConstructors
    pure $
      "data"
        ++ " "
        ++ iTyDeclName
        ++ " : "
        ++ concat params
        ++ "PType where \n"
        ++ concat constructors

uTyDeclConstructor :: IConstructor -> Indent String
uTyDeclConstructor IConstructor {iConName, iConArgs, iConTy} =
  do
    params <- mapM (uAnnParam True) iConArgs
    ty <- uTy iConTy
    pure $
      "\t"
        ++ iConName
        ++ " : "
        ++ concat params
        ++ ty
        ++ "\n"

uAnnParam :: Bool -> IAnnParam -> Indent String
uAnnParam arrow (IAnnParam (var, ty) vis) = do
  t <- uTy ty
  pure $ (if vis then "(" else "{") ++ var ++ " : " ++ t ++ (if vis then ")" else "}") ++ (if arrow then " -> " else " ")

uTy :: ITy -> Indent String
uTy ITyNat = pure "Nat"
uTy ITyBool = pure "Bool"
uTy ITyTy = pure "PType"
uTy ITyUnit = pure "()"
uTy (ITyCustom name params) = do
  params <- mapM uTm params
  pure $ name ++ " " ++ unwords params
uTy (ITyFunc args) = do
  args <- mapM uFuncArg args
  pure $ intercalate " -> " args
uTy (ITyTm t) = uTm t
uTy (ITyList t) = (++) "List " <$> uTy t

uFuncArg :: (Maybe String, ITy) -> Indent String
uFuncArg (Nothing, ty) = uTy ty
uFuncArg (Just v, ty) = uTy ty >>= \x -> pure $ "(" ++ v ++ " : " ++ x ++ ")"

uTm :: ITm -> Indent String
uTm (ITmNat n) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ show n
uTm (ITmBool b) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ show b
uTm (ITmPlus n1 n2) = do
  (ind, t) <- get
  put (ind, False)
  t1 <- uTm n1
  t2 <- uTm n2
  pure $ indent t ind ++ "(" ++ (if n1 == ITmNat 1 then "S " else t1 ++ " + ") ++ t2 ++ ")"
uTm (ITmMinus n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "(" ++ t1 ++ " - " ++ t2 ++ ")"
uTm (ITmBEq n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "(" ++ t1 ++ " == " ++ t2 ++ ")"
uTm (ITmBLT n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "(" ++ t1 ++ " < " ++ t2 ++ ")"
uTm (ITmVar v) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ v
uTm (ITmFuncCall f args) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm f
  args <- mapM uTm args
  pure $ indent t ind ++ "(" ++ tm ++ (if null args then "" else " ") ++ unwords args ++ ")"
uTm (ITmCon c args) = do
  args <- mapM uTm args
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ c ++ (if null args then "" else " ") ++ unwords args
uTm (ITmIf cond thenCase elseCase) = do
  (ind, t) <- get
  put (ind, False)
  cond <- uTm cond
  put (ind + 1, True)
  thenCase <- uTm thenCase
  put (ind + 1, True)
  elseCase <- uTm elseCase
  put (ind, False)
  pure $ indent t ind ++ "if " ++ cond ++ " then \n" ++ thenCase ++ "\n" ++ indent t ind ++ "else \n" ++ elseCase
uTm ITmUnit = pure "()"
uTm (ITmTy t) = do
  (ind, _) <- get
  put (ind, False)
  uTy t
uTm (ITmFunc f) = uFuncs f
uTm (ITmNot tm) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm tm
  pure $ indent t ind ++ "not " ++ tm
uTm (ITmLet v ty val body) = do
  (ind, t) <- get
  put (ind, False)
  ty <- uTy ty
  tm <- uTm val
  put (ind + 1, True)
  b <- uTm body
  put (ind, False)
  pure $ indent t ind ++ "let " ++ v ++ " : " ++ ty ++ " = " ++ tm ++ " in\n" ++ b
uTm (ITmMatch on cases) = undefined

uFuncs :: IFunc -> Indent String
uFuncs IFunc {iFuncName, iFuncRetTy, iFuncArgs, iFuncBody, iWhere} = do
  (ind, t) <- get
  put (ind, False)
  retty <- uTy iFuncRetTy
  args <- mapM (uAnnParam True) iFuncArgs
  put (ind + 1, True)
  body <- uTm iFuncBody
  put (ind + 1, True)
  deps <- mapM uTm iWhere
  put (ind, False)
  pure $
    indent t ind
      ++ iFuncName
      ++ " : "
      ++ concat args
      ++ retty
      ++ "\n"
      ++ indent t ind
      ++ iFuncName
      ++ " "
      ++ unwords (map (\(IAnnParam (v, _) _) -> v) (filter (\(IAnnParam (_, _) vis) -> vis) iFuncArgs))
      ++ " = \n"
      ++ body
      ++ if null deps
        then ""
        else
          indent t ind
            ++ "\nwhere \n"
            ++ intercalate "\n" deps
