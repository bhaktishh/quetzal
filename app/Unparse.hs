{-# LANGUAGE NamedFieldPuns #-}

module Unparse where

import Control.Monad.State.Lazy
import Data.List (intercalate)
import ITypes
import PToI (deriveDecEq)

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
    (ind, t) <- get
    put (ind, False)
    impl <- uImplementation (deriveDecEq decl)
    put (ind, t)
    prog <- uProg xs
    pure $ dec ++ "\n\n" ++ impl ++ "\n\n" ++ prog
  IIFunc func -> do
    f <- uFuncs func
    pr <- uProg xs
    pure $ f ++ "\n\n" ++ pr
  IIImport m -> do
    pr <- uProg xs
    pure $ "import " ++ m ++ "\n\n" ++ pr

uTypes :: IDecl -> Indent String
uTypes (ITy tdecl) = uTyDecl tdecl
uTypes (IRec recdecl) = uRecDecl recdecl

uRecDecl :: IRecDecl -> Indent String
uRecDecl
  IRecDecl
    { iRecDeclName,
      iRecDeclConstructor,
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
          ++ "\tconstructor "
          ++ iRecDeclConstructor
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
        ++ "Type where \n"
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
  (ind, tt) <- get
  put (ind, False)
  t <- uTy ty
  put (ind, tt)
  pure $ (if vis then "(" else "{") ++ var ++ " : " ++ t ++ (if vis then ")" else "}") ++ (if arrow then " -> " else " ")

uTy :: ITy -> Indent String
uTy ITyNat = pure "Nat"
uTy ITyBool = pure "Bool"
uTy ITyTy = pure "Type"
uTy ITyUnit = pure "()"
uTy (ITyCustom name params) = do
  (ind, t) <- get
  put (ind, False)
  params <- mapM uTm params
  put (ind, t)
  pure $ name ++ " " ++ unwords params
uTy (ITyFunc args) = do
  args <- mapM uFuncArg args
  pure $ intercalate " -> " args
uTy (ITyTm t) = uTm t
uTy (ITyList t) = (++) "List " <$> uTy t
uTy ITyHole = pure $ "?"

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
uTm (ITmMod n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "(" ++ t1 ++ " % " ++ t2 ++ ")"
uTm (ITmMult n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "(" ++ t1 ++ " * " ++ t2 ++ ")"
uTm (ITmDiv n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "(" ++ t1 ++ " / " ++ t2 ++ ")"
uTm (ITmBEq n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  -- pure $ indent t ind ++ "(" ++ "decEq " ++ t1 ++ " " ++ t2 ++ ")"
  pure $ indent t ind ++ "(" ++ t1 ++ " == " ++ t2 ++ ")"
uTm (ITmBLT n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  (ind, t) <- get
  put (ind, False)
  -- pure $ indent t ind ++ "(" ++ "isLT " ++ t1 ++ " " ++ t2 ++ ")"
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
  (ind, t) <- get
  put (ind, False)
  args <- mapM uTm args
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
uTm ITmUnit = do
  (ind, t) <- get
  pure $ indent t ind ++ "()"
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
uTm (ITmLet v Nothing val body) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm val
  put (ind + 1, True)
  b <- uTm body
  put (ind, False)
  pure $ indent t ind ++ "let " ++ v ++ " = " ++ tm ++ " in\n" ++ b
uTm (ITmLet v (Just ty) val body) = do
  (ind, t) <- get
  put (ind, False)
  ty <- uTy ty
  tm <- uTm val
  put (ind + 1, True)
  b <- uTm body
  put (ind, False)
  pure $ indent t ind ++ "let " ++ v ++ " : " ++ ty ++ " = " ++ tm ++ " in\n" ++ b
uTm (ITmMatch on cases) = do
  (ind, t) <- get
  put (ind, False)
  on <- mapM uTm on
  put (ind + 1, True)
  cases <-
    mapM
      ( \(xs, v) -> do
          (ind, t) <- get
          put (ind, False)
          xs <- mapM uTm xs
          put (ind, False)
          v <- uTm v
          pure (xs, v)
      )
      cases
  put (ind, t)
  pure $
    indent t ind
      ++ "(case "
      ++ "("
      ++ intercalate "," on
      ++ ")"
      ++ " of\n"
      ++ indent True (ind + 1)
      ++ intercalate
        ("\n" ++ indent True (ind + 1))
        (map (\(xs, tm) -> "(" ++ intercalate "," xs ++ ")" ++ " => " ++ tm) cases)
      ++ ")"
uTm (ITmMatchImpossible on cases) = do
  (ind, t) <- get
  put (ind, False)
  on <- mapM uTm on
  cases <- mapM uTm cases
  pure $
    indent t ind
      ++ "(case "
      ++ "("
      ++ intercalate "," on
      ++ ")"
      ++ " of "
      ++ "("
      ++ intercalate "," cases
      ++ ")"
      ++ " impossible"
      ++ ")"
uTm (ITmList t l) = undefined
uTm (ITmLam v tm) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm tm
  put (ind, t)
  pure $ indent t ind ++ putParens ("\\" ++ v ++ " => " ++ tm)

uFuncs :: IFunc -> Indent String
uFuncs IFunc {iFuncName, iFuncRetTy, iFuncArgs, iFuncBody, iWhere} = do
  (ind, t) <- get
  put (ind, False)
  retty <- uTy iFuncRetTy
  args <- mapM (uAnnParam True) iFuncArgs
  put (ind + 1, True)
  body <- uTm iFuncBody
  put (ind, False)
  deps <-
    mapM
      ( \i -> do
          (ind, t) <- get
          put (ind + 1, True)
          uTm i
      )
      iWhere
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
            ++ intercalate "\n where \n" deps

uImplementation :: IImplementation -> Indent String
uImplementation Impl {iImplicits, iConstraints, iSubject, iBody} = do
  (ind, t) <- get
  put (ind, False)
  implicits <- mapM (uAnnParam True) iImplicits
  constraints <- mapM uTm iConstraints
  subject <- uTm iSubject
  put (ind + 1, True)
  body <- mapM uImplCase iBody
  pure $
    indent t ind
      ++ concat implicits
      ++ intercalate " => " (map putParens constraints)
      ++ (if not (null constraints) then " => " else "")
      ++ "DecEq "
      ++ putParens subject
      ++ " where \n"
      ++ intercalate "\n" body

doWith :: Maybe String -> String
doWith Nothing = ""
doWith (Just s) = " with " ++ s ++ "\n"

uImplCase :: IImplCase -> Indent String
uImplCase IImplCase {iArgs, iBarArgs, iWith, iCaseBody} = do
  (ind, t) <- get
  put (ind, False)
  t1 <- uTm (fst iArgs)
  t2 <- uTm (snd iArgs)
  barArgs <- mapM uTm iBarArgs
  let barArgs' = concatMap (" | " ++) barArgs
  w <- mapM uTm iWith
  let w' = doWith w
  body <- uImplCaseBody iCaseBody
  (ind, t) <- get
  pure $
    indent True ind ++ "decEq " ++ putParens t1 ++ " " ++ putParens t2 ++ barArgs' ++ (if null barArgs' then "" else " ") ++ w' ++ body

uImplCaseBody :: IImplCaseBody -> Indent String
uImplCaseBody (Tm tm) = do
  (ind, t) <- get
  put (ind, False)
  tm' <- uTm tm
  put (ind, t)
  pure $ " = " ++ tm'
uImplCaseBody (Nest tms) = do
  (ind, t) <- get
  put (ind + 1, True)
  tms <- mapM uImplCase tms
  put (ind, True)
  pure $ intercalate "\n" tms

putParens :: String -> String
putParens s = "(" ++ s ++ ")"