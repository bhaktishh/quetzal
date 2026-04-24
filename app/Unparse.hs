{-# LANGUAGE NamedFieldPuns #-}

module Unparse where

import Control.Monad.State.Lazy
import Data.List (intercalate, sort)
import Data.Maybe (fromMaybe)
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
    prog <- uProg xs
    pure $ dec ++ "\n\n" ++ prog
  IIFunc func -> do
    f <- uFuncs func
    pr <- uProg xs
    pure $ f ++ "\n\n" ++ pr
  IIImport m -> do
    pr <- uProg xs
    pure $ "import " ++ m ++ "\n" ++ pr
  IIImplementation i -> do
    (ind, t) <- get
    put (ind, t)
    i' <- uImplementation i
    put (ind, False)
    pr <- uProg xs
    pure $ i' ++ "\n\n" ++ pr

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
  t <- uTy False ty
  pure $ "\t" ++ var ++ " : " ++ t ++ "\n"

uTyDecl :: ITyDecl -> Indent String
uTyDecl
  ITyDecl
    { iTyDeclName,
      iTyDeclParams,
      iTyDeclConstructors
    } = do
    (ind, t) <- get
    params <- mapM (uAnnParam True) iTyDeclParams
    put (ind + 1, True)
    constructors <- mapM uTyDeclConstructor iTyDeclConstructors
    put (ind, t)
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
    (ind, t) <- get
    params <- mapM (uAnnParam True) iConArgs
    ty <- uTy False iConTy
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
  t <- uTy False ty
  put (ind, tt)
  pure $ (if vis then "(" else "{") ++ (if var /= "" then var ++ " : " else "") ++ t ++ (if vis then ")" else "}") ++ (if arrow then " -> " else " ")

-- b : Bool = putParens?
uTy :: Bool -> ITy -> Indent String
uTy _ ITyNat = pure "Nat"
uTy _ ITyBool = pure "Bool"
uTy _ ITyTy = pure "Type"
uTy _ ITyUnit = pure "()"
uTy _ (ITyApp name params) = do
  (ind, t) <- get
  put (ind, False)
  params <- mapM (uTm True) params
  name <- uTy False name
  put (ind, t)
  pure $ name ++ (if null params then "" else " " ++ unwords params)
uTy _ (ITyFunc args) = do
  args <- mapM uFuncArg args
  pure $ intercalate " -> " args
uTy b (ITyTm t) = uTm b t
uTy _ (ITyList t) = (++) "List " <$> uTy True t
uTy _ ITyHole = pure ""
uTy _ (ITyPair t1 t2) = do
  (ind, t) <- get
  put (ind, False)
  t1' <- uTy False t1
  t2' <- uTy False t2
  pure $ indent t ind ++ putParens True (t1' ++ ", " ++ t2')
uTy _ (ITyIO ty) = do
  (ind, t) <- get
  put (ind, False)
  ty' <- uTy True ty
  pure $ indent t ind ++ "IO " ++ ty'
uTy _ (ITyVar v) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ v

uFuncArg :: (Maybe String, ITy) -> Indent String
uFuncArg (Nothing, ty) = uTy False ty
uFuncArg (Just v, ty) = uTy False ty >>= \x -> pure $ "(" ++ v ++ " : " ++ x ++ ")"

uTm :: Bool -> ITm -> Indent String
uTm _ (ITmNat n) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ show n
uTm _ (ITmString s) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "\"" ++ s ++ "\""
uTm _ (ITmDot a f) = do
  (ind, t) <- get
  put (ind, False)
  a' <- uTm False a
  f' <- uTm False f
  put (ind, t)
  pure $ indent t ind ++ a' ++ "." ++ f'
uTm _ ITmWildCard = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ "_"
uTm _ (ITmBool b') = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ show b'
uTm b (ITmPlus n1 n2) = do
  (ind, t) <- get
  put (ind, False)
  t1 <- uTm True n1
  t2 <- uTm True n2
  pure $ indent t ind ++ putParens b (t1 ++ " + " ++ t2)
uTm b (ITmMinus n1 n2) = do
  t1 <- uTm True n1
  t2 <- uTm True n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " - " ++ t2)
uTm b (ITmMod n1 n2) = do
  t1 <- uTm True n1
  t2 <- uTm True n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " % " ++ t2)
uTm b (ITmMult n1 n2) = do
  t1 <- uTm True n1
  t2 <- uTm True n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " * " ++ t2)
uTm b (ITmDiv n1 n2) = do
  t1 <- uTm True n1
  t2 <- uTm True n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " / " ++ t2)
uTm b (ITmBEq n1 n2) = do
  t1 <- uTm False n1
  t2 <- uTm False n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " == " ++ t2)
uTm b (ITmBOr n1 n2) = do
  t1 <- uTm True n1
  t2 <- uTm True n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " || " ++ t2)
uTm b (ITmBAnd n1 n2) = do
  t1 <- uTm True n1
  t2 <- uTm True n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " && " ++ t2)
uTm b (ITmBLT n1 n2) = do
  t1 <- uTm False n1
  t2 <- uTm False n2
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ putParens b (t1 ++ " < " ++ t2)
uTm _ (ITmVar v) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ v
uTm b (ITmFuncCall f args) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm False f
  args <- mapM (uTm True) args
  pure $ indent t ind ++ putParens (b && not (null args)) (tm ++ (if null args then "" else " ") ++ unwords args)
uTm b (ITmCon c args) = do
  (ind, t) <- get
  put (ind, False)
  args <- mapM (uTm True) args
  pure $ indent t ind ++ putParens (b && not (null args)) (c ++ (if null args then "" else " ") ++ unwords args)
uTm b (ITmIf cond thenCase elseCase) = do
  (ind, t) <- get
  put (ind, False)
  cond <- uTm False cond
  put (ind + 1, True)
  thenCase <- uTm False thenCase
  put (ind + 1, True)
  elseCase <- uTm False elseCase
  put (ind, False)
  pure $ indent t ind ++ putParens b ("if " ++ cond ++ " then \n" ++ thenCase ++ "\n" ++ indent True ind ++ "else \n" ++ elseCase)
uTm _ ITmUnit = do
  (ind, t) <- get
  pure $ indent t ind ++ "()"
uTm b (ITmTy t) = do
  (ind, _) <- get
  put (ind, False)
  uTy b t
uTm _ (ITmFunc f) = uFuncs f
uTm b (ITmNot tm) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm True tm
  pure $ indent t ind ++ putParens b ("not " ++ tm)
uTm b (ITmLet v Nothing val body) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm False val
  put (ind + 1, True)
  bd <- uTm False body
  put (ind, False)
  pure $ indent t ind ++ putParens b ("let " ++ v ++ " = " ++ tm ++ " in\n" ++ bd)
uTm b (ITmLet v (Just ty) val body) = do
  (ind, t) <- get
  put (ind, False)
  ty <- uTy False ty
  tm <- uTm False val
  put (ind + 1, True)
  bd <- uTm False body
  put (ind, False)
  pure $ indent t ind ++ putParens b ("let " ++ v ++ " : " ++ ty ++ " = " ++ tm ++ " in\n" ++ bd)
uTm b (ITmMatch on cases) = do
  (ind, t) <- get
  put (ind, False)
  on <- mapM (uTm False) on
  put (ind + 1, True)
  cases <-
    mapM
      ( \(xs, v) -> do
          (ind, t) <- get
          put (ind, False)
          xs <- mapM (uTm False) xs
          put (ind, False)
          v <- uTm False v
          pure (xs, v)
      )
      cases
  put (ind, t)
  pure $
    indent t ind
      ++ putParens
        b
        ( "case "
            ++ ( if length on < 2
                   then concat on
                   else
                     putParens True (intercalate "," on)
               )
            ++ " of\n"
            ++ (if null cases then "" else indent True (ind + 1))
            ++ intercalate
              ("\n" ++ indent True (ind + 1))
              (map (\(xs, tm) -> (if length xs < 2 then concat xs else putParens True (intercalate "," xs)) ++ " => " ++ tm) cases)
        )
uTm b (ITmMatchImpossible on cases) = do
  (ind, t) <- get
  put (ind, False)
  on <- mapM (uTm False) on
  cases <- mapM (uTm b) cases
  pure $
    indent t ind
      ++ putParens
        b
        ( "case "
            ++ ( if length on < 2
                   then concat on
                   else
                     putParens b (intercalate "," on)
               )
            ++ " of "
            ++ ( if length cases < 2
                   then concat cases
                   else
                     putParens b (intercalate ", " cases)
               )
            ++ " impossible"
        )
uTm _ (ITmList _ l) = do
  (ind, t) <- get
  put (ind, False)
  ls <- mapM (uTm False) l
  put (ind, t)
  pure $ indent t ind ++ "[" ++ intercalate "," ls ++ "]"
uTm _ (ITmLam v tm) = do
  (ind, t) <- get
  put (ind, False)
  vs <- mapM (uTm False) v
  tm <- uTm False tm
  put (ind, t)
  pure $ indent t ind ++ putParens True ("\\" ++ (if length vs < 2 then concat vs else putParens True (intercalate ", " vs)) ++ " => " ++ tm) -- todo check
uTm _ (ITmPair t1 t2) = do
  (ind, t) <- get
  put (ind, False)
  t1' <- uTm False t1
  t2' <- uTm False t2
  pure $ indent t ind ++ putParens True (t1' ++ ", " ++ t2')
uTm b (ITmBind t1 t2) = do
  (ind, t) <- get
  put (ind, False)
  t1' <- uTm False t1
  t2' <- uTm False t2
  pure $ indent t ind ++ putParens b (t1' ++ " >>= " ++ t2')
uTm _ (ITmDo d) = do
  (ind, t) <- get
  put (ind + 1, True)
  dos <- mapM uTmDo d
  put (ind, t)
  pure $ indent t ind ++ "do \n" ++ intercalate "\n" dos

uTmDo :: ITmDo -> Indent String
uTmDo (ITmDoLet v (Just ty') x) = do
  (ind, t) <- get
  put (ind, False)
  ty <- uTy False ty'
  tm <- uTm False x
  put (ind, t)
  pure $ indent t ind ++ "let " ++ v ++ " : " ++ ty ++ " = " ++ tm
uTmDo (ITmDoLet v Nothing x) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm False x
  put (ind, t)
  pure $ indent t ind ++ "let " ++ v ++ " = " ++ tm
uTmDo (ITmDoBind xs x) = do
  (ind, t) <- get
  put (ind, False)
  tm <- uTm False x
  xs' <- mapM (uTm False) xs
  put (ind, t)
  pure $ indent t ind ++ (if length xs' < 2 then concat xs' else putParens True (intercalate "," xs')) ++ " <- " ++ tm
uTmDo (ITmDoCase ons branches) = do
  (ind, t) <- get
  put (ind, False)
  on <- mapM (uTm False) ons
  put (ind + 1, True)
  cases <-
    mapM
      ( \(xs, v) -> do
          (ind, t) <- get
          put (ind, False)
          xs <- mapM (uTm False) xs
          put (ind, False)
          v <- uTm False v
          pure (xs, v)
      )
      branches
  put (ind, t)
  pure $
    indent t ind
      ++ "case "
      ++ ( if length on < 2
             then concat on
             else
               putParens True (intercalate ", " on)
         )
      ++ " of\n"
      ++ indent True (ind + 1)
      ++ intercalate
        ("\n" ++ indent True (ind + 1))
        (map (\(xs, tm) -> (if length xs < 2 then concat xs else putParens True (intercalate "," xs)) ++ " => " ++ tm) cases)
uTmDo (ITmDoPure tm) = do
  (ind, t) <- get
  put (ind, False)
  tm' <- uTm True tm
  put (ind, t)
  pure $ indent t ind ++ "pure " ++ tm'
uTmDo (ITmDoIf c th e) = do
  (ind, t) <- get
  put (ind, False)
  c' <- uTm False c
  put (ind + 1, True)
  t' <- uTm False th
  put (ind + 1, True)
  e' <- uTm False e
  put (ind, False)
  pure $ indent t ind ++ "if " ++ c' ++ " then\n" ++ t' ++ " else\n" ++ e'
uTmDo (ITmDoTm tm) = do
  (ind, t) <- get
  put (ind, False)
  tm' <- uTm False tm
  put (ind, t)
  pure $ indent t ind ++ tm'

uFuncs :: IFunc -> Indent String
uFuncs IFunc {iFuncName, iFuncRetTy, iFuncArgs, iFuncBody, iWhere} = do
  (ind, t) <- get
  put (ind, False)
  retty <- uTy False iFuncRetTy
  args <- mapM (uAnnParam True) iFuncArgs
  -- put (ind + 1, True)
  bodies <- mapM (\(l, body) -> (,) <$> uTm False l <*> (put (ind + 1, True) >> uTm False body)) iFuncBody
  put (ind, False)
  deps <-
    mapM
      ( \i -> do
          (ind, t) <- get
          put (ind + 1, True)
          uTm False i
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
      ++ intercalate "\n" (map (\(l, body) -> l ++ " = \n" ++ body) bodies)
      ++ if null deps
        then ""
        else
          indent t ind
            ++ "\nwhere \n"
            ++ indent t (ind + 1)
            ++ intercalate "\n" deps

uImplementation :: IImplementation -> Indent String
uImplementation Impl {iImplicits, iConstraints, iSubject, iBody} = do
  (ind, t) <- get
  put (ind, False)
  implicits <- mapM (uAnnParam True) iImplicits
  constraints <- mapM (uTm False) iConstraints
  subject <- uTm True iSubject
  put (ind + 1, True)
  body <- mapM uImplCase iBody
  pure $
    indent t ind
      ++ concat implicits
      ++ intercalate " => " constraints
      ++ (if not (null constraints) then " => " else "")
      ++ "DecEq "
      ++ subject
      ++ " where \n"
      ++ intercalate "\n" body

doWith :: Maybe String -> String
doWith Nothing = ""
doWith (Just s) = " with " ++ s ++ "\n"

uImplCase :: IImplCase -> Indent String
uImplCase IImplCase {iArgs, iBarArgs, iWith, iCaseBody} = do
  (ind, t) <- get
  put (ind, False)
  t1 <- uTm True (fst iArgs)
  t2 <- uTm True (snd iArgs)
  barArgs <- mapM (uTm False) iBarArgs
  let barArgs' = concatMap (" | " ++) barArgs
  w <- mapM (uTm True) iWith
  let w' = doWith w
  body <- uImplCaseBody iCaseBody
  (ind, t) <- get
  pure $
    indent True ind ++ "decEq " ++ t1 ++ " " ++ t2 ++ barArgs' ++ (if null barArgs' then "" else " ") ++ w' ++ body

uImplCaseBody :: IImplCaseBody -> Indent String
uImplCaseBody (Tm tm) = do
  (ind, t) <- get
  put (ind, False)
  tm' <- uTm False tm
  put (ind, t)
  pure $ " = " ++ tm'
uImplCaseBody (Nest tms) = do
  (ind, t) <- get
  put (ind + 1, True)
  tms <- mapM uImplCase tms
  put (ind, True)
  pure $ intercalate "\n" tms

putParens :: Bool -> String -> String
putParens b s = if b then "(" ++ s ++ ")" else s