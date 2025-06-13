{-# LANGUAGE NamedFieldPuns #-}

module ToIdris where

import Control.Monad.State.Lazy
import Data.Char (toLower)
import Data.List (intercalate, intersperse)
import Types

type Indent a = State (Int, Bool) a

uProg :: Prog -> Indent String
uProg [] = pure ""
uProg (x : xs) = case x of
  PDecl decl -> do
    dec <- uTypes decl
    prog <- uProg xs
    pure $ dec ++ "\n\n" ++ prog
  PFunc func -> do
    f <- uFuncs func
    pr <- uProg xs
    pure $ f ++ "\n\n" ++ pr

uFuncs :: Func -> Indent String
uFuncs
  Func
    { funcName,
      funcRetTy,
      funcArgs,
      funcBody
    } = do
    retty <- uTy funcRetTy
    args <- mapM (uAnnParam True) funcArgs
    body <- uTm funcBody
    pure $
      funcName
        ++ " : "
        ++ concat args
        ++ retty
        ++ "\n"
        ++ funcName
        ++ " "
        ++ unwords (map (\(AnnParam (_, v) _) -> v) (filter (\(AnnParam (_, _) vis) -> vis) funcArgs))
        ++ " = "
        ++ body

uTypes :: Decl -> Indent String
uTypes (Ty tdecl) = uTyDecl tdecl
uTypes (Rec recdecl) = uRecDecl recdecl

uTyDecl :: TyDecl -> Indent String
uTyDecl
  TyDecl
    { tyDeclName,
      tyDeclParams,
      tyDeclConstructors
    } = do
    params <- mapM (uAnnParam True) tyDeclParams
    constructors <- mapM uTyDeclConstructor tyDeclConstructors
    pure $
      "data"
        ++ " "
        ++ tyDeclName
        ++ " : "
        ++ concat params
        ++ "Type where \n"
        ++ concat constructors

uTyDeclConstructor :: Constructor -> Indent String
uTyDeclConstructor Constructor {conName, conArgs, conTy} =
  do
    params <- mapM (uAnnParam True) conArgs
    ty <- uTy conTy
    pure $
      "\t"
        ++ conName
        ++ " : "
        ++ concat params
        ++ ty
        ++ "\n"

uAnnParam :: Bool -> AnnParam -> Indent String
uAnnParam arrow (AnnParam (ty, var) vis) = do
  t <- uTy ty
  pure $ (if vis then "(" else "{") ++ var ++ " : " ++ t ++ (if vis then ")" else "}") ++ (if arrow then " -> " else " ")

uTyDeclParam :: (Ty, String) -> Indent String
uTyDeclParam (ty, var) = do
  t <- uTy ty
  pure $ "(" ++ var ++ " : " ++ t ++ ")" ++ " -> "

uRecDecl :: RecDecl -> Indent String
uRecDecl
  RecDecl
    { recDeclName,
      recDeclParams,
      recDeclFields
    } =
    do
      params <- mapM (uAnnParam False) recDeclParams
      fields <- mapM uRecDeclField recDeclFields
      pure $
        "record"
          ++ " "
          ++ recDeclName
          ++ " "
          ++ concat params
          ++ "where \n"
          ++ "\tconstructor Mk"
          ++ recDeclName
          ++ "\n"
          ++ concat fields

uRecDeclField :: (Ty, String) -> Indent String
uRecDeclField (ty, var) = do
  t <- uTy ty
  pure $ "\t" ++ var ++ " : " ++ t ++ "\n"

uTy :: Ty -> Indent String
uTy TyNat = pure "Nat"
uTy TyBool = pure "Bool"
uTy TyTy = pure "Type"
uTy TyUnit = pure "()"
uTy (TyCustom {tyName, tyParams}) = do
  params <- mapM uTm tyParams
  pure $ tyName ++ " " ++ unwords params
uTy (TyFunc {tyFuncArgs, tyFuncRetTy}) = do
  params <- mapM uTyDeclParam tyFuncArgs
  t <- uTy tyFuncRetTy
  pure $ "(" ++ concat params ++ t ++ ")"
uTy (TyTm t) = uTm t

uTm :: Tm -> Indent String
uTm (TmNat n) = pure $ show n
uTm (TmBool b) = pure $ show b
uTm (TmPlus n1 n2) = do
  t1 <- uTm n1
  t2 <- uTm n2
  pure $ "(" ++ (if n1 == TmNat 1 then "S " else t1 ++ " + ") ++ t2 ++ ")"
uTm (TmVar v) = do
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ v
uTm (TmFuncCall f args) = do
  (ind, t) <- get
  tm <- uTm f
  args <- mapM uTm args
  put (ind, False)
  pure $ indent t ind ++ "(" ++ tm ++ (if null args then "" else " ") ++ unwords args ++ ")"
uTm (TmCon c args) = do
  args <- mapM uTm args
  (ind, t) <- get
  put (ind, False)
  pure $ indent t ind ++ c ++ (if null args then "" else " ") ++ unwords args
uTm (TmReturn tm) = uTm tm
uTm (TmSwitch s) = uSwitch s
uTm (TmIf cond thenCase elseCase) = error "TODO"
uTm TmUnit = pure "()"
uTm (TmTy t) = uTy t
uTm (TmFunc f) = uFuncs f
uTm (TmBlock stmts tm) = do
  (ind, t) <- get
  put (ind, False)
  stmts <- mapM uStmt stmts
  tm <- uTm tm
  pure $ indent t ind ++ concat stmts ++ tm
uTm (TmNot tm) = do 
  t <- uTm tm
  pure $ "not " ++ t

uStmt :: Stmt -> Indent String
uStmt (Assign v tm) = do
  tm <- uTm tm
  (ind, t) <- get
  _ <- put (ind + 1, True)
  pure $ indent t ind ++ "let " ++ v ++ " = " ++ tm ++ " in\n"
uStmt (DeclAssign ty v tm) = do
  ty <- uTy ty
  tm <- uTm tm
  (ind, t) <- get
  put (ind + 1, True)
  pure $ indent t ind ++ "let " ++ v ++ " : " ++ ty ++ " = " ++ tm ++ " in\n"
uStmt _ = error "should have been transformed bruh"

uSwitch :: Switch -> Indent String
uSwitch (Switch {switchOn, cases}) = do
  (ind, t) <- get
  switchOn <- mapM uTm switchOn
  put (ind + 1, True)
  cases <- mapM uCase cases
  put (ind - 1, False)
  pure $ indent t ind ++ "case (" ++ intercalate "," switchOn ++ ") of\n" ++ concat cases

uCase :: Case -> Indent String
uCase (Case {caseOn, caseBody}) = do
  (ind, t) <- get
  put (ind, False)
  caseOn <- mapM uTm caseOn
  caseBody <- uTm caseBody
  put (ind, True)
  pure $ indent t ind ++ "(" ++ intercalate "," caseOn ++ ") => " ++ caseBody ++ "\n"

indent :: Bool -> Int -> String
indent b n = if b then replicate n '\t' else ""
