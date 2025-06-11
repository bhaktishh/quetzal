{-# LANGUAGE NamedFieldPuns #-}

module ToIdris where

import Data.Char (toLower)
import Data.List (intersperse)
import Types

uProg :: Prog -> String
uProg [] = ""
uProg (x:xs) = case x of
  PDecl decl -> uTypes decl ++ uProg xs
  PFunc func -> uFuncs func ++ uProg xs 

uFuncs :: Func -> String
uFuncs
  Func
    { funcName,
      funcRetTy,
      funcArgs,
      funcBody
    } =
    funcName
      ++ " : "
      ++ concatMap uAnnParam funcArgs
      ++ uTy funcRetTy
      ++ "\n"
      ++ funcName
      ++ " "
      ++ unwords (map (\(AnnParam (_, v) _) -> map toLower v) funcArgs)
      ++ " = "
      ++ uTm funcBody
      ++ "\n"


uTypes :: Decl -> String
uTypes (Ty tdecl) = uTyDecl tdecl
uTypes (Rec recdecl) = uRecDecl recdecl

uTyDecl :: TyDecl -> String
uTyDecl
  TyDecl
    { tyDeclName,
      tyDeclParams,
      tyDeclConstructors
    } =
    "data"
      ++ " "
      ++ tyDeclName
      ++ " : "
      ++ concatMap uAnnParam tyDeclParams
      ++ "Type where \n"
      ++ concatMap uTyDeclConstructor tyDeclConstructors
      ++ "\n"

uTyDeclConstructor :: Constructor -> String
uTyDeclConstructor Constructor {conName, conArgs, conTy} =
  "\t"
    ++ conName
    ++ " : "
    ++ concatMap uAnnParam conArgs
    ++ uTy conTy
    ++ "\n"

uAnnParam :: AnnParam -> String
uAnnParam (AnnParam (ty, var) vis) = "(" ++ map toLower var ++ " : " ++ uTy ty ++ ")" ++ " -> "

uTyDeclParam :: (Ty, String) -> String
uTyDeclParam (ty, var) = "(" ++ map toLower var ++ " : " ++ uTy ty ++ ")" ++ " -> "


-- TODO 
uRecDecl :: RecDecl -> String
uRecDecl
  RecDecl
    { recDeclName,
      recDeclParams,
      recDeclFields
    } =
    "record"
      ++ " "
      ++ recDeclName
      ++ " "
      ++ "where \n"
      ++ concatMap uAnnParam recDeclParams
      ++ "\tconstructor Mk"
      ++ recDeclName
      ++ "\n"
      ++ concatMap uRecDeclField recDeclFields
      ++ "\n"

uRecDeclField :: (Ty, String) -> String
uRecDeclField (ty, var) = "\t" ++ var ++ " : " ++ uTy ty ++ "\n"

uTy :: Ty -> String
uTy TyNat = "Nat"
uTy TyBool = "Bool"
uTy TyTy = "Type"
uTy TyUnit = "()"
uTy (TyCustom {tyName, tyParams}) = tyName ++ " " ++ unwords (map uTm tyParams)
uTy (TyFunc {tyFuncArgs, tyFuncRetTy}) = "(" ++ concatMap uTyDeclParam tyFuncArgs ++ uTy tyFuncRetTy ++ ")"
uTy (TyTm t) = uTm t

uTm :: Tm -> String
uTm (TmNat n) = show n
uTm (TmBool b) = show b
uTm (TmPlus n1 n2) = "(" ++ uTm n1 ++ " + " ++ uTm n2 ++ ")"
uTm (TmVar v) = v
uTm (TmFuncCall f args) = uTm f ++ " " ++ unwords (map uTm args)
uTm (TmCon c args) = c ++ " " ++ unwords (map uTm args)
uTm (TmReturn tm) = uTm tm
uTm (TmSwitch {switchOn, cases}) = error "TODO"
uTm (TmIf cond thenCase elseCase) = error "TODO"
uTm TmUnit = "()"
uTm (TmTy t) = uTy t
uTm (TmFunc f) = uFuncs f 
uTm (TmBlock stmts tm) = concatMap uStmt stmts ++ uTm tm 


uStmt :: Stmt -> String
uStmt (Assign v tm) = "let " ++ v ++ " = " ++ uTm tm ++ " in\n\t"
uStmt (DeclAssign ty v tm) = "let " ++ v ++ " : " ++ uTy ty ++ " = " ++ uTm tm ++ " in\n\t"
uStmt _ = error "should have been transformed bruh"
