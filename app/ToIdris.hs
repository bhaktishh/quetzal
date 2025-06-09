
{-# LANGUAGE NamedFieldPuns #-}

module ToIdris where

    import FirstTypes
    import Data.Char (toLower)
    import Data.List (intersperse)

    uProg :: Prog -> String
    uProg Prog {types, funcs} =
        concatMap uTypes types ++ concatMap uFuncs funcs


    uFuncs :: Func -> String
    uFuncs Func {funcName, funcRetType,
        funcErasedArgs, funcArgs, funcBody } = 
            funcName ++ " : " ++ concatMap uTyDeclParam funcErasedArgs ++
            concatMap uTyDeclParam funcArgs ++ uTy funcRetType ++ "\n" ++ 
            " " 

    uTypes :: Decl -> String
    uTypes (Ty tdecl) = uTyDecl tdecl
    uTypes (Rec recdecl) = uRecDecl recdecl

    uTyDecl :: TyDecl -> String
    uTyDecl TyDecl {tyDeclName, tyDeclErasedParams,
        tyDeclParams, tyDeclConstructors} =
            "data" ++ " " ++ tyDeclName ++ " : "
            ++ concatMap uTyDeclParam tyDeclErasedParams ++
            concatMap uTyDeclParam tyDeclParams ++ "Type where \n" ++
            concatMap uTyDeclConstructor tyDeclConstructors ++ "\n"

    uTyDeclConstructor :: Constructor -> String
    uTyDeclConstructor Constructor {conName, conErasedArgs, conArgs, conTy} =
        "\t" ++ conName ++ " : " ++ concatMap uTyDeclParam conErasedArgs ++
        concatMap uTyDeclParam conArgs ++ uTy conTy ++ "\n"

    uTyDeclParam :: (Ty, String) -> String
    uTyDeclParam (ty, var) = "(" ++ map toLower var ++ " : " ++ uTy ty ++ ")" ++ " -> "

    uRecDecl :: RecDecl -> String
    uRecDecl RecDecl {recDeclName, recDeclErasedParams,
        recDeclParams, recDeclFields} = "record" ++ " " ++ recDeclName ++ " " ++
            concatMap uTyDeclParam recDeclErasedParams ++
            concatMap uTyDeclParam recDeclParams ++ "where \n" ++
            "\tconstructor Mk" ++ recDeclName ++ "\n" ++
            concatMap uRecDeclField recDeclFields ++ "\n" 

    uRecDeclField :: (Ty, String) -> String 
    uRecDeclField (ty, var) = "\t" ++ var ++ " : " ++ uTy ty ++ "\n"

    uTy :: Ty -> String
    uTy TyNat = "Nat"
    uTy TyBool = "Bool"
    uTy TyTy = "Type"
    uTy TyVoid = "()"
    uTy (TyVar s) = map toLower s
    uTy (TyFunctionCall f args) = f ++ " " ++ unwords (map uTm args)
    uTy (TyCustom {tyName, tyErasedParams, tyParams}) = tyName ++ " " ++ unwords (map uTm tyErasedParams) ++ " " ++ unwords (map uTm tyParams)
    uTy (TyFunc {tyFuncArgs, tyFuncRetTy}) = "(" ++ concatMap uTyDeclParam tyFuncArgs ++ uTy tyFuncRetTy ++ ")"

    uTm :: Tm -> String
    uTm (TmNat n) = show n
    uTm (TmBool b) = show b
    uTm (TmPlus n1 n2) = "(" ++ uTm n1 ++ " + " ++ uTm n2 ++ ")"
    uTm (TmVar v) = v
    uTm (TmTyVar v) = map toLower v
    uTm (TmFunctionCall f args) = f ++ " " ++ unwords (map uTm args)
    uTm (TmCon c args) = c ++ " " ++ unwords (map uTm args)

    uStmt :: Stmt -> String 
    uStmt (Assign v tm) = "let " ++ v ++ " = " ++ uTm tm ++ " in\n\t"
    uStmt (Decl ty str) = error "TODO"
    uStmt (DeclAssign ty v tm) =  "let " ++ v ++ " : " ++ uTy ty ++ " = " ++ uTm tm ++ " in\n\t"
    uStmt (Return tm) = uTm tm 
    uStmt Blank = "\n"
    uStmt (Switch {switchOn, cases}) = error "TODO"