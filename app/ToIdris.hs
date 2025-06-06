
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
        funcErasedArgs, funcArgs, funcBody } = undefined 

    uTypes :: Decl -> String 
    uTypes (Ty tdecl) = uTyDecl tdecl
    uTypes (Rec recdecl) = uRecDecl recdecl 

    uTyDecl :: TyDecl -> String 
    uTyDecl TyDecl {tyDeclName, tyDeclErasedParams, 
        tyDeclParams, tyDeclConstructors} = 
            "data" ++ " " ++ tyDeclName ++ " : " 
            ++ (concatMap uTyDeclParam tyDeclErasedParams) ++
            (concatMap uTyDeclParam tyDeclParams) ++ "Type where \n" ++
            concatMap uTyDeclConstructor tyDeclConstructors

    uTyDeclConstructor :: Constructor -> String 
    uTyDeclConstructor Constructor {conName, conErasedArgs, conArgs, conTy} =
        conName ++ " : " ++ (concatMap uTyDeclParam conErasedArgs) ++
        (concatMap uTyDeclParam conArgs) ++ uTy conTy ++ "\n"

    uTyDeclParam :: (Ty, String) -> String 
    uTyDeclParam (ty, var) = "(" ++ (map toLower var) ++ " : " ++ uTy ty ++ ")" ++ " -> "

    uRecDecl :: RecDecl -> String 
    uRecDecl RecDecl {recDeclName, recDeclErasedParams, 
        recDeclParams, recDeclFields} = undefined 

    uTy :: Ty -> String 
    uTy TyNat = "Nat" 
    uTy TyTy = "Type"
    uTy TyVoid = "()"
    uTy (TyVar s) = map toLower s
    uTy (TyFunctionCall f args) = undefined 
    uTy (TyCustom {tyName, tyErasedParams, tyParams}) = tyName ++ " " ++ (concatMap uTm tyErasedParams) ++ " " ++ (concatMap uTm tyParams)
    uTy (TyFunc {tyFuncArgs, tyFuncRetTy}) = undefined

    uTm :: Tm -> String 
    uTm (TmNat n) = show n 
    uTm (TmPlus n1 n2) = "(" ++ uTm n1 ++ " + " ++ uTm n2 ++ ")"
    uTm (TmVar v) = v
    uTm (TmTyVar v) = map toLower v 
    uTm (TmFunctionCall f args) = undefined 
    uTm (TmCon c args) = c ++ " " ++ concat (intersperse " " (map uTm args))