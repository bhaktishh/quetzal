{-# LANGUAGE NamedFieldPuns #-}


module Main where

import Lib
import FirstTypes
import Data.Void (Void)
import Text.Megaparsec ( (<|>), runParser, many, some, Parsec, MonadParsec(try, eof), parse, sepBy )
import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space, digitChar)
import qualified Data.Map as M
import GHC.TypeLits (Nat)
import Data.Tuple (swap)
import Data.List (unsnoc)
import ToIdris

-- TODO: change many, some, satisfy to takeWhileP and takeWhile1P for efficiency
-- is there a way i can add a list of variables and types to carry around? or should that be a second pass
-- how many passes is too many passes 
-- also shouldn't idris handle all that 
-- maybe idris shouldn't maybe this should have a dependent typechecker of its own 
-- maybe the goal is efficiency and i can do the custom data representation stuff 

-- variables must begin with a lowercase letter
-- type metavariables must be all uppercase
-- type names and type constructor names must begin with an uppercase letter 
-- non parameterized types must include "<>"

-- TODO: remove unnecessary {}, (), <>, of Void ... eg Nil() 
-- TODO: deal with semicolons right 


main :: IO ()
main = someFunc

type Parser = Parsec Void String

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of 
        Left _ -> undefined 
        Right tm -> tm  

pTLDecl :: Parser Decl 
pTLDecl = (Ty <$> pTyDecl) <|> (Rec <$> pRecDecl)

pProg :: Parser Prog
pProg = do 
    types <- many $ pSpaces pTLDecl 
    funcs <- many $ pSpaces pFunc
    _ <- eof
    pure $ Prog {
        types, funcs
    }

pSpaces :: Parser a -> Parser a 
pSpaces p = space *> p <* space

pParens :: Parser a -> Parser a
pParens p = do 
    _ <- pSpaces $ char '('
    x <- p
    _ <- pSpaces $ char ')' 
    pure x 

pSemicolon :: Parser Char
pSemicolon = char ';'

pLowerString :: Parser String
pLowerString = (:) <$> lowerChar <*> many alphaNumChar

pUpperString :: Parser String 
pUpperString = (:) <$> upperChar <*> many alphaNumChar

pTyVar :: Parser String 
pTyVar = some upperChar

pVar :: Parser String 
pVar = pLowerString

pVarTm :: Parser Tm
pVarTm = TmVar <$> pVar

pTyVarTm :: Parser Tm
pTyVarTm = TmTyVar <$> pTyVar

pTyVarTy :: Parser Ty 
pTyVarTy = TyVar <$> pTyVar 

pTyFunctionCall :: Parser Ty
pTyFunctionCall = do 
    name <- pSpaces $ pTyVar <|> pVar 
    _ <- pSpaces $ char '('
    args <- pSpaces $ pTm `sepBy` char ','
    _ <- pSpaces $ char ')'
    pure $ TyFunctionCall name args 

pPlusTm :: Parser Tm 
pPlusTm = do 
    x <- pSpaces pTm1
    _ <- char '+'
    y <- pSpaces pTm
    pure $ TmPlus x y

pTm :: Parser Tm 
pTm = try pPlusTm <|> try pFunctionCall <|> try pConTm <|> pTm1

pTm1 :: Parser Tm 
pTm1 = try (pParens pTm) <|> try pVarTm <|> pTyVarTm <|> pNat <|> pBool

pTyCustom :: Parser Ty 
pTyCustom = do
    tyName <- pSpaces pUpperString 
    _ <- pSpaces $ char '<'
    tyErasedParams <- pSpaces pTm `sepBy` char ','
    _ <- pSpaces $ char '>'
    _ <- pSpaces $ char '('
    tyParams <- pSpaces pTm `sepBy` char ','
    _ <- pSpaces $ char ')'
    pure $ TyCustom {
        tyName, tyErasedParams, tyParams
    }

pTyBool :: Parser Ty 
pTyBool = string "Bool" >> pure TyBool 

pBool :: Parser Tm 
pBool = pTrue <|> pFalse 

pTrue :: Parser Tm 
pTrue = string "True" >> pure (TmBool True)

pFalse :: Parser Tm 
pFalse = string "False" >> pure (TmBool False)

pNat :: Parser Tm 
pNat = do
    nums <- some digitChar
    pure $ TmNat ((read :: String -> Nat) nums)

pTyNat :: Parser Ty 
pTyNat = string "Nat" >> pure TyNat 

pTyTy :: Parser Ty 
pTyTy = string "Ty" >> pure TyTy

pTyVoid :: Parser Ty
pTyVoid = string "Void" >> pure TyVoid 

pTyFunc :: Parser Ty
pTyFunc = do 
    _ <- pSpaces $ string "Func"
    _ <- pSpaces $ char '('
    tyFuncArgs <- pFuncArgs 
    _ <- pSpaces $ string "=>"
    tyFuncRetTy <- pSpaces pTy
    _ <- pSpaces $ char ')'
    pure $ TyFunc {
        tyFuncArgs, tyFuncRetTy
    }

pTy :: Parser Ty 
pTy = try pTyCustom <|> try pTyFunc <|> try pTyFunctionCall <|> pTyNat <|> pTyBool <|> pTyTy <|> pTyVoid <|> pTyVarTy 

-- type declarations 
pTyDeclConstructor :: Parser Constructor
pTyDeclConstructor = do
    _ <- pSpaces $ string "constructor"
    conName <- pSpaces pUpperString
    conErasedArgs <- pSpaces pConErasedArgs
    conArgs <- pSpaces pConArgs
    _ <- pSpaces $ string "of"
    conTy <- pSpaces pTy
    _ <- pSpaces pSemicolon
    pure $ Constructor {
        conName, conErasedArgs, conArgs, conTy
    }

pConErasedArgs :: Parser [(Ty, String)]
pConErasedArgs = do 
    _ <- pSpaces $ char '<'
    ls <- pFuncArgs
    _ <- pSpaces $ char '>'
    pure ls 

pConArgs :: Parser [(Ty, String)]
pConArgs = do 
    _ <- pSpaces $ char '('
    ls <- pFuncArgs
    _ <- pSpaces $ char ')'
    pure ls 

pRecDecl :: Parser RecDecl 
pRecDecl = do 
    _ <- pSpaces $ string "record"
    recDeclName <- pSpaces pUpperString
    _ <- pSpaces $ char '<'
    recDeclErasedParams <- pSpaces pFuncArgs
    _ <- pSpaces $ char '>'
    _ <- pSpaces $ char '('
    recDeclParams <- pSpaces pFuncArgs
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ char '{'
    recDeclFields <- pSpaces $ many pRecDeclField
    _ <- pSpaces $ char '}'
    pure $ RecDecl {
        recDeclName, recDeclErasedParams, recDeclParams, recDeclFields
    }

pRecDeclField :: Parser (Ty, String)
pRecDeclField = do
    ty <- pSpaces pTy 
    var <- pSpaces pVar
    _ <- pSpaces pSemicolon
    pure (ty, var)

pTyDecl :: Parser TyDecl
pTyDecl = do 
    _ <- pSpaces $ string "type"
    tyDeclName <- pSpaces pUpperString
    _ <- pSpaces $ char '<'
    tyDeclErasedParams <- pSpaces pFuncArgs
    _ <- pSpaces $ char '>'
    _ <- pSpaces $ char '('
    tyDeclParams <- pSpaces pFuncArgs
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ char '{'
    tyDeclConstructors <- pSpaces $ many pTyDeclConstructor
    _ <- pSpaces $ char '}'
    pure $ TyDecl {
        tyDeclName, tyDeclErasedParams, tyDeclParams, tyDeclConstructors
    }

-- function definitions 

pFunc :: Parser Func 
pFunc = do 
    _ <- pSpaces $ string "func"
    funcName <- pSpaces pLowerString
    _ <- pSpaces $ char '<'
    funcErasedArgs <- pSpaces pFuncArgs
    _ <- pSpaces $ char '>'
    _ <- pSpaces $ char '('
    funcArgs <- pSpaces pFuncArgs
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ string "of"
    funcRetType <- pSpaces pTy 
    _ <- pSpaces $ char '{'
    body <- pSpaces $ many pStmt
    let funcBody = unsnoc body
    _ <- pSpaces $ char '}'
    pure $ Func {
        funcName, funcRetType, funcErasedArgs, funcArgs, funcBody
    }

pFuncArgs :: Parser (List (Ty, String))
pFuncArgs = pSpaces 
            ((,) <$> 
                pSpaces pTy <*> 
                pSpaces (pVar <|> pTyVar))
            `sepBy` char ',' 


-- statements 

pStmt :: Parser Stmt
pStmt = pSpaces $ 
        (try pDeclAssign <|>
        try pDecl <|>
        try pAssign <|> 
        try pSwitch <|> 
        -- pFunctionCall <|> TODO 
         pReturn) <* pSemicolon
        <|> pIf
        <|> pWhile
         <|> pBlank

pBlank :: Parser Stmt 
pBlank = char ';' >> pure Blank

pSwitch :: Parser Stmt 
pSwitch = do 
    _ <- pSpaces $ string "switch"
    _ <- pSpaces $ char '('
    switchOn <- pSpaces pTm `sepBy` char ','
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ char '{'
    cases <- some $ pSpaces pCase
    _ <- pSpaces $ char '}'
    pure $ Switch {
        switchOn, cases
    }

pCase :: Parser Case 
pCase = do 
    _ <- pSpaces $ string "case"
    _ <- pSpaces $ char '('
    caseOn <- pSpaces pTm `sepBy` char ','
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ char '{'
    caseBody <- many $ pSpaces pStmt
    _ <- pSpaces $ char '}'
    pure $ Case {
        caseOn, caseBody
    }

pReturn :: Parser Stmt 
pReturn = do 
    _ <- pSpaces $ string "return"
    tm <- pSpaces pTm
    pure $ Return tm 

pAssign :: Parser Stmt 
pAssign = do 
    var <- pSpaces pLowerString
    _ <- pSpaces $ char '='
    rhs <- pSpaces pTm 
    pure $ Assign var rhs 


pDecl :: Parser Stmt 
pDecl = do 
    ty <- pSpaces pTy 
    var <- pSpaces pLowerString
    pure $ Decl ty var

pDeclAssign :: Parser Stmt 
pDeclAssign = do 
    ty <- pSpaces pTy 
    var <- pSpaces pLowerString 
    _ <- pSpaces $ char '='
    rhs <- pSpaces pTm
    pure $ DeclAssign  ty var rhs 

pFunctionCall :: Parser Tm 
pFunctionCall = do
    name <- pSpaces pLowerString 
    _ <- pSpaces $ char '('
    args <- pSpaces pTm `sepBy` char ','
    _ <- pSpaces $ char ')'
    pure $ TmFunctionCall name args

pConTm :: Parser Tm 
pConTm = do
    name <- pSpaces pUpperString 
    _ <- pSpaces $ char '('
    args <- pSpaces pTm `sepBy` char ','
    _ <- pSpaces $ char ')'
    pure $ TmCon name args

pWhile :: Parser Stmt 
pWhile = do 
    _ <- pSpaces $ string "while" 
    _ <- pSpaces $ char '('
    condition <- pSpaces pTm 
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ char '{'
    body <- many $ pSpaces pStmt
    _ <- pSpaces $ char '}'
    pure $ While {
        condition, body
    }

pIf :: Parser Stmt 
pIf = do 
    _ <- pSpaces $ string "if"
    _ <- pSpaces $ char '('
    cond <- pSpaces pTm
    _ <- pSpaces $ char ')'
    _ <- pSpaces $ char '{'
    thenCase <- many $ pSpaces pStmt 
    _ <- pSpaces $ char '}'
    _ <- pSpaces $ string "else"
    _ <- pSpaces $ char '{'
    elseCase <- many $ pSpaces pStmt 
    _ <- pSpaces $ char '}'
    pure $ If {
        cond, thenCase, elseCase
    }
 
-- parsing utils 
parseFromFile p file = runParser p file <$> readFile file

combine :: Maybe ([Stmt], Stmt) -> List Stmt 
combine Nothing = []
combine (Just (xs, x)) = xs ++ [x]

doShadowing :: Func -> Func 
doShadowing f = let stmts = funcBody f in 
    f { funcBody = unsnoc $ doStmts (M.fromList (map swap (funcArgs f))) (combine stmts) }

doStmts :: M.Map String Ty -> List Stmt -> List Stmt
doStmts _ [] = []
doStmts vars (x:xs) = case x of 
    Assign var tm -> case M.lookup var vars of 
        Nothing -> error "assign before declare" 
        Just ty -> DeclAssign ty var tm : doStmts vars xs
    Decl ty var -> Decl ty var : doStmts (M.insert var ty vars) xs
    DeclAssign ty var tm -> DeclAssign ty var tm : doStmts (M.insert var ty vars) xs
    Switch { switchOn, cases } -> Switch {
        switchOn,
        cases = map (\y -> y {caseBody = doStmts vars (caseBody y)}) cases
    } : doStmts vars xs
    _ -> x : doStmts vars xs 

{-
foo_iterative(params){
    header
    while(condition){
        loop_body
    }
    return tail
}

foo_recursive(params){
    header
    return foo_recursion(params, header_vars)
}

foo_recursion(params, header_vars){
    if(!condition){
        return tail
    }

    loop_body
    return foo_recursion(params, modified_header_vars)
}
-}
unLoop :: Func -> List Func 
unLoop Func { funcName, funcRetType, funcErasedArgs, funcArgs, funcBody} = undefined  

unSwitch :: Func -> Func 
unSwitch f = undefined 

process :: String -> Prog 
process x = case parse pProg "" x of 
        Left _ -> error "bruh"
        Right tm -> tm { funcs = map doShadowing (funcs tm) }

processFile :: String -> IO Prog 
processFile file = do 
    x <- readFile file
    pure $ process x 

writeIdris :: Prog -> String -> IO ()
writeIdris p fpath = writeFile fpath (uProg p)