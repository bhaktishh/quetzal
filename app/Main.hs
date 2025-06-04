{-# LANGUAGE NamedFieldPuns #-}


module Main (main) where

import Lib
import Data.Void (Void)
import Text.Megaparsec ( (<|>), runParser, many, some, Parsec, MonadParsec(try, eof), parse, sepBy )
import Data.Functor (($>))
import Data.Char (digitToInt)
import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space, digitChar)

type List a = [a]

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

-- how do i add parsing for terms that have user defined types ... must i parse the types first and then the terms

{-

type Vect<Nat n, Ty T> {
    constructor Nil () of Vect<0,T>;
    constructor Cons (T head, Vect<n, T> tail) of Vect<n+1, T>;
}

func append<Nat n, Nat m, Ty T> (Vect<n,T> v1, Vect<m,T> v2) of Vect<n+m, T> {
    switch (v1, v2) {
        case (Nil, v2) {
            return v2;
        }
        case (Cons x xs, v2) {
            v2 = append xs v2;
            return Cons x v2;
        }
    }
}

func test<>() {} of Void


func replicate<Ty T> (T a, Nat n) of Vect<n,T> {
    switch(n) {
        case (0) {;}
        case (1) {;}
    }
}

func replicate<Ty T> (T a, Nat n) of Vect<n,T> {
    switch(n) {
        case (0) {return Nil;}
        case (S n) {return Cons x (repl x n);}

    }
}
-}


main :: IO ()
main = someFunc

data Ty = TyNat 
        | TyTy 
        | TyVoid
        | TyVar String
        | TyCustom {
            tyName :: String, 
            tyParams :: List Tm
        } 
        deriving (Show, Eq)

data Tm = TmNat Int
        | TmPlus Tm Tm 
        | TmVar String
        | TmTy Ty 
        | TmApp Tm Tm 
        | TmTyVar String 
        deriving (Show, Eq)

data Prog = Prog {
    types :: List TyDecl, 
    funcs :: List Func
} 
    deriving (Show, Eq)

data Func = Func {
    funcName :: String, 
    funcRetType :: Ty, 
    funcErasedArgs :: List (Ty, String),
    funcArgs :: List (Ty, String),
    funcBody :: List Stmt
}
    deriving (Show, Eq)

data TyDecl = TyDecl {
    tyDeclName :: String, 
    tyDeclParams :: List (Ty, String), 
    tyDeclConstructors :: List Constructor
}
    deriving (Show, Eq)

data Constructor = Constructor {
    conName :: String, 
    conArgs :: List (Ty, String), 
    conTy :: Ty
}
    deriving (Show, Eq)

data Stmt = Assign String Stmt
        | Decl Ty String 
        | DeclAssign Ty String Stmt 
        | Return Tm
        | Blank
        | Switch {
            switchOn :: List Tm,
            cases :: List Case
        }
        deriving (Show, Eq)

data Case = Case {
    caseOn :: List Tm, 
    caseBody :: List Stmt
}
    deriving (Show, Eq)

type Parser = Parsec Void String

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of 
        Left _ -> undefined 
        Right tm -> tm  

pProg :: Parser Prog
pProg = do 
    types <- many $ pSpaces pTyDecl 
    funcs <- many $ pSpaces pFunc
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

pPlusTm :: Parser Tm 
pPlusTm = do 
    x <- pSpaces pTm1
    _ <- char '+'
    y <- pSpaces pTm
    pure $ TmPlus x y

pTm :: Parser Tm 
pTm = try pPlusTm <|> pTm1

pTm1 :: Parser Tm 
pTm1 = try (pParens pTm) <|> pVarTm <|> pTyVarTm <|> pNat

pTyCustom :: Parser Ty 
pTyCustom = do
    tyName <- pSpaces $ pUpperString 
    (_, tyParams, _) <- pSpaces $ (, ,) <$> try (char '<') <*> (pSpaces pTm) `sepBy` char ',' <*> try (char '>')
    pure $ TyCustom {
        tyName, tyParams
    }

pNat :: Parser Tm 
pNat = do
    nums <- some digitChar
    pure $ TmNat ((read :: String -> Int) nums)

pTyNat :: Parser Ty 
pTyNat = string "Nat" >> pure TyNat 

pTyTy :: Parser Ty 
pTyTy = string "Ty" >> pure TyTy

pTyVoid :: Parser Ty
pTyVoid = string "Void" >> pure TyVoid 

pTy :: Parser Ty 
pTy = try pTyCustom <|> pTyNat <|> pTyTy <|> pTyVoid <|> pTyVarTy 

-- type declarations 
pTyDeclConstructor :: Parser Constructor
pTyDeclConstructor = do
    _ <- pSpaces $ string "constructor"
    conName <- pSpaces $ pUpperString 
    conArgs <- pSpaces $ pConArgs
    _ <- pSpaces $ string "of"
    conTy <- pSpaces $ pTy
    _ <- pSpaces pSemicolon
    pure $ Constructor {
        conName, conArgs, conTy
    }

pConArgs :: Parser [(Ty, String)]
pConArgs = do 
    _ <- pSpaces $ char '('
    ls <- pFuncArgs
    _ <- pSpaces $ char ')'
    pure ls 

pTyDecl :: Parser TyDecl
pTyDecl = do 
    _ <- pSpaces $ string "type"
    tyDeclName <- pSpaces pUpperString
    _ <- pSpaces $ char '<'
    tyDeclParams <- pSpaces pFuncArgs 
    _ <- pSpaces $ char '>'
    _ <- pSpaces $ char '{'
    tyDeclConstructors <- pSpaces $ many pTyDeclConstructor
    _ <- pSpaces $ char '}'
    pure $ TyDecl {
        tyDeclName, tyDeclParams, tyDeclConstructors
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
    funcBody <- many pStmt
    pure $ Func {
        funcName, funcRetType, funcErasedArgs, funcArgs, funcBody
    }

pFuncArgs :: Parser (List (Ty, String))
pFuncArgs = (pSpaces 
            ((,) <$> 
                pSpaces pTy <*> 
                pSpaces (pVar <|> pTyVar))) 
            `sepBy` char ',' 


-- statements 

pStmt :: Parser Stmt
pStmt = pSpaces $ 
        pSwitch <|> 
        try pDecl <|> pDeclAssign <|> try pAssign <|>
        pReturn <|> pBlank

pBlank :: Parser Stmt 
pBlank = char ';' >> pure Blank

pSwitch :: Parser Stmt 
pSwitch = do 
    _ <- pSpaces $ string "switch"
    _ <- pSpaces $ char '('
    switchOn <- (pSpaces pTm) `sepBy` char ','
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
    caseOn <- (pSpaces pTm) `sepBy` char ','
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
    _ <- pSemicolon
    pure $ Return tm 

pAssign :: Parser Stmt 
pAssign = do 
    var <- pSpaces pLowerString
    _ <- pSpaces $ char '='
    rhs <- pSpaces pStmt 
    _ <- pSpaces pSemicolon
    pure $ Assign var rhs 


pDecl :: Parser Stmt 
pDecl = do 
    ty <- pSpaces pTy 
    var <- pSpaces pLowerString
    _ <- pSpaces pSemicolon
    pure $ Decl ty var

pDeclAssign :: Parser Stmt 
pDeclAssign = do 
    ty <- pSpaces pTy 
    var <- pSpaces pLowerString 
    _ <- pSpaces $ char '='
    rhs <- pSpaces pStmt
    _ <- pSpaces pSemicolon
    pure $ DeclAssign  ty var rhs 

-- parsing utils 
parseFromFile p file = runParser p file <$> readFile file

