{-# LANGUAGE NamedFieldPuns #-}

module Main (main) where

import Lib
import Data.Void (Void)
import Text.Megaparsec ( (<|>), many, some, Parsec, MonadParsec(try, eof), parse, sepBy )
import Data.Functor (($>))
import Data.Char (digitToInt)
import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space, digitChar)

type List a = [a]

-- variables must begin with a lowercase letter
-- type metavariables must be all uppercase
-- type names and type constructor names must begin with an uppercase letter 

main :: IO ()
main = someFunc

data Ty = TyNat 
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
    funcs :: List Func, 
    funcMain :: Func
} 
    deriving (Show, Eq)

data Func = Func {
    funName :: String, 
    funRetType :: Ty, 
    funArgs :: List (String, Ty), -- should be dependent
    funBody :: List Stmt,
    funReturns :: Stmt
}
    deriving (Show, Eq)

data TyDecl = TyDecl {
    tyDeclName :: String, 
    tyDeclParams :: List TyParam, 
    tyDeclConstructors :: List Constructor
}
    deriving (Show, Eq)

data TyParam = TmParam String Ty 
            | TyParam String
    deriving (Show, Eq)

data Constructor = Constructor {
    conName :: String, 
    conArgs :: List (Ty, String), 
    conTy :: Ty
}
    deriving (Show, Eq)

data Stmt = Assignment String Stmt
        | Return Tm
        | Switch {
            switchOn :: Tm,
            cases :: List Case
        }
        deriving (Show, Eq)

data Case = Case {
    caseOn :: Tm, 
    caseBody :: List Stmt
}
    deriving (Show, Eq)

type Parser = Parsec Void String

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of 
        Left _ -> undefined 
        Right tm -> tm  

pProg :: Parser Prog
pProg = undefined

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

pTyParam :: Parser TyParam
pTyParam = undefined 

pLowerString :: Parser String
pLowerString = (:) <$> lowerChar <*> many alphaNumChar

pUpperString :: Parser String 
pUpperString = (:) <$> upperChar <*> many alphaNumChar

pConArgs :: Parser [(Ty, String)]
pConArgs = do 
    _ <- pSpaces $ char '('
    ls <- (pSpaces ((,) <$> pSpaces pTy <*> pSpaces pVar)) `sepBy` char ',' 
    _ <- pSpaces $ char ')'
    pure ls 

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
    nums <- many digitChar
    pure $ TmNat ((read :: String -> Int) nums)

pTyNat :: Parser Ty 
pTyNat = string "Nat" >> pure TyNat 

pTy :: Parser Ty 
pTy = try pTyCustom <|> pTyNat <|> pTyVarTy

pTyDeclConstructor :: Parser Constructor
pTyDeclConstructor = do
    _ <- pSpaces $ string "constructor"
    conName <- pSpaces $ pUpperString 
    conArgs <- pSpaces $ pConArgs
    _ <- pSpaces $ string "of"
    conTy <- pSpaces $ pTy
    _ <- pSemicolon
    pure $ Constructor {
        conName, conArgs, conTy
    }

pTyDecl :: Parser TyDecl
pTyDecl = do 
    _ <- pSpaces $ string "type"
    tyDeclName <- pSpaces pUpperString
    tyDeclParams <- pSpaces pTyDeclParams 
    _ <- pSpaces $ char '{'
    tyDeclConstructors <- pSpaces $ many pTyDeclConstructor
    _ <- pSpaces $ char '}'
    pure $ TyDecl {
        tyDeclName, tyDeclParams, tyDeclConstructors
    }