{-# LANGUAGE NamedFieldPuns #-}

module Main (main) where

import Lib
import Data.Void (Void)
import Text.Megaparsec ( (<|>), many, Parsec, MonadParsec(try, eof), parse, sepBy )
import Data.Functor (($>))
import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space)

type List a = [a]

-- variables must begin with a lowercase letter
-- type metavariables must be all uppercase
-- type names and type constructor names must begin with an uppercase letter 

main :: IO ()
main = someFunc

data Ty = TyNat 
        | TyFunc Ty Ty 
        | TyCustom {
            tyName :: String, 
            tyParams :: List Tm
        } 
        deriving (Show, Eq)

data Tm = TmNat Int
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
    conArgs :: List (String, Ty), 
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

pSemicolon :: Parser Char
pSemicolon = char ';'

pTyDecl :: Parser TyDecl
pTyDecl = undefined

pTyDeclName :: Parser String 
pTyDeclName = undefined 

pTyParam :: Parser TyParam
pTyParam = undefined 

pLowerString :: Parser String
pLowerString = (:) <$> lowerChar <*> many alphaNumChar

pUpperString :: Parser String 
pUpperString = (:) <$> upperChar <*> many alphaNumChar

pConArgs :: Parser [(String, Ty)]
pConArgs = undefined 

pTyVar :: Parser String 
pTyVar = many upperChar

pVar :: Parser String 
pVar = pLowerString

pVarTm :: Parser Tm
pVarTm = TmVar <$> pVar

pTyVarTm :: Parser Tm
pTyVarTm = TmTyVar <$> pTyVar


pTm :: Parser Tm 
pTm = pVarTm <|> pTyVarTm

pTyCustom :: Parser Ty 
pTyCustom = do
    tyName <- pSpaces $ pUpperString 
    (_, tyParams, _) <- pSpaces $ (, ,) <$> try (char '<') <*> (pSpaces pTm) `sepBy` char ',' <*> try (char '>')
    pure $ TyCustom {
        tyName, tyParams
    }

pTy :: Parser Ty 
pTy = undefined

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