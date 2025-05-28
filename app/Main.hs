{-# LANGUAGE NamedFieldPuns #-}
module Main (main) where

import Lib
import Data.Void (Void)
import Text.Megaparsec ( (<|>), many, Parsec, MonadParsec(try, eof), parse )
import Data.Functor (($>))
import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space)

type List a = [a]

main :: IO ()
main = someFunc

data Ty = TyNat 
        | TyFunc Ty Ty 
        | TyNew TyDecl 

data Tm = TmNat Int
        | TmVar String
        | TmTy Ty 
        | TmApp Tm Tm 

data Prog = Prog {
    types :: List TyDecl, 
    funcs :: List Func, 
    funcMain :: Func
} 

data Func = Func {
    funName :: String, 
    funRetType :: Ty, 
    funArgs :: List (String, Ty), -- should be dependent
    funBody :: List Stmt,
    funReturns :: Stmt
}

data TyDecl = TyDecl {
    tyDeclName :: String, 
    tyDeclParams :: List TyParam, 
    tyDeclConstructors :: List Constructor
}

data TyParam = TmParam String Ty 
            | TyParam String

data Constructor = Constructor {
    conName :: String, 
    conArgs :: List (String, Ty), 
    conTy :: Ty
}

data Stmt = Assignment String Stmt
        | Return Tm
        | Switch {
            switchOn :: Tm,
            cases :: List Case
        }

data Case = Case {
    caseOn :: Tm,
    caseBody :: List Stmt
}

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



