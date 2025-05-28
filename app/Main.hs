module Main (main) where

import Lib

import Text.Megaparsec 

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
    types :: [TyDecl], 
    funcs :: [Func], 
    funcMain :: Func
} 

data Func = Func {
    funName :: String, 
    funRetType :: Ty, 
    funArgs :: [(String, Ty)], -- should be dependent
    funBody :: [Stmt],
    funReturns :: Stmt
}

data TyDecl = TyDecl {
    tyDeclName :: String, 
    tyDeclParams :: [TyParam], 
    tyDeclConstructors :: [Constructor]
}

data TyParam = TmParam String Ty 
            | TyParam String

data Constructor = Constructor {
    name :: String, 
    conArgs :: [(String, Ty)], 
    conTy :: Ty
}

data Stmt = Assignment String Stmt
        | Return Tm
        | Switch {
            switchOn :: Tm,
            cases :: [Case]
        }

data Case = Case {
    caseOn :: Tm,
    caseBody :: [Stmt]
}

type Parser = Parsec Void String

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of 
        Left _ -> error "todo"
        Right tm -> tm  

pProg :: Parser Prog
pProg = error "todo"

