{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Data.List (unsnoc)
import qualified Data.Map as M
import Data.Tuple (swap)
import Data.Void (Void)
import GHC.TypeLits (Nat)
import Lib
import Text.Megaparsec (MonadParsec (eof, try), Parsec, many, parse, runParser, sepBy, some, (<|>))
import Text.Megaparsec.Char
import ToIdris
import Types

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

pSpaces :: Parser a -> Parser a
pSpaces p = space *> p <* space

pParens :: Parser a -> Parser a
pParens p = do
  _ <- pSpaces $ char '('
  x <- p
  _ <- pSpaces $ char ')'
  pure x

pCurlies :: Parser a -> Parser a
pCurlies p = do
  _ <- pSpaces $ char '('
  x <- p
  _ <- pSpaces $ char ')'
  pure x

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of
  Left _ -> undefined
  Right tm -> tm

pTLDecl :: Parser Decl
pTLDecl = (Ty <$> pTyDecl) <|> (Rec <$> pRecDecl)

pProg :: Parser Prog
pProg = (PDecl <$> pTLDecl) <|> (PFunc <$> pFunc) <* eof

pFunc :: Parser Func
pFunc = do
  _ <- pSpaces $ string "func"
  funcName <- pSpaces pLowerStr
  impArgs <- try $ pSpaces pImplicit
  expArgs <- pSpaces $ pParens pFuncArgs
  let funcArgs = (map (mkAnnParam False) impArgs) ++ (map (mkAnnParam True) expArgs)
  _ <- pSpaces $ string "of"
  funcRetTy <- pSpaces pTy
  funcBody <- pSpaces $ pCurlies pTm
  pure $
    Func
      { funcName,
        funcArgs,
        funcRetTy,
        funcBody
      }

mkAnnParam :: Bool -> (Ty, String) -> AnnParam
mkAnnParam b x = AnnParam x b

pImplicit :: Parser (List (Ty, String))
pImplicit = do
  _ <- pSpaces $ char '<'
  args <- pFuncArgs
  _ <- pSpaces $ char '>'
  pure args

pFuncArgs :: Parser (List (Ty, String))
pFuncArgs =
  pSpaces
    ( (,)
        <$> pSpaces pTy
        <*> pSpaces pVarStr
    )
    `sepBy` char ','

pVarStr :: Parser String
pVarStr = (:) <$> letterChar <*> many alphaNumChar

pUpperStr :: Parser String
pUpperStr = (:) <$> upperChar <*> many alphaNumChar

pLowerStr :: Parser String
pLowerStr = (:) <$> lowerChar <*> many alphaNumChar

pTyDecl :: Parser TyDecl
pTyDecl = do
  _ <- pSpaces $ string "type"
  tyDeclName <- pSpaces pUpperStr
  impArgs <- try $ pSpaces pImplicit
  expArgs <- try $ pSpaces $ pParens pFuncArgs
  let tyDeclParams = (map (mkAnnParam False) impArgs) ++ (map (mkAnnParam True) expArgs)
  tyDeclConstructors <- pSpaces $ pCurlies $ many pTyDeclConstructor
  pure $
    TyDecl
      { tyDeclName,
        tyDeclParams,
        tyDeclConstructors
      }

pTyDeclConstructor :: Parser Constructor
pTyDeclConstructor = do
  _ <- pSpaces $ string "constructor"
  conName <- pSpaces pUpperStr
  impArgs <- try $ pSpaces pImplicit
  expArgs <- try $ pSpaces $ pParens pFuncArgs
  let conArgs = (map (mkAnnParam False) impArgs) ++ (map (mkAnnParam True) expArgs)
  _ <- pSpaces $ string "of"
  conTy <- pSpaces pTy
  _ <- pSpaces $ char ';'
  pure $
    Constructor
      { conName,
        conArgs,
        conTy
      }

pRecDecl :: Parser RecDecl
pRecDecl = do
  _ <- pSpaces $ string "record"
  recDeclName <- pSpaces pUpperStr
  impArgs <- try $ pSpaces pImplicit
  expArgs <- try $ pSpaces $ pParens pFuncArgs
  let recDeclParams = (map (mkAnnParam False) impArgs) ++ (map (mkAnnParam True) expArgs)
  recDeclFields <- pSpaces $ pCurlies $ many pRecDeclField
  pure $
    RecDecl
      { recDeclName,
        recDeclParams,
        recDeclFields
      }

pRecDeclField :: Parser (Ty, String)
pRecDeclField = do
  ty <- pSpaces pTy
  var <- pSpaces pVarStr
  _ <- pSpaces $ char ';'
  pure (ty, var)

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

pTyUnit :: Parser Ty
pTyUnit = string "Void" >> pure TyUnit

pTm :: Parser Tm
pTm = undefined

pTy :: Parser Ty
pTy = undefined

-- -- function definitions

-- pFunc :: Parser Func
-- pFunc = do
--   _ <- pSpaces $ string "func"
--   funcName <- pSpaces pLowerString
--   _ <- pSpaces $ char '<'
--   funcErasedArgs <- pSpaces pFuncArgs
--   _ <- pSpaces $ char '>'
--   _ <- pSpaces $ char '('
--   funcArgs <- pSpaces pFuncArgs
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ string "of"
--   funcRetType <- pSpaces pTy
--   _ <- pSpaces $ char '{'
--   body <- pSpaces $ many pStmt
--   let funcBody = unsnoc body
--   _ <- pSpaces $ char '}'
--   pure $
--     Func
--       { funcName,
--         funcRetType,
--         funcErasedArgs,
--         funcArgs,
--         funcBody
--       }

-- pLowerString :: Parser String
-- pLowerString = (:) <$> lowerChar <*> many alphaNumChar

-- pUpperString :: Parser String
-- pUpperString = (:) <$> upperChar <*> many alphaNumChar

-- pVar :: Parser String
-- pVar = pLowerString

-- pVarTm :: Parser Tm
-- pVarTm = TmVar <$> pVar

-- pTyVarTm :: Parser Tm
-- pTyVarTm = TmTyVar <$> pTyVar

-- pTyVarTy :: Parser Ty
-- pTyVarTy = TyVar <$> pTyVar

-- pTyFunctionCall :: Parser Ty
-- pTyFunctionCall = do
--   name <- pSpaces $ pTyVar <|> pVar
--   _ <- pSpaces $ char '('
--   args <- pSpaces $ pTm `sepBy` char ','
--   _ <- pSpaces $ char ')'
--   pure $ TyFunctionCall name args

-- pPlusTm :: Parser Tm
-- pPlusTm = do
--   x <- pSpaces pTm1
--   _ <- char '+'
--   y <- pSpaces pTm
--   pure $ TmPlus x y

-- pTm :: Parser Tm
-- pTm = try pPlusTm <|> try pFunctionCall <|> try pConTm <|> pTm1

-- pTm1 :: Parser Tm
-- pTm1 = try (pParens pTm) <|> try pVarTm <|> pTyVarTm <|> pNat <|> pBool

-- pTyCustom :: Parser Ty
-- pTyCustom = do
--   tyName <- pSpaces pUpperString
--   _ <- pSpaces $ char '<'
--   tyErasedParams <- pSpaces pTm `sepBy` char ','
--   _ <- pSpaces $ char '>'
--   _ <- pSpaces $ char '('
--   tyParams <- pSpaces pTm `sepBy` char ','
--   _ <- pSpaces $ char ')'
--   pure $
--     TyCustom
--       { tyName,
--         tyErasedParams,
--         tyParams
--       }

-- pTyFunc :: Parser Ty
-- pTyFunc = do
--   _ <- pSpaces $ string "Func"
--   _ <- pSpaces $ char '('
--   tyFuncArgs <- pFuncArgs
--   _ <- pSpaces $ string "=>"
--   tyFuncRetTy <- pSpaces pTy
--   _ <- pSpaces $ char ')'
--   pure $
--     TyFunc
--       { tyFuncArgs,
--         tyFuncRetTy
--       }

-- pTy :: Parser Ty
-- pTy = try pTyCustom <|> try pTyFunc <|> try pTyFunctionCall <|> pTyNat <|> pTyBool <|> pTyTy <|> pTyVoid <|> pTyVarTy

-- -- type declarations
-- pTyDeclConstructor :: Parser Constructor
-- pTyDeclConstructor = do
--   _ <- pSpaces $ string "constructor"
--   conName <- pSpaces pUpperString
--   conErasedArgs <- pSpaces pConErasedArgs
--   conArgs <- pSpaces pConArgs
--   _ <- pSpaces $ string "of"
--   conTy <- pSpaces pTy
--   _ <- pSpaces pSemicolon
--   pure $
--     Constructor
--       { conName,
--         conErasedArgs,
--         conArgs,
--         conTy
--       }

-- pConErasedArgs :: Parser [(Ty, String)]
-- pConErasedArgs = do
--   _ <- pSpaces $ char '<'
--   ls <- pFuncArgs
--   _ <- pSpaces $ char '>'
--   pure ls

-- pConArgs :: Parser [(Ty, String)]
-- pConArgs = do
--   _ <- pSpaces $ char '('
--   ls <- pFuncArgs
--   _ <- pSpaces $ char ')'
--   pure ls

-- pRecDecl :: Parser RecDecl
-- pRecDecl = do
--   _ <- pSpaces $ string "record"
--   recDeclName <- pSpaces pUpperString
--   _ <- pSpaces $ char '<'
--   recDeclErasedParams <- pSpaces pFuncArgs
--   _ <- pSpaces $ char '>'
--   _ <- pSpaces $ char '('
--   recDeclParams <- pSpaces pFuncArgs
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ char '{'
--   recDeclFields <- pSpaces $ many pRecDeclField
--   _ <- pSpaces $ char '}'
--   pure $
--     RecDecl
--       { recDeclName,
--         recDeclErasedParams,
--         recDeclParams,
--         recDeclFields
--       }

-- pTyDecl :: Parser TyDecl
-- pTyDecl = do
--   _ <- pSpaces $ string "type"
--   tyDeclName <- pSpaces pUpperString
--   _ <- pSpaces $ char '<'
--   tyDeclErasedParams <- pSpaces pFuncArgs
--   _ <- pSpaces $ char '>'
--   _ <- pSpaces $ char '('
--   tyDeclParams <- pSpaces pFuncArgs
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ char '{'
--   tyDeclConstructors <- pSpaces $ many pTyDeclConstructor
--   _ <- pSpaces $ char '}'
--   pure $
--     TyDecl
--       { tyDeclName,
--         tyDeclErasedParams,
--         tyDeclParams,
--         tyDeclConstructors
--       }

-- -- statements

-- pStmt :: Parser Stmt
-- pStmt =
--   pSpaces $
--     ( try pDeclAssign
--         <|> try pDecl
--         <|> try pAssign
--         <|> try pSwitch
--         <|>
--         -- pFunctionCall <|> TODO
--         pReturn
--     )
--       <* pSemicolon
--         <|> pIf
--         <|> pWhile
--         <|> pBlank

-- pBlank :: Parser Stmt
-- pBlank = char ';' >> pure Blank

-- pSwitch :: Parser Stmt
-- pSwitch = do
--   _ <- pSpaces $ string "switch"
--   _ <- pSpaces $ char '('
--   switchOn <- pSpaces pTm `sepBy` char ','
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ char '{'
--   cases <- some $ pSpaces pCase
--   _ <- pSpaces $ char '}'
--   pure $
--     Switch
--       { switchOn,
--         cases
--       }

-- pCase :: Parser Case
-- pCase = do
--   _ <- pSpaces $ string "case"
--   _ <- pSpaces $ char '('
--   caseOn <- pSpaces pTm `sepBy` char ','
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ char '{'
--   caseBody <- many $ pSpaces pStmt
--   _ <- pSpaces $ char '}'
--   pure $
--     Case
--       { caseOn,
--         caseBody
--       }

-- pReturn :: Parser Stmt
-- pReturn = do
--   _ <- pSpaces $ string "return"
--   tm <- pSpaces pTm
--   pure $ Return tm

-- pAssign :: Parser Stmt
-- pAssign = do
--   var <- pSpaces pLowerString
--   _ <- pSpaces $ char '='
--   rhs <- pSpaces pTm
--   pure $ Assign var rhs

-- pDecl :: Parser Stmt
-- pDecl = do
--   ty <- pSpaces pTy
--   var <- pSpaces pLowerString
--   pure $ Decl ty var

-- pDeclAssign :: Parser Stmt
-- pDeclAssign = do
--   ty <- pSpaces pTy
--   var <- pSpaces pLowerString
--   _ <- pSpaces $ char '='
--   rhs <- pSpaces pTm
--   pure $ DeclAssign ty var rhs

-- pFunctionCall :: Parser Tm
-- pFunctionCall = do
--   name <- pSpaces pLowerString
--   _ <- pSpaces $ char '('
--   args <- pSpaces pTm `sepBy` char ','
--   _ <- pSpaces $ char ')'
--   pure $ TmFunctionCall name args

-- pConTm :: Parser Tm
-- pConTm = do
--   name <- pSpaces pUpperString
--   _ <- pSpaces $ char '('
--   args <- pSpaces pTm `sepBy` char ','
--   _ <- pSpaces $ char ')'
--   pure $ TmCon name args

-- pWhile :: Parser Stmt
-- pWhile = do
--   _ <- pSpaces $ string "while"
--   _ <- pSpaces $ char '('
--   condition <- pSpaces pTm
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ char '{'
--   body <- many $ pSpaces pStmt
--   _ <- pSpaces $ char '}'
--   pure $
--     While
--       { condition,
--         body
--       }

-- pIf :: Parser Stmt
-- pIf = do
--   _ <- pSpaces $ string "if"
--   _ <- pSpaces $ char '('
--   cond <- pSpaces pTm
--   _ <- pSpaces $ char ')'
--   _ <- pSpaces $ char '{'
--   thenCase <- many $ pSpaces pStmt
--   _ <- pSpaces $ char '}'
--   _ <- pSpaces $ string "else"
--   _ <- pSpaces $ char '{'
--   elseCase <- many $ pSpaces pStmt
--   _ <- pSpaces $ char '}'
--   pure $
--     If
--       { cond,
--         thenCase,
--         elseCase
--       }

-- -- parsing utils
parseFromFile p file = runParser p file <$> readFile file

-- combine :: Maybe ([Stmt], Stmt) -> List Stmt
-- combine Nothing = []
-- combine (Just (xs, x)) = xs ++ [x]

-- doShadowing :: Func -> Func
-- doShadowing f =
--   let stmts = funcBody f
--    in f {funcBody = unsnoc $ doStmts (M.fromList (map swap (funcArgs f))) (combine stmts)}

-- doStmts :: M.Map String Ty -> List Stmt -> List Stmt
-- doStmts _ [] = []
-- doStmts vars (x : xs) = case x of
--   Assign var tm -> case M.lookup var vars of
--     Nothing -> error "assign before declare"
--     Just ty -> DeclAssign ty var tm : doStmts vars xs
--   Decl ty var -> Decl ty var : doStmts (M.insert var ty vars) xs
--   DeclAssign ty var tm -> DeclAssign ty var tm : doStmts (M.insert var ty vars) xs
--   Switch {switchOn, cases} ->
--     Switch
--       { switchOn,
--         cases = map (\y -> y {caseBody = doStmts vars (caseBody y)}) cases
--       }
--       : doStmts vars xs
--   _ -> x : doStmts vars xs

-- {-
-- foo_iterative(params){
--     header
--     while(condition){
--         loop_body
--     }
--     return tail
-- }

-- foo_recursive(params){
--     header
--     return foo_recursion(params, header_vars)
-- }

-- foo_recursion(params, header_vars){
--     if(!condition){
--         return tail
--     }

--     loop_body
--     return foo_recursion(params, modified_header_vars)
-- }
-- -}
-- unLoop :: Func -> List Func
-- unLoop f = undefined

-- unSwitch :: Func -> Func
-- unSwitch f = undefined

-- process :: String -> Prog
-- process x = case parse pProg "" x of
--   Left _ -> error "bruh"
--   Right tm -> tm {funcs = map doShadowing (funcs tm)}

-- processFile :: String -> IO Prog
-- processFile file = do
--   x <- readFile file
--   pure $ process x

-- writeIdris :: Prog -> String -> IO ()
-- writeIdris p fpath = writeFile fpath (uProg p)
