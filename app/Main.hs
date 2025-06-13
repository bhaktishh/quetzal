{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Monad.State (evalState, execState, runState)
import Data.List (unsnoc)
import qualified Data.Map as M
import Data.Tuple (swap)
import Data.Void (Void)
import GHC.TypeLits (Nat)
import Lib
import Text.Megaparsec (MonadParsec (eof, try), Parsec, many, parse, runParser, sepBy, sepBy1, sepEndBy1, some, (<|>))
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

reserved :: [String]
reserved =
  [ "func",
    "data",
    "constructor",
    "type",
    "Func",
    "of",
    "while",
    "record",
    "return",
    "case",
    "Void",
    "switch",
    "Ty"
  ]

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
  _ <- pSpaces $ char '{'
  x <- p
  _ <- pSpaces $ char '}'
  pure x

pAngles :: Parser a -> Parser a
pAngles p = do
  _ <- pSpaces $ char '<'
  x <- p
  _ <- pSpaces $ char '>'
  pure x

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of
  Left _ -> undefined
  Right tm -> tm

pTLDecl :: Parser Decl
pTLDecl = (Ty <$> pTyDecl) <|> (Rec <$> pRecDecl)

pProgEl :: Parser ProgEl
pProgEl = pSpaces ((PDecl <$> pTLDecl) <|> (PFunc <$> pFunc))

pProg :: Parser Prog
pProg = many (pSpaces pProgEl) <* eof

pFunc :: Parser Func
pFunc = do
  _ <- pSpaces $ string "func"
  funcName <- pSpaces pLowerStr
  impArgs <- try ((pSpaces (char '<') >> pSpaces (char '>')) >> pure []) <|> try (pSpaces (pAngles pFuncArgs)) <|> pure []
  expArgs <- try ((pSpaces (char '(') >> pSpaces (char ')')) >> pure []) <|> pSpaces (pParens pFuncArgs)
  let funcArgs = map (mkAnnParam False) impArgs ++ map (mkAnnParam True) expArgs
  _ <- pSpaces $ string "of"
  funcRetTy <- pSpaces pTy
  funcBody <- pSpaces $ pCurlies (try pTm <|> pure TmUnit)
  pure $
    Func
      { funcName,
        funcArgs,
        funcRetTy,
        funcBody
      }

mkAnnParam :: Bool -> (Ty, String) -> AnnParam
mkAnnParam b x = AnnParam x b

-- if this tries to parse an empty string it loops, probably because it calls pTy and keeps going
pFuncArgs :: Parser (List (Ty, String))
pFuncArgs =
  pSpaces
    ( try $
        (,)
          <$> pSpaces pTy
          <*> pSpaces pVar
    )
    `sepBy` char ','
    <|> pure []

pVarStr :: Parser String
pVarStr = (:) <$> letterChar <*> many (alphaNumChar <|> char '_')

pVar :: Parser String
pVar = try $ do
  x <- pVarStr
  if x `elem` reserved
    then fail $ x ++ " reserved"
    else return x

pUpperStr :: Parser String
pUpperStr = (:) <$> upperChar <*> many alphaNumChar

pLowerStr :: Parser String
pLowerStr = (:) <$> lowerChar <*> many alphaNumChar

pTyDecl :: Parser TyDecl
pTyDecl = do
  _ <- pSpaces $ string "type"
  tyDeclName <- pSpaces pUpperStr
  impArgs <- try ((pSpaces (char '<') >> pSpaces (char '>')) >> pure []) <|> pSpaces (pAngles pFuncArgs) <|> pure []
  expArgs <- try ((pSpaces (char '(') >> pSpaces (char ')')) >> pure []) <|> pSpaces (pParens pFuncArgs) <|> pure []
  let tyDeclParams = map (mkAnnParam False) impArgs ++ map (mkAnnParam True) expArgs
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
  impArgs <- try ((pSpaces (char '<') >> pSpaces (char '>')) >> pure []) <|> pSpaces (pAngles pFuncArgs) <|> pure []
  expArgs <- try ((pSpaces (char '(') >> pSpaces (char ')')) >> pure []) <|> pSpaces (pParens pFuncArgs) <|> pure []
  let conArgs = map (mkAnnParam False) impArgs ++ map (mkAnnParam True) expArgs
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
  impArgs <- try ((pSpaces (char '<') >> pSpaces (char '>')) >> pure []) <|> pSpaces (pAngles pFuncArgs) <|> pure []
  expArgs <- try ((pSpaces (char '(') >> pSpaces (char ')')) >> pure []) <|> pSpaces (pParens pFuncArgs) <|> pure []
  let recDeclParams = map (mkAnnParam False) impArgs ++ map (mkAnnParam True) expArgs
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
  var <- pSpaces pVar
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

pAssign :: Parser Stmt
pAssign = do
  var <- pSpaces pLowerStr
  _ <- pSpaces $ char '='
  rhs <- pSpaces pTm
  _ <- pSpaces $ char ';'
  pure $ Assign var rhs

pDeclAssign :: Parser Stmt
pDeclAssign = do
  _ <- pSpaces $ string "let"
  ty <- pSpaces pTy -- this is reachable from pTm which is reachable from pTy
  -- add syntax in front of decl to remove LR
  var <- pSpaces pLowerStr
  _ <- pSpaces $ char '='
  rhs <- pSpaces pTm0
  _ <- pSpaces $ char ';'
  pure $ DeclAssign ty var rhs

pWhile :: Parser Stmt
pWhile = do
  _ <- pSpaces $ string "while"
  condition <- pSpaces $ pParens pTm
  body <- pSpaces $ pCurlies $ many pStmt
  pure $
    While
      { condition,
        body
      }

pStmt :: Parser Stmt
pStmt =
  try pDeclAssign
    <|> try pAssign

-- <|> try pWhile

pPlusTm :: Parser Tm
pPlusTm = do
  x <- pSpaces pTm1
  _ <- pSpaces $ char '+'
  y <- pSpaces pTm
  pure $ TmPlus x y

pTmCon :: Parser Tm
pTmCon = do
  name <- pSpaces pUpperStr
  args <- pSpaces $ try (pParens $ pTm `sepBy` char ',') <|> pure []
  pure $ TmCon name args

pTmBlock :: Parser Tm
pTmBlock = do
  stmts <- pSpaces $ many pStmt
  tm <- pSpaces pTm0
  pure $ TmBlock stmts tm

pTmReturn :: Parser Tm
pTmReturn = do
  _ <- pSpaces $ string "return"
  tm <- pSpaces pTm
  _ <- pSpaces $ char ';'
  pure $ TmReturn tm

pTmVar :: Parser Tm
pTmVar = TmVar <$> pVar

pFuncCall :: Parser Tm
pFuncCall = do
  name <- pSpaces pTm1
  args <- pSpaces $ pParens $ (pSpaces pTm1 `sepBy` char ',') <|> pure []
  pure $ TmFuncCall name args

pIf :: Parser Tm
pIf = do
  _ <- pSpaces $ string "if"
  cond <- pSpaces $ pParens pTm
  t <- pSpaces $ pCurlies pTm
  _ <- pSpaces $ string "else"
  e <- pSpaces $ pCurlies pTm
  pure $ TmIf cond t e

pTmSwitch :: Parser Tm
pTmSwitch = do
  _ <- pSpaces $ string "switch"
  switchOn <- pSpaces $ pParens $ pTm `sepBy` char ','
  cases <- pSpaces $ pCurlies $ many pCase
  pure $
    TmSwitch $
      Switch
        { switchOn,
          cases
        }

pCase :: Parser Case
pCase = do
  _ <- pSpaces $ string "case"
  caseOn <- pSpaces $ pParens $ pTm `sepBy` char ','
  caseBody <- pSpaces $ pCurlies pTm
  pure $
    Case
      { caseOn,
        caseBody
      }

pTyTm :: Parser Ty
pTyTm = TyTm <$> pTm

pTmTy :: Parser Tm
pTmTy = TmTy <$> pTy

pTyCustom :: Parser Ty
pTyCustom = do
  tyName <- pSpaces pUpperStr
  impParams <- try (pSpaces $ pAngles $ pTm `sepBy` char ',') <|> pure []
  expParams <- try (pSpaces $ pParens $ pTm `sepBy` char ',') <|> pure []
  let tyParams = impParams ++ expParams
  pure $
    TyCustom
      { tyName,
        tyParams
      }

pTyFunc :: Parser Ty
pTyFunc = do
  _ <- pSpaces $ string "Func"
  _ <- pSpaces $ char '('
  tyFuncArgs <- pFuncArgs
  _ <- pSpaces $ string "=>"
  tyFuncRetTy <- pSpaces pTy
  _ <- pSpaces $ char ')'
  pure $
    TyFunc
      { tyFuncArgs,
        tyFuncRetTy
      }

pTy :: Parser Ty
pTy =
  try pTyBool
    <|> try pTyNat
    <|> try pTyTy
    <|> try pTyUnit
    <|> try pTyFunc
    <|> try pTyCustom
    <|> try pTyTm

pTm0 :: Parser Tm
pTm0 =
  try pPlusTm
    <|> try pTmReturn
    <|> try pFuncCall
    <|> try pTmCon
    <|> try pTmSwitch
    <|> try pTm1

pTm1 :: Parser Tm
pTm1 =
  try (pParens pTm)
    <|> try pTmVar
    <|> pNat
    <|> pBool

pTm :: Parser Tm
pTm = try pTmBlock <|> try pTm0

-- -- parsing utils
parseFromFile p file = runParser p file <$> readFile file

-- combine :: Maybe ([Stmt], Stmt) -> List Stmt
-- combine Nothing = []
-- combine (Just (xs, x)) = xs ++ [x]

doShadowing :: Func -> Func
doShadowing f =
  let tm = funcBody f
   in f {funcBody = doTms (M.fromList (map (\(AnnParam (t, v) _) -> (v, t) ) (funcArgs f))) tm}

doTms :: M.Map String Ty -> Tm -> Tm 
doTms m (TmBlock stmts tm) = TmBlock (doStmts m stmts) tm
doTms m (TmPlus t1 t2) = TmPlus (doTms m t1) (doTms m t2)
doTms m (TmCon v tms) = TmCon v (map (doTms m) tms)
doTms m (TmFunc f) = TmFunc f { funcBody = doTms m (funcBody f) }
doTms m (TmFuncCall t ts) = TmFuncCall (doTms m t) (map (doTms m) ts)
doTms m (TmIf t1 t2 t3) = TmIf (doTms m t1) (doTms m t2) (doTms m t3)
doTms m (TmReturn t) = TmReturn (doTms m t)
doTms m (TmSwitch s) = TmSwitch s {switchOn = map (doTms m) (switchOn s), cases = map (\c -> Case {caseOn = map (doTms m) (caseOn c), caseBody = doTms m (caseBody c)}) (cases s)}
doTms _ tm = tm 

doStmts :: M.Map String Ty -> List Stmt -> List Stmt
doStmts _ [] = []
doStmts vars (x : xs) = case x of
  Assign var tm -> case M.lookup var vars of
    Nothing -> error "assign before declare"
    Just ty -> DeclAssign ty var tm : doStmts vars xs
  DeclAssign ty var tm -> DeclAssign ty var tm : doStmts (M.insert var ty vars) xs
  _ -> x : doStmts vars xs

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

-- may have to parse to a second data type because of the differences

unLoopF :: Func -> List Tm 
unLoopF = undefined 

unLoop :: Tm -> Tm
unLoop (TmFunc f) = 
  let whrDecs = unLoopF f
  in undefined

getHVars :: List Stmt -> List (Ty, String)
getHVars stmts = [] -- todo 

defOuter :: List Stmt -> String -> List AnnParam -> Ty -> Func 
defOuter hdr fname params ty = 
  let funcName = fname ++ "_reco"
      funcInner = fname ++ "_reci"
      hvars = map (`AnnParam` True) $ getHVars hdr 
    in 
      Func { 
        funcName = funcName, 
        funcArgs = params, 
        funcRetTy = ty, 
        funcBody = TmBlock hdr (TmFuncCall (TmVar funcInner) (map (TmVar . getAnnParamVar) (params ++ hvars)))
      }

defInner :: Tm -> Tm -> List Stmt -> String -> List AnnParam -> List (Ty, String) -> Ty -> Func
defInner condition tl body fname params vars retty = 
  let funcName = fname ++ "_reci" 
      hvars = map (`AnnParam` True) vars
    in
    Func {
    funcName = funcName,
    funcArgs = params ++ hvars, 
    funcRetTy = retty, 
    funcBody = TmIf (TmNot condition) (TmReturn tl) (TmBlock body (TmFuncCall (TmVar funcName) (map (TmVar . getAnnParamVar) (params ++ hvars))))
  }

getAnnParamVar :: AnnParam -> String 
getAnnParamVar (AnnParam (_, str) _) = str

getAnnParamTy :: AnnParam -> Ty 
getAnnParamTy (AnnParam (ty, _) _) = ty

-- unSwitch :: Func -> Func
-- unSwitch f = undefined

-- process :: String -> Prog
-- process x = case parse pProg "" x of
--   Left _ -> error "bruh"
--   Right tm -> tm {funcs = map doShadowing (funcs tm)}

processFile :: String -> IO Prog
processFile file = do
  x <- readFile file
  case parse pProg "" x of
    Left _ -> error "wtf"
    Right tm -> pure tm 

writeIdris :: Prog -> String -> IO ()
writeIdris p fpath = writeFile fpath (evalState (uProg p) (0, False))
