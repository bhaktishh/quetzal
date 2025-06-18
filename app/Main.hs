{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Monad.State (evalState, execState, runState)
import Data.List (unsnoc)
import qualified Data.Map as M
import Data.Tuple (swap)
import Data.Void (Void)
import GHC.TypeLits (Nat)
import Lib
import PTypes
import Text.Megaparsec (MonadParsec (eof, try), Parsec, many, parse, runParser, sepBy, sepBy1, sepEndBy1, some, (<|>))
import Text.Megaparsec.Char
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
pTLDecl = (PTy <$> pTyDecl) <|> (Rec <$> pRecDecl)

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
  funcRetTy <- pSpaces pPTy
  funcBody <- pSpaces $ pCurlies (try pPTm <|> pure PTmUnit)
  pure $
    Func
      { funcName,
        funcArgs,
        funcRetTy,
        funcBody
      }

mkAnnParam :: Bool -> (PTy, String) -> AnnParam
mkAnnParam b x = AnnParam x b

-- if this tries to parse an empty string it loops, probably because it calls pPTy and keeps going
pFuncArgs :: Parser (List (PTy, String))
pFuncArgs =
  pSpaces
    ( try $
        (,)
          <$> pSpaces pPTy
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
  conTy <- pSpaces pPTy
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

pRecDeclField :: Parser (PTy, String)
pRecDeclField = do
  ty <- pSpaces pPTy
  var <- pSpaces pVar
  _ <- pSpaces $ char ';'
  pure (ty, var)

pPTyBool :: Parser PTy
pPTyBool = string "Bool" >> pure PTyBool

pBool :: Parser PTm
pBool = pTrue <|> pFalse

pTrue :: Parser PTm
pTrue = string "True" >> pure (PTmBool True)

pFalse :: Parser PTm
pFalse = string "False" >> pure (PTmBool False)

pNat :: Parser PTm
pNat = do
  nums <- some digitChar
  pure $ PTmNat ((read :: String -> Nat) nums)

pPTyNat :: Parser PTy
pPTyNat = string "Nat" >> pure PTyNat

pPTyTy :: Parser PTy
pPTyTy = string "PTy" >> pure PTyTy

pPTyUnit :: Parser PTy
pPTyUnit = string "Void" >> pure PTyUnit

pAssign :: Parser Stmt
pAssign = do
  var <- pSpaces pLowerStr
  _ <- pSpaces $ char '='
  rhs <- pSpaces pPTm
  _ <- pSpaces $ char ';'
  pure $ Assign var rhs

pDeclAssign :: Parser Stmt
pDeclAssign = do
  _ <- pSpaces $ string "let"
  ty <- pSpaces pPTy -- this is reachable from pPTm which is reachable from pPTy
  -- add syntax in front of decl to remove LR
  var <- pSpaces pLowerStr
  _ <- pSpaces $ char '='
  rhs <- pSpaces pPTm0
  _ <- pSpaces $ char ';'
  pure $ DeclAssign ty var rhs

pWhile :: Parser Stmt
pWhile = do
  _ <- pSpaces $ string "while"
  condition <- pSpaces $ pParens pPTm
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
    <|> try pWhile 

-- <|> try pWhile

pPlusPTm :: Parser PTm
pPlusPTm = do
  x <- pSpaces pPTm1
  _ <- pSpaces $ char '+'
  y <- pSpaces pPTm
  pure $ PTmPlus x y

pPTmCon :: Parser PTm
pPTmCon = do
  name <- pSpaces pUpperStr
  args <- pSpaces $ try (pParens $ pPTm `sepBy` char ',') <|> pure []
  pure $ PTmCon name args

pPTmBlock :: Parser PTm
pPTmBlock = do
  stmts <- pSpaces $ many pStmt
  tm <- pSpaces pPTm0
  pure $ PTmBlock stmts tm

pPTmReturn :: Parser PTm
pPTmReturn = do
  _ <- pSpaces $ string "return"
  tm <- pSpaces pPTm
  _ <- pSpaces $ char ';'
  pure $ PTmReturn tm

pPTmVar :: Parser PTm
pPTmVar = PTmVar <$> pVar

pFuncCall :: Parser PTm
pFuncCall = do
  name <- pSpaces pPTm1
  args <- pSpaces $ pParens $ (pSpaces pPTm1 `sepBy` char ',') <|> pure []
  pure $ PTmFuncCall name args

pIf :: Parser PTm
pIf = do
  _ <- pSpaces $ string "if"
  cond <- pSpaces $ pParens pPTm
  t <- pSpaces $ pCurlies pPTm
  _ <- pSpaces $ string "else"
  e <- pSpaces $ pCurlies pPTm
  pure $ PTmIf cond t e

pPTmSwitch :: Parser PTm
pPTmSwitch = do
  _ <- pSpaces $ string "switch"
  switchOn <- pSpaces $ pParens $ pPTm `sepBy` char ','
  cases <- pSpaces $ pCurlies $ many pCase
  pure $
    PTmSwitch $
      Switch
        { switchOn,
          cases
        }

pCase :: Parser Case
pCase = do
  _ <- pSpaces $ string "case"
  caseOn <- pSpaces $ pParens $ pPTm `sepBy` char ','
  caseBody <- pSpaces $ pCurlies pPTm
  pure $
    Case
      { caseOn,
        caseBody
      }

pPTyPTm :: Parser PTy
pPTyPTm = PTyPTm <$> pPTm

pPTmPTy :: Parser PTm
pPTmPTy = PTmPTy <$> pPTy

pPTyCustom :: Parser PTy
pPTyCustom = do
  tyName <- pSpaces pUpperStr
  impParams <- try (pSpaces $ pAngles $ pPTm `sepBy` char ',') <|> pure []
  expParams <- try (pSpaces $ pParens $ pPTm `sepBy` char ',') <|> pure []
  let tyParams = impParams ++ expParams
  pure $
    PTyCustom
      { tyName,
        tyParams
      }

pPTyFunc :: Parser PTy
pPTyFunc = do
  _ <- pSpaces $ string "Func"
  _ <- pSpaces $ char '('
  tyFuncArgs <- pFuncArgs
  _ <- pSpaces $ string "=>"
  tyFuncRetTy <- pSpaces pPTy
  _ <- pSpaces $ char ')'
  pure $
    PTyFunc
      { tyFuncArgs,
        tyFuncRetTy
      }

pPTy :: Parser PTy
pPTy =
  try pPTyBool
    <|> try pPTyNat
    <|> try pPTyTy
    <|> try pPTyUnit
    <|> try pPTyFunc
    <|> try pPTyCustom
    <|> try pPTyPTm

pPTm0 :: Parser PTm
pPTm0 =
  try pPlusPTm
    <|> try pPTmReturn
    <|> try pFuncCall
    <|> try pPTmCon
    <|> try pPTmSwitch
    <|> try pPTm1

pPTm1 :: Parser PTm
pPTm1 =
  try (pParens pPTm)
    <|> try pPTmVar
    <|> pNat
    <|> pBool

pPTm :: Parser PTm
pPTm = try pPTmBlock <|> try pPTm0

-- -- parsing utils
parseFromFile p file = runParser p file <$> readFile file

-- combine :: Maybe ([Stmt], Stmt) -> List Stmt
-- combine Nothing = []
-- combine (Just (xs, x)) = xs ++ [x]

-- doShadowing :: Func -> Func
-- doShadowing f =
--   let tm = funcBody f
--    in f {funcBody = doPTms (M.fromList (map (\(AnnParam (t, v) _) -> (v, t)) (funcArgs f))) tm}

-- doPTms :: M.Map String PTy -> PTm -> PTm
-- doPTms m (PTmBlock stmts tm) = PTmBlock (doStmts m stmts) tm
-- doPTms m (PTmPlus t1 t2) = PTmPlus (doPTms m t1) (doPTms m t2)
-- doPTms m (PTmCon v tms) = PTmCon v (map (doPTms m) tms)
-- doPTms m (PTmFunc f) = PTmFunc f {funcBody = doPTms m (funcBody f)}
-- doPTms m (PTmFuncCall t ts) = PTmFuncCall (doPTms m t) (map (doPTms m) ts)
-- doPTms m (PTmIf t1 t2 t3) = PTmIf (doPTms m t1) (doPTms m t2) (doPTms m t3)
-- doPTms m (PTmReturn t) = PTmReturn (doPTms m t)
-- doPTms m (PTmSwitch s) =
--   PTmSwitch
--     s
--       { switchOn = map (doPTms m) (switchOn s),
--         cases = map (\c -> Case {caseOn = map (doPTms m) (caseOn c), caseBody = doPTms m (caseBody c)}) (cases s)
--       }
-- doPTms _ tm = tm

-- doStmts :: M.Map String PTy -> List Stmt -> List Stmt
-- doStmts _ [] = []
-- doStmts vars (x : xs) = case x of
--   Assign var tm -> case M.lookup var vars of
--     Nothing -> error "assign before declare"
--     Just ty -> DeclAssign ty var tm : doStmts vars xs
--   DeclAssign ty var tm -> DeclAssign ty var tm : doStmts (M.insert var ty vars) xs
--   _ -> x : doStmts vars xs

-- {-
-- foo_iterative(params){
--     header
--     while(condition){
--         loop_body
--     }
--
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

-- unLoopF :: Func -> List PTm
-- unLoopF = undefined

-- unLoop :: PTm -> PTm
-- unLoop (PTmFunc f) =
--   let whrDecs = unLoopF f
--    in undefined

-- getHVars :: List Stmt -> List (PTy, String)
-- getHVars stmts = [] -- todo

-- defOuter :: List Stmt -> String -> List AnnParam -> PTy -> Func
-- defOuter hdr fname params ty =
--   let funcName = fname ++ "_reco"
--       funcInner = fname ++ "_reci"
--       hvars = map (`AnnParam` True) $ getHVars hdr
--    in Func
--         { funcName = funcName,
--           funcArgs = params,
--           funcRetTy = ty,
--           funcBody = PTmBlock hdr (PTmFuncCall (PTmVar funcInner) (map (PTmVar . getAnnParamVar) (params ++ hvars)))
--         }

-- defInner :: PTm -> PTm -> List Stmt -> String -> List AnnParam -> List (PTy, String) -> PTy -> Func
-- defInner condition tl body fname params vars retty =
--   let funcName = fname ++ "_reci"
--       hvars = map (`AnnParam` True) vars
--    in Func
--         { funcName = funcName,
--           funcArgs = params ++ hvars,
--           funcRetTy = retty,
--           funcBody = PTmIf (PTmNot condition) (PTmReturn tl) (PTmBlock body (PTmFuncCall (PTmVar funcName) (map (PTmVar . getAnnParamVar) (params ++ hvars))))
--         }

-- getAnnParamVar :: AnnParam -> String
-- getAnnParamVar (AnnParam (_, str) _) = str

-- getAnnParamPTy :: AnnParam -> PTy
-- getAnnParamPTy (AnnParam (ty, _) _) = ty

-- unSwitch :: Func -> Func
-- unSwitch f = undefined

-- process :: String -> Prog
-- process x = case parse pProg "" x of
--   Left _ -> error "bruh"
--   Right tm -> tm {funcs = map doShadowing (funcs tm)}

processFile :: String -> Parser a -> IO a
processFile file p = do
  x <- readFile file
  case parse p "" x of
    Left _ -> error "wtf"
    Right tm -> pure tm

writeIdris :: Prog -> String -> IO ()
writeIdris p fpath = writeFile fpath (evalState (uProg p) (0, False))
