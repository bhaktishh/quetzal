{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

module Parse where

import Data.Char (toUpper)
import Data.List (intercalate, intersperse)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Void (Void)
import GHC.TypeLits (Nat)
import PTypes
import Text.Megaparsec
  ( MonadParsec (eof, try),
    Parsec,
    many,
    noneOf,
    optional,
    parse,
    sepBy,
    some,
    (<|>),
  )
import Text.Megaparsec.Char

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
    "Ty",
    "FSM",
    "action"
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

pSquare :: Parser a -> Parser a
pSquare p = do
  _ <- pSpaces $ char '['
  x <- p
  _ <- pSpaces $ char ']'
  pure x

tmParse :: String -> Prog
tmParse str = case parse pProg "" str of
  Left _ -> undefined
  Right tm -> tm

pTmString :: Parser PTm
pTmString = do
  _ <- pSpaces $ char '"'
  str <- pSpaces $ many (noneOf "\"")
  _ <- pSpaces $ char '"'
  pure $ PTmString str

pTLDecl :: Parser Decl
pTLDecl = (PTy <$> pTyDecl) <|> (Rec <$> pRecDecl)

pProgEl :: Parser ProgEl
pProgEl = pSpaces (pImport <|> (PDecl <$> pTLDecl) <|> (PFunc <$> pFunc))

pImport :: Parser ProgEl
pImport = do
  _ <- pSpaces $ string "import"
  m <- pSpaces $ pUpperStr `sepBy` char '.'
  pure $ PImport (intercalate "." m)

getFuncs :: Prog -> List Func
getFuncs [] = []
getFuncs (PFunc f : xs) = f : getFuncs xs
getFuncs (_ : xs) = getFuncs xs

pProg :: Parser Prog
pProg = many (pSpaces pProgEl) <* eof

-- prog ::
-- pProg = do
--   prog <- many (pSpaces pProgEl) <* eof
--   -- TODO should we store a map of some sort for easy identification of exec func data
--   -- i dont think this will be necessary actually but will keep around to try later
--   pure ((PFSM <$> M.elems kvs) ++ prog, kvs)

fstUpper :: String -> String
fstUpper [] = []
fstUpper (x : xs) = toUpper x : xs

-- add global FSM structures populated with init and action directive funcs
mkFSMs :: Func -> M.Map DirectiveSub FSM -> M.Map DirectiveSub FSM
mkFSMs f kvs = case funcDirective f of
  Nothing -> kvs
  Just (Directive dSub@(DFSM res st) dTy) ->
    let (kvs', fsm) = maybe (M.insert dSub (FSM {resourceTy = res, stateTy = st, initCons = [], actions = []}) kvs, FSM {resourceTy = res, stateTy = st, initCons = [], actions = []}) (kvs,) (M.lookup dSub kvs)
     in case dTy of
          DAction {directiveReturns, directiveStTrans} ->
            let actionNew =
                  Action
                    { actionName = fstUpper $ funcName f,
                      actionRetTy = directiveReturns,
                      actionStTrans = directiveStTrans
                    }
             in M.adjust (\x -> let actionsOld = actions x in x {actions = actionNew : actionsOld}) dSub kvs'
          DInit -> M.adjust (\x -> let initConsOld = initCons x in x {initCons = f : initConsOld}) dSub kvs'
          _ -> kvs'

pEff :: Parser Eff
pEff = do
  _ <- pSpaces $ char '['
  eff <- try (pSpaces (string "IO") >> pure IO)
  _ <- pSpaces $ char ']'
  pure eff

pDirectiveSub :: Parser DirectiveSub
pDirectiveSub = do
  _ <- pSpaces $ string "FSM"
  (res, st) <- pSpaces $ pParens $ (,) <$> pPTy <*> (pSpaces (char ',') >> pPTy)
  pure (DFSM res st)

pStTrans :: Parser (PTm, PTm)
pStTrans = do
  _ <- pSpaces $ char '['
  stIn <- pSpaces pPTm
  stOut <- try (pSpaces (string "-->") >> pSpaces pPTm) <|> pure stIn
  _ <- pSpaces $ char ']'
  pure (stIn, stOut)

pDAction :: Parser Directive
pDAction = do
  _ <- pSpaces $ string "#action"
  directiveSub <- pSpaces pDirectiveSub
  directiveReturns <- try (string "returns" >> (,) <$> pSpaces pPTy <*> optional (pSpaces pLowerStr)) <|> pure (PTyUnit, Nothing)
  directiveStTrans <- pSpaces pStTrans
  pure $
    Directive
      directiveSub
      DAction
        { directiveReturns,
          directiveStTrans
        }

pDInit :: Parser Directive
pDInit = do
  _ <- pSpaces $ string "#init"
  directiveSub <- pSpaces pDirectiveSub
  pure $ Directive directiveSub DInit

pDRun :: Parser Directive
pDRun = do
  _ <- pSpaces $ string "#run"
  directiveSub <- pSpaces pDirectiveSub
  directiveReturns <- try (string "returns" >> (,) <$> pSpaces pPTy <*> optional (pSpaces pLowerStr)) <|> pure (PTyUnit, Nothing)
  directiveWith <- pSpaces (string "with") >> ((,) <$> (pSpaces pPTmThis >> pSpaces (char '=') >> pure "this") <*> pPTm)
  directiveStTrans <- pSpaces pStTrans
  pure $
    Directive
      directiveSub
      DRun
        { directiveReturns,
          directiveWith,
          directiveStTrans
        }

pDirective :: Parser Directive
pDirective = try (pSpaces pDAction) <|> try (pSpaces pDInit) <|> try (pSpaces pDRun)

pFunc :: Parser Func
pFunc = do
  funcDirective <- optional (pSpaces pDirective)
  funcEff <- optional (pSpaces pEff)
  _ <- pSpaces $ string "func"
  funcName <- pSpaces pLowerStr
  impArgs <- try ((pSpaces (char '<') >> pSpaces (char '>')) >> pure []) <|> try (pSpaces (pAngles pFuncArgs)) <|> pure []
  expArgs <- try ((pSpaces (char '(') >> pSpaces (char ')')) >> pure []) <|> pSpaces (pParens pFuncArgs)
  let funcArgs = map (mkAnnParam False) impArgs ++ map (mkAnnParam True) expArgs
  funcRetTy <- try (pSpaces (string "returns") >> pSpaces pPTy) <|> pure PTyUnit
  funcBody <- pSpaces $ pCurlies (try pStmt <|> pure (StBlock []))
  pure $
    Func
      { funcName,
        funcArgs,
        funcRetTy,
        funcBody,
        funcEff,
        funcDirective
      }

mkAnnParam :: Bool -> (PTy, String) -> AnnParam
mkAnnParam b x = AnnParam x b

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

pTmUnit :: Parser PTm
pTmUnit = pSpaces $ string "()" >> pure PTmUnit

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
  cons <- pSpaces $ pCurlies $ many pTyDeclConstructor
  let tyDeclConstructors = map (\c -> if conTy c == PTyHole then c {conTy = PTyCustom {tyName = tyDeclName, tyParams = map (PTmPTy . fst) expArgs}} else c) cons
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
  impArgs <- try ((pSpaces (char '<') >> pSpaces (char '>')) >> pure []) <|> try (pSpaces (pAngles pFuncArgs)) <|> pure []
  expArgs <- try ((pSpaces (char '(') >> pSpaces (char ')')) >> pure []) <|> try (pSpaces (pParens pFuncArgs)) <|> pure []
  let conArgs = map (mkAnnParam False) impArgs ++ map (mkAnnParam True) expArgs
  conTy <- try (pSpaces $ string "of" >> pSpaces pPTy) <|> pure PTyHole
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

pPTyList :: Parser PTy
pPTyList = PTyList <$> (string "List" >> pPTy)

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
pPTyTy = string "Ty" >> pure PTyTy

pPTyUnit :: Parser PTy
pPTyUnit = string "()" >> pure PTyUnit

pAssign :: Parser Stmt
pAssign = do
  var <- pSpaces pLowerStr
  _ <- pSpaces $ char '='
  rhs <- pSpaces pPTm
  _ <- pSpaces $ char ';'
  pure $ StAssign var rhs

pDeclAssign :: Parser Stmt
pDeclAssign = do
  (ty, var) <- try ((,) <$> optional (pSpaces pPTy) <*> pSpaces pLowerStr) <|> (,) Nothing <$> pSpaces pLowerStr
  _ <- pSpaces $ char '='
  rhs <- pSpaces pPTm
  _ <- pSpaces $ char ';'
  pure $ StDeclAssign ty var rhs

pSkip :: Parser Stmt
pSkip = do
  _ <- pSpaces $ string ";;"
  pure StSkip

pWhile :: Parser Stmt
pWhile = do
  _ <- pSpaces $ string "while"
  condition <- pSpaces $ pParens pPTm
  body <- pSpaces $ pCurlies pStmt
  pure $
    StWhile
      { condition,
        body
      }

pEWhile :: Parser Stmt
pEWhile = do
  _ <- pSpaces $ string "ewhile"
  condition <- pSpaces $ pParens pPTm
  body <- pSpaces $ pCurlies pStmt
  pure $
    StEWhile
      { condition,
        body
      }

pStIf :: Parser Stmt
pStIf = do
  _ <- pSpaces $ string "if"
  cond <- pSpaces $ pParens pPTm
  t <- pSpaces $ pCurlies pStmt
  _ <- pSpaces $ string "else"
  e <- pSpaces $ pCurlies pStmt
  pure $ StIf cond t e

pStEIf :: Parser Stmt
pStEIf = do
  _ <- pSpaces $ string "eif"
  cond <- pSpaces $ pParens pPTm
  t <- pSpaces $ pCurlies pStmt
  _ <- pSpaces $ string "else"
  e <- pSpaces $ pCurlies pStmt
  pure $ StEIf cond t e

pStmt :: Parser Stmt
pStmt = StBlock <$> some pStmt0

pStmt0 :: Parser Stmt
pStmt0 =
  try pSkip
    <|> try pDeclAssign
    <|> try pAssign
    <|> try pWhile
    <|> try pEWhile
    <|> try pStReturn
    <|> try pStIf
    <|> try pStEIf
    <|> try pStSwitch
    <|> try pStDot

pPlusPTm :: Parser PTm
pPlusPTm = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ char '+'
  y <- pSpaces pPTm0
  pure $ PTmPlus x y

pTmMinus :: Parser PTm
pTmMinus = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ char '-'
  y <- pSpaces pPTm0
  pure $ PTmMinus x y

pTmMult :: Parser PTm
pTmMult = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ char '*'
  y <- pSpaces pPTm0
  pure $ PTmMult x y

pTmDiv :: Parser PTm
pTmDiv = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ char '/'
  y <- pSpaces pPTm0
  pure $ PTmDiv x y

pTmMod :: Parser PTm
pTmMod = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ char '%'
  y <- pSpaces pPTm0
  pure $ PTmMod x y

pTmNot :: Parser PTm
pTmNot = do
  _ <- pSpaces $ char '!'
  x <- pSpaces pPTm
  pure $ PTmNot x

pTmBEq :: Parser PTm
pTmBEq = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ string "=="
  y <- pSpaces pPTm0
  pure $ PTmBEq x y

pTmBAnd :: Parser PTm
pTmBAnd = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ string "&&"
  y <- pSpaces pPTm0
  pure $ PTmBAnd x y

pTmBOr :: Parser PTm
pTmBOr = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ string "||"
  y <- pSpaces pPTm0
  pure $ PTmBOr x y

pTmBLT :: Parser PTm
pTmBLT = do
  x <- pSpaces pPTm0
  _ <- pSpaces $ char '<'
  y <- pSpaces pPTm0
  pure $ PTmBLT x y

pPTmCon :: Parser PTm
pPTmCon = do
  name <- pSpaces pUpperStr
  args <- pSpaces $ try (pParens $ pPTm `sepBy` char ',') <|> pure []
  pure $ PTmCon name args

pStReturn :: Parser Stmt
pStReturn = do
  _ <- pSpaces $ string "return"
  tm <- pSpaces pPTm
  _ <- pSpaces $ char ';'
  pure $ StReturn tm

pPTmVar :: Parser PTm
pPTmVar = PTmVar <$> pVar

pPTmWildCard :: Parser PTm
pPTmWildCard = pSpaces (char '_') >> pure PTmWildCard

pFuncCall :: Parser PTm
pFuncCall = do
  name <- pSpaces pPTm0
  args <- pSpaces $ pParens $ (pSpaces pPTm `sepBy` char ',') <|> pure []
  pure $ PTmFuncCall name args

pIf :: Parser PTm
pIf = do
  _ <- pSpaces $ string "if"
  cond <- pSpaces $ pParens pPTm
  t <- pSpaces $ pCurlies pPTm
  _ <- pSpaces $ string "else"
  e <- pSpaces $ pCurlies pPTm
  pure $ PTmIf cond t e

pTernary :: Parser PTm
pTernary = do
  t1 <- pSpaces pPTm0
  _ <- pSpaces $ char '?'
  t2 <- pSpaces pPTm0
  _ <- pSpaces $ char ':'
  t3 <- pSpaces pPTm0
  pure $ PTmTernary t1 t2 t3

pStSwitch :: Parser Stmt
pStSwitch = do
  _ <- pSpaces $ string "switch"
  switchOn <- pSpaces $ pParens $ pPTm `sepBy` char ','
  _ <- pSpaces $ char '{'
  cases <- pSpaces $ many pCase
  defaultCase <- pSpaces $ optional pDefault
  _ <- pSpaces $ char '}'
  pure $
    StSwitch $
      Switch
        { switchOn,
          cases,
          defaultCase
        }

pStDot :: Parser Stmt
pStDot = do
  t1 <- (pSpaces (string "IO") >> pure Nothing) <|> Just <$> pSpaces pPTm0
  _ <- pSpaces $ char '.'
  PTmFuncCall f xs <- pSpaces pFuncCall
  _ <- pSpaces $ char ';'
  case t1 of
    Just ty -> pure $ StDot ty f xs
    Nothing -> pure $ StIODot f xs

pDefault :: Parser Case
pDefault = do
  _ <- pSpaces $ string "default"
  caseBody <- pSpaces $ pCurlies pStmt
  pure $
    Case
      { caseOn = [],
        caseBody
      }

pCase :: Parser Case
pCase = do
  _ <- pSpaces $ string "case"
  caseOn <- pSpaces $ pParens $ pPTm `sepBy` char ','
  caseBody <- pSpaces $ pCurlies pStmt
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
  tyFuncArgs <- pFuncArgs -- TODO
  _ <- pSpaces $ string "=>"
  tyFuncRetTy <- pSpaces pPTy
  _ <- pSpaces $ char ')'
  pure $
    PTyFunc
      { tyFuncArgs,
        tyFuncRetTy
      }

pTmDot :: Parser PTm
pTmDot = do
  t1 <- (pSpaces (string "IO") >> pure Nothing) <|> (pSpaces (string "this") >> pure (Just PTmThis)) <|> Just <$> pSpaces pPTm0
  _ <- char '.'
  PTmFuncCall f xs <- pSpaces pFuncCall
  case t1 of
    Just ty -> pure $ PTmDot ty f xs
    Nothing -> pure $ PTmDot PTmIO f xs

pTmDotRec :: Parser PTm
pTmDotRec = do
  t1 <- pSpaces pPTm0
  _ <- char '.'
  t2 <- pSpaces pPTm0
  pure $ PTmDotRec t1 t2

pTyHole :: Parser PTy
pTyHole = pSpaces (char '?') >> pure PTyHole

pPTmThis :: Parser PTm
pPTmThis = pSpaces (string "this") >> pure PTmThis

pPTy :: Parser PTy
pPTy =
  try pPTyBool
    <|> try pPTyNat
    <|> try pPTyTy
    <|> try pPTyUnit
    <|> try pPTyFunc
    <|> try pPTyCustom
    <|> try pPTyPTm
    <|> try pPTyList
    <|> try pTyHole

pPTm1 :: Parser PTm
pPTm1 =
  try pPlusPTm
    <|> try pTmDot
    <|> try pTmDotRec
    <|> try pTmMinus
    <|> try pTmMult
    <|> try pTmDiv
    <|> try pTmMod
    <|> try pTmBEq
    <|> try pTmBLT
    <|> try pTmBAnd
    <|> try pTmBOr
    <|> try pFuncCall
    <|> try pPTmCon
    <|> try pIf
    <|> try pTernary
    <|> try pPTm0

pPTm0 :: Parser PTm
pPTm0 =
  try (pParens pPTm1)
    <|> try pPTmVar
    <|> try pPTmThis
    <|> try pPTmWildCard
    <|> try pNat
    <|> try pBool
    <|> try pTmUnit
    <|> try pTmString
    <|> try pTmNot

pPTm :: Parser PTm
pPTm = pSpaces pPTm1