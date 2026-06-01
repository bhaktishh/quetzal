{-# LANGUAGE LambdaCase #-}

module Main where

import Data.List (partition)
import qualified Data.Map as M
import Data.Maybe
import ITypes
import PToI
import PTypes
import Parse
import Text.Megaparsec (errorBundlePretty, parse, parseTest, runParser)
import System.Environment (getArgs)
import Unparse
import Data.List (uncons)
import System.Environment (getArgs)

-- TODO: change many, some, satisfy to takeWhileP and takeWhile1P for efficiency
-- is there a way i can add a list of variables and types to carry around? or should that be a second pass
-- how many passes is too many passes
-- also shouldn't idris handle all that
-- maybe idris shouldn't maybe this should have a dependent typechecker of its own

-- variables must begin with a lowercase letter
-- type metavariables must be all uppercase
-- type names and type constructor names must begin with an uppercase letter
-- non parameterized types must include "<>"

main :: IO ()
main = do
    args <- getArgs
    case uncons args of
        Nothing -> error "Usage: quetzal-exe <.qt file> <.idr file>"
        Just (inpf, outpf) -> processFile inpf outpf

-- -- parsing utils
parseFromFile p file = runParser p file <$> readFile file

processFile :: String -> String -> IO ()
processFile inpf outpf = do
  x <- readFile inpf
  case parse pProg "" x of
    Left err -> putStr . errorBundlePretty $ err
    Right prg' -> do
      let kvs = foldr mkFSMs M.empty (getFuncs prg')
          prg = prg' ++ (PFSM <$> M.elems kvs)
          iprg = IIImport "Decidable.Equality" : mkProgEls prg ([], [], [], [])
      writeIdris iprg outpf

-- args     og list       (imports, (declaration, maybe deceq), functions, functions w directives)
mkProgEls :: [ProgEl] -> ([IProgEl], [(IProgEl, Maybe IProgEl)], [IProgEl], [IProgEl]) -> [IProgEl]
mkProgEls [] (is, ds, fs, fds) =
  let ds' = foldr (\(dec, mimp) acc -> dec : maybeToList mimp ++ acc) [] ds
   in is ++ ds' ++ fs ++ fds
mkProgEls (PFSM fsm : xs) (is, ds, fs, fds) =
  let (decl, frun) = trFSM fsm
   in mkProgEls xs (is, ds ++ [(IIDecl (ITy decl), Nothing)], fs ++ [IIFunc frun], fds)
mkProgEls (PImport str : xs) (is, ds, fs, fds) = mkProgEls xs (is ++ [IIImport str], ds, fs, fds)
mkProgEls (PDecl d : xs) (is, ds, fs, fds) =
  let d' = trDecl d
   in mkProgEls xs (is, ds ++ [(IIDecl d', Just (IIImplementation $ deriveDecEq d'))], fs, fds)
mkProgEls (PFunc f : xs) (is, ds, fs, fds) = case funcDirective f of
  Just (Directive _ (DRun {})) -> mkProgEls xs (is, ds, fs, fds ++ [IIFunc (trFunc f M.empty)])
  _ -> mkProgEls xs (is, ds, fs ++ [IIFunc (trFunc f M.empty)], fds)

writeIdris :: IProg -> String -> IO ()
writeIdris p fpath = writeFile fpath (unparse p)
