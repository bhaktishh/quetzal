module Main where

import qualified Data.Map as M
import ITypes
import PToI
import PTypes
import Parse
import System.Environment (getArgs)
import Text.Megaparsec (parse, parseTest, runParser)
import Unparse

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
  [inpf, outpf] <- getArgs
  processFile inpf outpf

-- -- parsing utils
parseFromFile p file = runParser p file <$> readFile file

processFile :: String -> String -> IO ()
processFile inpf outpf = do
  x <- readFile inpf
  case parse pProg "" x of
    Left _ -> error "wtf"
    Right prg' -> do
      let kvs = foldr mkFSMs M.empty (getFuncs prg')
          prg = prg' ++ (PFSM <$> M.elems kvs)
          iprg = IIImport "Decidable.Equality" : map trProgEl prg
      writeIdris iprg outpf

trProgEl :: ProgEl -> IProgEl
trProgEl (PFunc f) = IIFunc $ trFunc f M.empty
trProgEl (PDecl x) = IIDecl $ trDecl x
trProgEl (PImport x) = IIImport x
trProgEl (PFSM fsm) = IIFSM $ trFSM fsm

writeIdris :: IProg -> String -> IO ()
writeIdris p fpath = writeFile fpath (unparse p)
