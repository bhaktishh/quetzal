module Main where

import ITypes
import PToI
import PTypes
import Parse
import Text.Megaparsec (parse, runParser)
import Unparse
import System.Environment (getArgs)
import qualified Data.Map as M

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
    Right (tm, kvs) -> do 
      writeIdris (map (doFuncs kvs) tm) outpf 

doFuncs :: M.Map DirectiveSub FSM -> ProgEl -> IProgEl
doFuncs kvs (PFunc f) = IIFunc $ trFunc kvs f M.empty
doFuncs _ (PDecl x) = IIDecl $ trDecl x
doFuncs _ (PImport x) = IIImport x
doFuncs _ (PFSM fsm) = IIFSM $ trFSM fsm

writeIdris :: IProg -> String -> IO ()
writeIdris p fpath = writeFile fpath (unparse p)
