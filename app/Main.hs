module Main where

import ITypes
import PToI
import PTypes
import Parse
import Text.Megaparsec (parse, runParser)
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
main = error "idk"

-- -- parsing utils
parseFromFile p file = runParser p file <$> readFile file

processFile :: String -> IO ()
processFile file = do
  x <- readFile file
  case parse pProg "" x of
    Left _ -> error "wtf"
    Right tm -> writeIdris (map doFuncs tm) "files/test.idr"

doFuncs :: ProgEl -> IProgEl
doFuncs (PFunc f) = IIFunc $ trFunc f
doFuncs (PDecl x) = IIDecl $ trDecl x
doFuncs (PImport x) = IIImport x
doFuncs (PFSM fsm) = IIFSM $ trFSM fsm 

writeIdris :: IProg -> String -> IO ()
writeIdris p fpath = writeFile fpath (unparse p)
