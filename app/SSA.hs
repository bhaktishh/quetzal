{-# LANGUAGE NamedFieldPuns #-}

module SSA where

import PTypes

-- a mystery tool for later

-- renameVarStmt :: String -> String -> Stmt -> Stmt
-- renameVarStmt from to stmt = case stmt of
--   Assign var tm -> Assign var (renameVarTm from to tm)
--   PDecl ty var -> Decl ty var
--   DeclAssign ty var tm -> DeclAssign ty var (renameVarTm from to tm)
--   PTmReturn tm -> Return (renameVarTm from to tm)
--   PTMBlank -> Blank
--   Switch {switchOn, cases} ->
--     Switch
--       { switchOn = map (renameVarTm from to) switchOn,
--         cases = map (renameVarCase from to) cases
--       }

-- renameVarCase :: String -> String -> Case -> Case
-- renameVarCase from to c =
--   c
--     { caseOn = map (renameVarTm from to) (caseOn c),
--       caseBody = map (renameVarStmt from to) (caseBody c)
--     }

-- renameVarTm :: String -> String -> Tm -> Tm
-- renameVarTm from to tm = case tm of
--   TmPlus t1 t2 -> TmPlus (renameVarTm from to t1) (renameVarTm from to t2)
--   TmFunctionCall f tms -> TmFunctionCall f (map (renameVarTm from to) tms)
--   TmCon c tms -> TmCon c (map (renameVarTm from to) tms)
--   _ -> tm
