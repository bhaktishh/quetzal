{-# LANGUAGE NamedFieldPuns #-}
{-# HLINT ignore "Use if" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{- HLINT ignore "Use bimap" -}
{- HLINT ignore "Use second" -}
{- HLINT ignore "Redundant bracket" -}

module PToI where

import qualified Data.Bifunctor
import Data.Char (toLower, toUpper)
import Data.List (nub, unsnoc)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Tuple (swap)
import ITypes
import PTypes

-- ---------------------------------
-- surface level transformations
-- ---------------------------------

trTm :: PTm -> ITm
trTm (PTmNat n) = ITmNat n
trTm (PTmString s) = ITmString s
trTm (PTmPlus t1 t2) =
  let t1' = trTm t1
      t2' = trTm t2
      tS = ITmCon "S"
   in if t1' == ITmNat 1 then tS [t2'] else ITmPlus t1' t2'
trTm (PTmBool b) = ITmBool b
trTm PTmUnit = ITmUnit
trTm (PTmNot t) = ITmNot (trTm t)
trTm (PTmPTy t) = ITmTy (trTy t)
trTm (PTmVar x) = ITmVar x
trTm PTmWildCard = ITmWildCard
trTm (PTmCon x cs) = ITmCon x (map trTm cs)
trTm (PTmFuncCall f args) = ITmFuncCall (trTm f) (map trTm args)
trTm (PTmIf c t e) = ITmIf (trTm c) (trTm t) (trTm e)
trTm (PTmMinus t1 t2) = ITmMinus (trTm t1) (trTm t2)
trTm (PTmMult t1 t2) = ITmMult (trTm t1) (trTm t2)
trTm (PTmDiv t1 t2) = ITmDiv (trTm t1) (trTm t2)
trTm (PTmMod t1 t2) = ITmMod (trTm t1) (trTm t2)
trTm (PTmBEq t1 t2) = ITmBEq (trTm t1) (trTm t2)
trTm (PTmBAnd t1 t2) = ITmBAnd (trTm t1) (trTm t2)
trTm (PTmBOr t1 t2) = ITmBOr (trTm t1) (trTm t2)
trTm (PTmBLT t1 t2) = ITmBLT (trTm t1) (trTm t2)
trTm (PTmList t1 xs) = ITmList (trTy t1) (map trTm xs)
trTm (PTmFunc f) = ITmFunc (trFunc f M.empty) -- TODO
trTm (PTmDot t1 f args) = ITmFuncCall (trTm f) (trTm t1 : map trTm args)
trTm (PTmTernary t1 t2 t3) = convIf (trTm t1) (trTm t2) (trTm t3)
trTm (PTmDotRec a b) = ITmDot (trTm a) (trTm b)
trTm (PTmPair a b) = ITmPair (trTm a) (trTm b)
trTm (PTmThis) = undefined

trBool :: ITm -> ITm
trBool (ITmBLT t1 t2) = ITmFuncCall (ITmVar "isLT") [t1, t2]
trBool (ITmBEq t1 t2) = ITmFuncCall (ITmVar "decEq") [t1, t2]
trBool (ITmBAnd t1 t2) = ITmBAnd (trBool t1) (trBool t2)
trBool (ITmBOr t1 t2) = ITmBOr (trBool t1) (trBool t2)
trBool (ITmNot t) = ITmNot (trBool t)
trBool x = x

trPBool :: PTm -> PTm
trPBool (PTmBLT t1 t2) = PTmFuncCall (PTmVar "isLT") [t1, t2]
trPBool (PTmBEq t1 t2) = PTmFuncCall (PTmVar "decEq") [t1, t2]
trPBool (PTmBAnd t1 t2) = PTmBAnd (trPBool t1) (trPBool t2)
trPBool (PTmBOr t1 t2) = PTmBOr (trPBool t1) (trPBool t2)
trPBool (PTmNot t) = PTmNot (trPBool t)
trPBool x = x

-- -- takes a function body : Stmt and function itself : Func
-- -- converts into a IFunc body and where clause
-- trFuncBody :: Func -> IFunc
-- trFuncBody f =
--   let x = funcBody f
--       argMap = mapFromFuncArgs (funcArgs f) M.empty
--       args = map (\(AnnParam (ty, str) _) -> (str, ty)) (funcArgs f)
--    in trListStmt f argMap

-- trMonadicFunc :: List Stmt -> Maybe FSM -> M.Map String PTy -> IFunc

trFunc :: Func -> M.Map String ITy -> IFunc
-- when under a run directive, the function is run under the fsm idxm
-- any IO statements must be lifted
-- kvs = fsm map
-- TODO check for directive compliance with func
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff, funcDirective = Just (Directive dsub@(DFSM resTy stTy) (DRun {directiveReturns = (dRet, mrvar), directiveWith, directiveStTrans = (stIn, stOut)}))}) m =
  case funcRetTy == dRet of
    False -> error "return type in function and directive do not match"
    True ->
      let args' = map trAnnParam funcArgs
          outerLHS = ITmFuncCall (ITmVar funcName) (map (ITmVar . getIAnnParamVar) args')
          str = myShowTy resTy ++ "_" ++ myShowTy stTy
          iFuncName = funcName ++ "\'"
          outerRHS = mkFSMExecOuterBody funcName directiveWith str
          m' = M.insert (fst directiveWith) (ITyTm $ trTm (snd directiveWith)) m
          innerLHS = ITmFuncCall (ITmVar iFuncName) (map (ITmVar . getIAnnParamVar) args')
          (db, w) = trMonadListStmt Nothing m' [funcBody] []
          innerRHS = ITmDo db
          f' =
            IFunc
              { iFuncName,
                iFuncArgs = args',
                iFuncBody = [(innerLHS, innerRHS)],
                iFuncRetTy = ITyApp (ITyVar ("Idxm" ++ str)) [ITmTy (trTy funcRetTy), trTm stIn, mkStOut stOut mrvar],
                iWhere = w
              }
          iFuncRetTy = ITyIO (trTy funcRetTy)
       in IFunc
            { iFuncName = funcName,
              iFuncArgs = args',
              iFuncBody = [(outerLHS, outerRHS)],
              iFuncRetTy,
              iWhere = [ITmFunc f']
            }
-- for functions with the "action" directive, we should be able to convert "this" in the body
-- TODO also handle when IO
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff, funcDirective = Just directive}) m = undefined
-- effectful IO translation
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff = Just IO, funcDirective}) m = undefined
-- all other functions have no special translation
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff, funcDirective}) m = undefined

-- --            stmt list   argmap              og func  where block  (func, where block)
-- trListStmt :: List Stmt -> M.Map String PTy -> Func -> List ITm -> (ITm, List ITm)
-- trListStmt [StSkip] _ _ _ = error "cannot end with skip i think"
-- trListStmt (StSkip : xs) m f i = trListStmt xs m f i
-- trListStmt [] _ _ i = (ITmUnit, i)
-- trListStmt (StBlock s : xs) m f i = trListStmt (s ++ xs) m f i
-- trListStmt [StReturn t] _ _ i = (trTm t, i)
-- trListStmt (StReturn _ : _) _ _ _ = error "return should be the last statement in the block"
-- trListStmt (StIf t s1 s2 : xs) m f i =
--   let (t1, i1) = trListStmt (s1 : xs) m f i
--       (t2, i2) = trListStmt (s2 : xs) m f (i ++ i1)
--    in (ITmIf (trTm t) t1 t2, i ++ i2)
-- trListStmt (StEIf t s1 s2 : xs) m f i =
--   let (t1, i1) = trListStmt (s1 : xs) m f i
--       (t2, i2) = trListStmt (s2 : xs) m f (i ++ i1)
--    in (convIf (trTm t) t1 t2, i ++ i2)
-- trListStmt (StDeclAssign (Just ty) x t : xs) m f i =
--   let (t', i') = trListStmt xs (M.insert x ty m) f i
--    in (ITmLet x (Just (trTy ty)) (trTm t) t', i ++ i')
-- trListStmt (StDeclAssign Nothing x t : xs) m f i =
--   let (t', i') = trListStmt xs (M.insert x PTyHole m) f i
--    in (ITmLet x Nothing (trTm t) t', i ++ i')
-- trListStmt (StAssign x t : xs) m f i =
--   let (t', i') = trListStmt xs m f i
--    in (ITmLet x (trTy <$> M.lookup x m) (trTm t) t', i ++ i')
-- trListStmt (StWhile t s : xs) m f i =
--   let (body, innerName, innerParams) = defOuter (funcName f) (funcArgs f ++ map ((`AnnParam` True) . swap) (M.toList m)) (length i)
--       innerFunc = defInner t s innerName (funcRetTy f) xs innerParams False
--    in (\(x, y) -> (x, ITmFunc (trFunc innerFunc) : y)) (trBody body f)
-- trListStmt (StEWhile t s : xs) m f i =
--   let (body, innerName, innerParams) = defOuter (funcName f) (funcArgs f ++ map ((`AnnParam` True) . swap) (M.toList m)) (length i)
--       innerFunc = defInner t s innerName (funcRetTy f) xs innerParams True
--    in (\(x, y) -> (x, ITmFunc (trFunc innerFunc) : y)) (trBody body f)
-- trListStmt (StSwitch Switch {switchOn, cases, defaultCase} : xs) m f i =
--   let def = case defaultCase of
--         Nothing -> []
--         Just c -> [c]
--       tmp = map (\(Case {caseOn, caseBody}) -> (if null caseOn then replicate (length switchOn) ITmWildCard else map trTm caseOn, trListStmt (caseBody : xs) m f i)) (cases ++ def)
--       branches = map (\(tm, (st, i)) -> ((tm, st), i)) tmp
--    in ( ITmMatch
--           (map trTm switchOn)
--           (map fst branches),
--         i ++ concatMap snd branches
--       )
-- trListStmt (StDot x g args : xs) m f i =
--   let (t', i') = trListStmt xs m f i
--       var = if myShowTm x == "IO" then "_" else myShowTm x
--    in (ITmLet var Nothing (ITmFuncCall (trTm g) (trTm x : map trTm args)) t', i ++ i')
-- trListStmt (StIODot g args : xs) _ _ _ = error "cannot have IOFunc in non IO effect function"

trTy :: PTy -> ITy
trTy PTyNat = ITyNat
trTy PTyBool = ITyBool
trTy PTyUnit = ITyUnit
trTy PTyTy = ITyTy
trTy PTyFunc {tyFuncArgs, tyFuncRetTy} = ITyFunc $ map (\(x, y) -> (Just y, trTy x)) tyFuncArgs ++ [(Nothing, trTy tyFuncRetTy)]
trTy PTyCustom {tyName, tyParams} = ITyApp (ITyVar tyName) (map trTm tyParams)
trTy (PTyPTm t) = ITyTm (trTm t)
trTy (PTyList t) = ITyList (trTy t)
trTy PTyHole = ITyHole
trTy (PTyPair x y) = ITyPair (trTy x) (trTy y)

trDecl :: Decl -> IDecl
trDecl (PTy tydecl) = ITy $ trTyDecl tydecl
trDecl (Rec recdecl) = IRec $ trRecDecl recdecl

trTyDecl :: TyDecl -> ITyDecl
trTyDecl
  TyDecl
    { tyDeclName,
      tyDeclParams,
      tyDeclConstructors
    } =
    ITyDecl
      { iTyDeclName = tyDeclName,
        iTyDeclParams = map trAnnParam tyDeclParams,
        iTyDeclConstructors = map trConstructor tyDeclConstructors
      }

trRecDecl :: RecDecl -> IRecDecl
trRecDecl
  RecDecl
    { recDeclName,
      recDeclParams,
      recDeclFields
    } =
    IRecDecl
      { iRecDeclName = recDeclName,
        iRecDeclParams = map trAnnParam recDeclParams,
        iRecDeclConstructor = "Mk" ++ recDeclName,
        iRecDeclFields = map (trAnnParam . (`AnnParam` True)) recDeclFields
      }

-- TODO decide what to do with resConc
-- outerFuncName    initVar, initCall  <resTy>_<stTy>
mkFSMExecOuterBody :: String -> (String, PTm) -> String -> ITm
mkFSMExecOuterBody f (initVar, initCall) str =
  let runFunc = "run" ++ str
      (resVal, resConc) = (ITmVar "resVal", ITmVar "resConc")
      f' = f ++ "\'"
   in ITmDo
        [ ITmDoLet initVar Nothing (trTm initCall),
          -- todo change for ioref
          ITmDoBind [ITmVar "resVal", ITmVar "resConc"] (ITmFuncCall (ITmVar runFunc) [ITmVar initVar, ITmVar f']),
          ITmDoPure resVal
        ]

-- TODO need trMonadListStmt like there is trIOBody, for an FSM translation with binds etc correctly
-- and handling of "this"

mkUpper :: PTm -> PTm
mkUpper (PTmVar (x : xs)) = PTmVar $ toUpper x : xs
mkUpper (PTmCon (x : xs) args) = PTmCon (toUpper x : xs) args
mkUpper x = x

-- trMonadListStmt :: Maybe Directive -> List Stmt -> M.Map String PTy ->

unblock :: Stmt -> List Stmt
unblock (StBlock s) = s
unblock x = [x]

-- Maybe String : if Nothing then IO monad, if something then var to update under Some
trMonadListStmt :: Maybe String -> M.Map String ITy -> List Stmt -> List ITm -> (List ITmDo, List ITm)
trMonadListStmt _ _ [] w = ([], w)
trMonadListStmt _ _ (StBlock _ : _) w = error "no TL block inside block allowed"
trMonadListStmt mstr ctx (StDeclAssign mty lhs rhs : xs) w =
  let imty = trTy <$> mty
      (rest, w') = trMonadListStmt Nothing (M.insert lhs (fromMaybe ITyHole imty) ctx) xs w
   in case rhs of
        PTmDot x f args ->
          let tm = case (mstr, x) of
                (Nothing, PTmIO) -> ITmDoBind [ITmVar lhs] (ITmFuncCall (trTm f) (map trTm args))
                (Just "this", PTmThis) -> ITmDoBind [ITmVar lhs, ITmVar "this"] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                (Just str, PTmVar v) | str == v -> ITmDoBind [ITmVar lhs, ITmVar str] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                (_, _) -> error "incorrect use of dot notation"
           in (tm : rest, w ++ w')
        _ ->
          let tm = ITmDoLet lhs imty (trTm rhs)
           in (tm : rest, w ++ w')
trMonadListStmt mstr ctx (StAssign var tm : xs) w = case (M.lookup var ctx) of
  Nothing -> error "assign without declare"
  Just ty ->
    let (rest, w') = trMonadListStmt mstr ctx xs w
     in case tm of
          PTmDot x f args ->
            let itm = case (mstr, x) of
                  (Nothing, PTmIO) -> ITmDoBind [ITmVar var] (ITmFuncCall (trTm f) (map trTm args))
                  (Just "this", PTmThis) -> ITmDoBind [ITmVar var, ITmVar "this"] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                  (Just str, PTmVar v) | str == v -> ITmDoBind [ITmVar var, ITmVar str] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                  (_, _) -> error "incorrect use of dot notation"
             in (itm : rest, w ++ w')
          _ ->
            let itm = ITmDoLet var (Just ty) (trTm tm)
             in (itm : rest, w ++ w')
trMonadListStmt _ _ [StReturn tm] w = ([ITmDoPure (trTm tm)], w)
trMonadListStmt mstr ctx (StDot x f args : xs) w =
  let x' = trTm x
      itm = ITmDoBind [ITmWildCard, x'] (ITmFuncCall (trTm f) (x' : map trTm args))
      (rest, w') = trMonadListStmt mstr ctx xs w
   in (itm : rest, w ++ w')
trMonadListStmt mstr ctx (StIODot f args : xs) w =
  let itm = ITmDoBind [ITmWildCard] (ITmFuncCall (trTm f) (map trTm args))
      (rest, w') = trMonadListStmt mstr ctx xs w
   in (itm : rest, w ++ w')
trMonadListStmt mstr ctx (StIf c t e : xs) w =
  let (t', wt) = trMonadListStmt mstr ctx (unblock t ++ xs) w
      (e', we) = trMonadListStmt mstr ctx (unblock t ++ xs) w
   in ([ITmDoIf (trTm c) (ITmDo (t')) (ITmDo e')], wt ++ we)
trMonadListStmt mstr ctx (StEIf c t e : xs) w =
  let (t', wt) = trMonadListStmt mstr ctx (unblock t ++ xs) w
      (e', we) = trMonadListStmt mstr ctx (unblock e ++ xs) w
      itm = convIOIf (trTm c) (ITmDo t') (ITmDo e')
   in ([itm], wt ++ we)
trMonadListStmt mstr ctx (StSwitch (Switch switchOn cases defaultCase) : xs) w = undefined
trMonadListStmt mstr ctx (StWhile condition body : xs) w = undefined
trMonadListStmt mstr ctx (StEWhile condition body : xs) w = undefined
trMonadListStmt mstr ctx (StSkip : xs) w = trMonadListStmt mstr ctx xs w
trMonadListStmt _ _ (StReturn _ : _) _ = error "return must be last statement in block"

-- trMonadListStmt b m (StSwitch sw : xs) w = undefined
-- trMonadListStmt b m (StSkip : xs) = trMonadListStmt xs
-- trMonadListStmt b m (StDot PTmThis f args : xs) = ITmDoBind ["_"] (ITmFuncCall (trTm $ mkUpper f) (map trTm args)) : trMonadListStmt b xs
-- trMonadListStmt b m (StIODot f args : xs) = ITmDoBind ["_"] (ITmFuncCall (ITmVar "Lift") (trTm f : map trTm args)) : trMonadListStmt b xs
-- trMonadListStmt _ _ _ = error "invalid case"

-- TODO add a specific case for functions with a directive "run"
-- directives action and init will be handled by the global FSM created
-- trFunc :: M.Map DirectiveSub FSM -> Func -> IFunc
-- trFunc kvs f@Func {funcDirective = Just (Directive (DFSM resTy stTy) (DRun {directiveReturns = (rty, rvar), directiveWith, directiveStTrans = (stIn, stOut)}))} =
--   let newName = funcName f ++ "\'"
--       iStOut = case rvar of
--         Nothing -> ITmFuncCall (ITmVar "const") [trTm stOut]
--         Just v -> ITmLam [ITmVar v] (trTm stOut)
--       -- (b, w) = if (funcEff f == Just IO) then trIOBody (funcBody f) (f {funcName = newName} )else trBody (funcBody f) (f {funcName = newName})
--       f' = trFuncBody kvs f {funcName = newName} (mapFromFuncArgs (funcArgs f) M.empty)
--       -- IFunc
--       --   { iFuncName = newName,
--       --     iFuncRetTy = ITyApp (myShowTy resTy) [ITmTy $ trTy (funcRetTy f), trTm stIn, iStOut],
--       --     iFuncArgs = map trAnnParam (funcArgs f),
--       --     iFuncBody = [(ITmVar newName, b)],
--       --     iWhere = w
--       --   }
--       -- todo add support for arguments
--       outerLHS = ITmFuncCall (ITmVar $ funcName f) []
--       outerRHS = mkFSMExecOuter newName directiveWith resTy
--    in IFunc
--         { iFuncName = funcName f,
--           iFuncArgs = map trAnnParam (funcArgs f),
--           iFuncBody = [(outerLHS, outerRHS)],
--           iFuncRetTy = trTy $ funcRetTy f,
--           iWhere = [ITmFunc f']
--         }
-- trFunc f@Func {funcName, funcRetTy, funcArgs, funcBody, funcEff = Just IO, funcDirective} =
--   let (b, w) = trIOBody funcBody f
--       iFuncArgs = map trAnnParam funcArgs
--    in IFunc
--         { iFuncName = funcName,
--           iFuncRetTy = ITyIO (trTy funcRetTy),
--           iFuncArgs,
--           iFuncBody = [(ITmCon funcName (map (ITmVar . getIAnnParamVar) iFuncArgs), b)],
--           iWhere = w
--         }
-- trFunc kvs f =
--   trFuncBody kvs f (mapFromFuncArgs (funcArgs f) M.empty)

-- let (b, w) = trBody funcBody f
--     iFuncArgs = map trAnnParam funcArgs
--  in IFunc
--       { iFuncName = funcName,
--         iFuncRetTy = trTy funcRetTy,
--         iFuncArgs,
--         iFuncBody = [(ITmCon funcName (map (ITmVar . getIAnnParamVar) iFuncArgs), b)],
--         iWhere = w
--       }

-- trIOBody :: Stmt -> Func -> (ITm, List ITm)
-- trIOBody x f =
--   -- make map of args from varname to ty
--   let argMap = mapFromFuncArgs (funcArgs f) M.empty
--       args = map (\(AnnParam (ty, str) _) -> (str, ty)) (funcArgs f)
--    in case x of
--         StBlock ls -> (Data.Bifunctor.first ITmDo) $ trListIOStmt ls argMap args f []
--         _ -> (Data.Bifunctor.first ITmDo) $ trListIOStmt [x] argMap args f []

-- for functions with an IO effect
--            stmt list   argmap              arglist               og func  where block  (func, where block)
-- trListIOStmt :: List Stmt -> M.Map String PTy -> List (String, PTy) -> Func -> List ITm -> (List ITmDo, List ITm)
-- trListIOStmt [StReturn t] _ _ _ i = ([ITmDoPure (trTm t)], i)
-- trListIOStmt (StReturn _ : _) _ _ _ _ = error "return should be the last statement in the block"
-- trListIOStmt (StDeclAssign mt v (PTmDot x g args) : xs) m ls f i =
--   let ty = Data.Maybe.fromMaybe PTyHole mt
--       ity = mt >>= Just . trTy
--       (t', i') = trListIOStmt xs (M.insert v ty m) (ls ++ [(v, ty)]) f i
--    in case funcRun f of
--         Just run -> (ITmDoBind [v, myShowTm x] (ITmFuncCall (ITmVar run) (trTm x : trTm (mkUpper g) : map trTm args)) : t', i ++ i')
--         Nothing -> (ITmDoBind [v, myShowTm x] (ITmFuncCall (trTm g) (trTm x : map trTm args)) : t', i ++ i')
-- trListIOStmt (StDeclAssign mt v t : xs) m ls f i =
--   let ty = Data.Maybe.fromMaybe PTyHole mt
--       ity = mt >>= Just . trTy
--       (t', i') = trListIOStmt xs (M.insert v ty m) (ls ++ [(v, ty)]) f i
--    in ((ITmDoLet v ity (trTm t) : t'), i ++ i')
-- trListIOStmt (StAssign v (PTmDot x g args) : xs) m ls f i =
--   let (t', i') = trListIOStmt xs m ls f i
--    in case funcRun f of
--         Just run -> (ITmDoBind [v, myShowTm x] (ITmFuncCall (ITmVar run) (trTm x : trTm (mkUpper g) : map trTm args)) : t', i ++ i')
--         Nothing -> (ITmDoBind [v, myShowTm x] (ITmFuncCall (trTm g) (trTm x : map trTm args)) : t', i ++ i')
-- trListIOStmt (StAssign x t : xs) m ls f i =
--   let (t', i') = trListIOStmt xs m ls f i
--    in (ITmDoLet x (trTy <$> M.lookup x m) (trTm t) : t', i ++ i')
-- trListIOStmt (StDot x g args : xs) m ls f i =
--   let (t', i') = trListIOStmt xs m ls f i
--    in case funcRun f of
--         Just run -> (ITmDoBind [myShowTm x] (ITmFuncCall (ITmVar run) (trTm x : trTm (mkUpper g) : map trTm args)) : t', i ++ i')
--         Nothing -> (ITmDoBind [myShowTm x] (ITmFuncCall (trTm g) (trTm x : map trTm args)) : t', i ++ i')
-- trListIOStmt (StSwitch Switch {switchOn, cases, defaultCase} : xs) m ls f i =
--   let def = case defaultCase of
--         Nothing -> []
--         Just c -> [c]
--       tmp = map (\(Case {caseOn, caseBody}) -> (if null caseOn then replicate (length switchOn) ITmWildCard else map trTm caseOn, trListIOStmt (caseBody : xs) m ls f i)) (cases ++ def)
--       branches = map (\(tm, (st, i)) -> ((tm, ITmDo st), i)) tmp
--    in ( [ ITmDoCase
--             (map trTm switchOn)
--             (map fst branches)
--         ],
--         i ++ concatMap snd branches
--       )
-- trListIOStmt (StEIf t s1 s2 : xs) m ls f i =
--   let (t1, i1) = trListIOStmt (s1 : xs) m ls f i
--       (t2, i2) = trListIOStmt (s2 : xs) m ls f (i ++ i1)
--       t' = convIOIf (trTm t) (ITmDo t1) (ITmDo t2)
--    in ([t'], i ++ i2)
-- trListIOStmt (StIf t s1 s2 : xs) m ls f i =
--   let (t1, i1) = trListIOStmt (s1 : xs) m ls f i
--       (t2, i2) = trListIOStmt (s2 : xs) m ls f (i ++ i1)
--    in ([ITmDoIf (trTm t) (ITmDo t1) (ITmDo t2)], i ++ i2)
-- trListIOStmt (StBlock x : xs) m ls f i = trListIOStmt (x ++ xs) m ls f i
-- trListIOStmt (StIODot g args : xs) m ls f i =
--   let (t', i') = trListIOStmt xs m ls f i
--    in (ITmDoIO (ITmFuncCall (trTm g) (map trTm args)) : t', i ++ i')
-- trListIOStmt (StSkip : xs) m ls f i = trListIOStmt xs m ls f i
-- trListIOStmt xs m ls f i =
--   let (a, b) = trListStmt xs m ls f i
--    in ([ITmDoPure a], b) -- TODO

-- convIf c t e = ITmMatch [trBool c] [([ITmCon "Yes" [ITmVar "yesprf"]], t), ([ITmCon "No" [ITmVar "noprf"]], e)]

convIOIf :: ITm -> ITm -> ITm -> ITmDo
convIOIf c t e = ITmDoCase [c] [([ITmCon "Yes" [ITmVar "yesprf"]], t), ([ITmCon "No" [ITmVar "noprf"]], e)]

trConstructor :: Constructor -> IConstructor
trConstructor
  Constructor
    { conName,
      conArgs,
      conTy
    } =
    IConstructor
      { iConName = conName,
        iConArgs = map trAnnParam conArgs,
        iConTy = trTy conTy
      }

-- ---------------------------
-- FSM transforms
-- ---------------------------

mkICon :: String -> String
mkICon [] = error "empty constructor"
mkICon (x : xs) = toUpper x : xs

mkIFun :: String -> String
mkIFun [] = error "empty constructor"
mkIFun (x : xs) = toLower x : xs

-- trActionFuncBody :: String -> Stmt -> Stmt
-- trActionFuncBody resource (StReturn tm) = StReturn (PTmPair tm (PTmVar resource))
-- trActionFuncBody resource (StBlock (x : xs)) = trActionFuncBody resource xs

-- trActionFunc :: String -> AnnParam -> Func -> Func
-- trActionFunc name resource (Func {funcName, funcRetTy, funcArgs, funcBody, funcEff, funcRun}) = let
--   funcRetTy' = funcRetTy
--   funcArgs' = funcArgs
--   in
--     undefined

--         stOut  mrvar
mkStOut :: PTm -> Maybe String -> ITm
mkStOut mstOut = maybe (ITmFuncCall (ITmVar "const") [trTm mstOut]) (\var -> ITmLam [ITmVar var] (trTm mstOut))

-- given name of idxm, resource and action
-- TODO translate IORefs
trAction :: String -> Action -> IConstructor
trAction name (Action {actionName, actionRetTy = (rty, mrvar), actionStTrans}) =
  let stIn = trTm (fst actionStTrans)
      stOut = mkStOut (snd actionStTrans) mrvar
   in IConstructor
        { iConName = mkICon actionName,
          iConArgs = [],
          iConTy = ITyApp (ITyVar name) [ITmTy (trTy rty), stIn, stOut]
        }

-- TODO better names for the default constructors

-- run resource (action >>= cont) = do
--    res <- run resource action
--    run store (cont res)
mkRunBind :: String -> String -> String -> (ITm, ITm)
mkRunBind _ funcName resVar =
  let action = ITmVar "action"
      cont = ITmVar "cont"
      run = ITmVar funcName
      resource = ITmVar resVar
   in (ITmFuncCall run [resource, ITmBind action cont], ITmDo [ITmDoBind [ITmVar "res"] (ITmFuncCall run [resource, action]), ITmDoIO (ITmFuncCall run [resource, ITmFuncCall cont [ITmVar "res"]])])

-- run resource (Pure<fsmName> x) = pure x
--         idxmName -> runFuncName -> resourceVar -> (LHS, RHS)
mkRunPure :: String -> String -> String -> (ITm, ITm)
mkRunPure fsmName funcName resVar =
  let x = ITmVar "x"
      vPure = ITmVar $ "Pure" ++ fsmName
      fPure = ITmVar "pure"
      resource = ITmVar resVar
      run = ITmVar funcName
   in (ITmFuncCall run [resource, ITmFuncCall vPure [x]], ITmFuncCall fPure [x])

-- run resource (Lift<fsmName> io) = io
mkRunLift :: String -> String -> String -> (ITm, ITm)
mkRunLift fsmName funcName resVar =
  let resource = ITmVar resVar
      run = ITmVar funcName
      lift = ITmVar $ "Lift" ++ fsmName
      io = ITmVar "io"
   in (ITmFuncCall run [resource, ITmFuncCall lift [io]], io)

-- Pure<fsmName> : (x : ty) -> resTy ty (st x) st
mkConPure :: String -> String -> IConstructor
mkConPure fsmName resTy =
  let st = ITmVar "st"
      x = ITmVar "x"
      ty = ITmVar "ty"
   in IConstructor
        { iConName = "Pure" ++ fsmName,
          iConArgs = [IAnnParam ("x", ITyTm ty) True],
          iConTy = ITyApp (ITyVar resTy) [ty, (ITmFuncCall st [x]), st]
        }

--   Lift : IO ty -> Resource ty st (const st)
mkConLift :: String -> String -> IConstructor
mkConLift fsmName resTy =
  let st = ITmVar "st"
      ty = ITmVar "ty"
      fConst = ITmVar "const"
   in IConstructor
        { iConName = "Lift" ++ fsmName,
          iConArgs = [noAnnIParam (ITyIO (ITyTm ty))],
          iConTy = ITyApp (ITyVar resTy) [ty, st, (ITmFuncCall fConst [st])]
        }

-- (>>=) : Resource a st1 st2 -> ((x : a) -> Resource b (st2 x) st3) -> Resource b st1 st3
mkConBind :: String -> String -> IConstructor
mkConBind _ resTy =
  let st1 = ITmVar "st1"
      st2 = ITmVar "st2"
      st3 = ITmVar "st3"
      a = ITmVar "a"
      b = ITmVar "b"
   in IConstructor
        { iConName = "(>>=)",
          iConArgs = [noAnnIParam (ITyApp (ITyVar resTy) [a, st1, st2]), noAnnIParam (ITyFunc [(Just "x", ITyTm a), (Nothing, ITyApp (ITyVar resTy) [b, (ITmFuncCall st2 [ITmVar "x"])])])],
          iConTy = ITyApp (ITyVar resTy) [b, st1, st3]
        }

-- run resource Action = action resource
mkRunAction :: String -> String -> String -> (ITm, ITm)
mkRunAction fName strRes strAction =
  let resource = ITmVar strRes
      actionFunc = ITmVar (mkIFun strAction)
      actionCon = ITmCon strAction [] -- todo what if args (later)
   in (ITmFuncCall (ITmVar fName) [resource, actionCon], ITmFuncCall actionFunc [resource])

-- str = "<resourceTy>_<stateTy>"
mkRun :: String -> ITy -> ITyDecl -> IFunc
mkRun str concTy decl =
  let idxmName = iTyDeclName decl
      resVar = "resource"
      iFuncName = "run" ++ str
      mcons = map (\f -> f idxmName iFuncName resVar) [mkRunPure, mkRunBind, mkRunLift]
      cons = map (mkRunAction iFuncName resVar . iConName) (iTyDeclConstructors decl)
   in -- iFuncBody = mcons ++ cons
      IFunc
        { iFuncName,
          iFuncArgs = [noAnnIParam concTy, mkITyArg decl],
          iFuncBody = mcons ++ cons,
          iFuncRetTy = ITyIO $ ITyPair (ITyTm (ITmVar "ty")) concTy,
          iWhere = []
        }

trFSM :: FSM -> IFSM
trFSM FSM {resourceTy, stateTy, initCons, actions} =
  let showFSM = myShowTy resourceTy ++ "_" ++ myShowTy stateTy
      idxmName = "Idxm" ++ showFSM
      confuncs = map (trAction idxmName) actions
      iStateTy = trTy stateTy
      idxm' =
        ITyDecl
          { iTyDeclName = idxmName,
            iTyDeclParams = [IAnnParam ("ty", ITyTy) True, noAnnIParam iStateTy, noAnnIParam (ITyFunc [(Nothing, ITyTm (ITmVar "ty")), (Nothing, iStateTy)])],
            -- we dont add the pure,bind,lift constructors here so that they are ignored in mkRun
            iTyDeclConstructors = confuncs
          }
      conc = trTy resourceTy
      run = mkRun showFSM conc idxm'
      idxm = idxm' {iTyDeclConstructors = confuncs ++ map (\f -> f showFSM (tyName resourceTy)) [mkConPure, mkConBind, mkConLift]}
   in IFSM
        { idxm,
          conc,
          run
        }

-- -----------------------------
-- AnnParam and IAnnParam utils
-- -----------------------------

trAnnParam :: AnnParam -> IAnnParam
trAnnParam (AnnParam (ty, str) vis) = IAnnParam (str, trTy ty) vis

getAnnParamVar :: AnnParam -> String
getAnnParamVar (AnnParam (_, str) _) = str

getAnnParamPTy :: AnnParam -> PTy
getAnnParamPTy (AnnParam (ty, _) _) = ty

nubAnnParam :: M.Map String (PTy, Bool) -> List AnnParam -> List AnnParam -> List AnnParam
nubAnnParam _ [] lnew = lnew
nubAnnParam m (x@(AnnParam (ty, v) vis) : xs) lnew = case M.lookup v m of
  Nothing -> nubAnnParam (M.insert v (ty, vis) m) xs (lnew ++ [x])
  Just _ -> nubAnnParam m xs lnew

getIAnnParamVar :: IAnnParam -> String
getIAnnParamVar (IAnnParam (str, _) _) = str

getIAnnParamTy :: IAnnParam -> ITy
getIAnnParamTy (IAnnParam (_, ty) _) = ty

noAnnIParam :: ITy -> IAnnParam
noAnnIParam ty = IAnnParam ("", ty) True

mkITyArg :: ITyDecl -> IAnnParam
mkITyArg ITyDecl {iTyDeclName, iTyDeclParams, iTyDeclConstructors} = noAnnIParam (ITyApp (ITyVar iTyDeclName) (map (ITmVar . getIAnnParamVar) iTyDeclParams))

-- --------------------------
-- automatic generation of decidable equality
-- ----------------------------

-- dependent pattern matching via if statements
convIf :: ITm -> ITm -> ITm -> ITm
convIf c t e = ITmMatch [trBool c] [([ITmCon "Yes" [ITmVar "yesprf"]], t), ([ITmCon "No" [ITmVar "noprf"]], e)]

mapFromFuncArgs :: List AnnParam -> M.Map String PTy -> M.Map String PTy
mapFromFuncArgs [] m = m
mapFromFuncArgs ((AnnParam (ty, var) _) : xs) m = mapFromFuncArgs xs (M.insert var ty m)

mapToAnnParam :: M.Map String PTy -> List AnnParam
mapToAnnParam m = map (\(v, ty) -> AnnParam (ty, v) True) (M.toList m)

defOuter :: String -> List AnnParam -> Int -> (Stmt, String, List AnnParam)
defOuter funcName funcArgs i =
  let funcInner = funcName ++ "_rec" ++ show i
      ps = nubAnnParam M.empty funcArgs []
   in ( StBlock [StReturn (PTmFuncCall (PTmVar funcInner) (nub $ map (PTmVar . getAnnParamVar) ps))],
        funcInner,
        ps
      )

defInner :: PTm -> Stmt -> String -> PTy -> List Stmt -> List AnnParam -> Bool -> Func
defInner condition body fname retty tl ps e =
  let ebdy =
        StSwitch
          Switch
            { switchOn = [trPBool condition],
              cases =
                [ Case
                    { caseOn = [PTmCon "No" [PTmVar "noprf"]],
                      caseBody = StBlock tl
                    },
                  Case
                    { caseOn = [PTmCon "Yes" [PTmVar "yesprf"]],
                      caseBody = StBlock $ body : [StReturn (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) ps))]
                    }
                ],
              defaultCase = Nothing
            }
      bdy = StIf condition (StBlock $ body : [StReturn (PTmFuncCall (PTmVar fname) (map (PTmVar . getAnnParamVar) ps))]) (StBlock tl)
   in Func
        { funcName = fname,
          funcArgs = ps,
          funcRetTy = retty,
          funcBody = if e then ebdy else bdy,
          funcEff = Nothing,
          funcDirective = Nothing
        }

dontDoTheseTypes :: [ITy]
dontDoTheseTypes =
  [ -- ITyNat,
    -- ITyBool,
    -- ITyUnit,
    ITyTy
  ]

inConTyTm :: String -> ITm -> Bool
inConTyTm vname (ITmVar x) = vname == x
inConTyTm vname (ITmCon _ xs) = any (inConTyTm vname) xs
inConTyTm vname (ITmFuncCall _ xs) = any (inConTyTm vname) xs
inConTyTm _ _ = False

inConTy :: String -> ITy -> Bool
inConTy vname (ITyApp _ tms) = any (inConTyTm vname) tms
inConTy vname (ITyTm tm) = inConTyTm vname tm
inConTy _ _ = False

deriveDecEq :: IDecl -> IImplementation
deriveDecEq
  ( ITy
      ( ITyDecl
          { iTyDeclName,
            iTyDeclParams,
            iTyDeclConstructors
          }
        )
    ) =
    case generateCases iTyDeclConstructors of
      Nothing -> error "this type probably does not have decidable equality, soz"
      Just cases ->
        let hasTyTy c = map (\(IAnnParam (v, ty) _) -> (v, ty `notElem` dontDoTheseTypes && not (inConTy v (iConTy c)))) $ filter (\(IAnnParam (_, _) b) -> b) (iConArgs c)
            tms i c = ITmCon (iConName c) (map (\(v, b) -> if b then ITmVar (v ++ i) else ITmVar v) (hasTyTy c))
            implicits = map (\(IAnnParam (v, ty) _) -> IAnnParam (v, ty) False) iTyDeclParams
         in Impl
              { iImplicits = implicits,
                iConstraints = getConstraints iTyDeclParams,
                iSubject = ITmCon iTyDeclName (map (ITmVar . getIAnnParamVar) iTyDeclParams),
                iBody = concatMap (getCases . \(x, y) -> (tms "1" x, tms "2" y)) cases
              }
deriveDecEq
  ( IRec
      ( IRecDecl
          { iRecDeclName,
            iRecDeclParams,
            iRecDeclConstructor,
            iRecDeclFields
          }
        )
    ) =
    let asTyDecl =
          ITyDecl
            { iTyDeclName = iRecDeclName,
              iTyDeclParams = iRecDeclParams,
              iTyDeclConstructors =
                [ IConstructor
                    { iConName = iRecDeclConstructor,
                      iConArgs = iRecDeclFields,
                      iConTy = ITyApp (ITyVar iRecDeclName) (map (ITmVar . getIAnnParamVar) iRecDeclParams)
                    }
                ]
            }
     in deriveDecEq (ITy asTyDecl)

getConstraints :: List IAnnParam -> List ITm
getConstraints [] = []
getConstraints (IAnnParam (v, ITyTy) _ : xs) = ITmCon "DecEq" [ITmVar v] : getConstraints xs
getConstraints (IAnnParam (v, ITyFunc args) _ : xs) = getFuncConstraint v args [] [] : getConstraints xs
getConstraints (_ : xs) = getConstraints xs

getFuncConstraint :: String -> List (Maybe String, ITy) -> List (Maybe String, ITy) -> List String -> ITm
getFuncConstraint fv args acc facc = case unsnoc args of
  Just (xs, x@(Just v, _)) -> getFuncConstraint fv xs (x : acc) (v : facc)
  Just (xs, (Nothing, _)) -> getFuncConstraint fv xs acc facc
  Nothing -> ITmTy (ITyFunc (acc ++ [(Nothing, ITyTm $ ITmCon "DecEq" [ITmFuncCall (ITmVar fv) (map ITmVar facc)])]))

-- args to match on
getCases :: (ITm, ITm) -> List IImplCase
getCases (c1@(ITmCon v1 args1), c2@(ITmCon v2 args2)) = case v1 == v2 of
  True -> case length args1 == length args2 of
    True -> case null args1 of
      True -> [mkCase (c1, c2) [] Nothing (Tm $ ITmCon "Yes" [ITmVar "Refl"])]
      False ->
        let pairedargs = zip args1 args2
         in doEverything v1 [] ([], Nothing) pairedargs
    False -> error "dawg dis is Wrong"
  False -> [mkCase (c1, c2) [] Nothing (Tm noImpossible)]
getCases _ = error "pls no"

noImpossible :: ITm
noImpossible = ITmCon "No" [ITmLam [ITmVar "h"] (ITmMatchImpossible [ITmVar "h"] [ITmCon "Refl" []])]

yesCon :: ITm
yesCon = ITmCon "Yes" [ITmVar "Refl"]

noCon :: String -> ITm
noCon prf = ITmCon "No" [ITmVar prf]

noConPrf :: String -> ITm
noConPrf prf = ITmCon "No" [ITmLam [ITmVar "h"] (ITmFuncCall (ITmVar prf) [ITmMatch [ITmVar "h"] [([ITmCon "Refl" []], ITmCon "Refl" [])]])]

mkCons :: String -> List (ITm, ITm) -> (ITm, ITm)
mkCons c args = (ITmCon c (map fst args), ITmCon c (map snd args))

--              cname     prevargs            curBar with last prf   remaining
doEverything :: String -> List (ITm, ITm) -> (List ITm, Maybe String) -> List (ITm, ITm) -> IImplBody
doEverything cname prevargs (curbar, Nothing) [] = [mkCase (mkCons cname prevargs) curbar Nothing (Tm yesCon)]
doEverything cname prevargs (curbar, Just prf) _ = [mkCase (mkCons cname prevargs) curbar Nothing (Tm $ noConPrf prf)]
doEverything cname prevargs (curbar, Nothing) ((x1, x2) : xs) =
  if x1 == x2
    then doEverything cname (prevargs ++ [(x1, x2)]) (curbar, Nothing) xs
    else
      let yesCase = doEverything cname (prevargs ++ [(x1, x1)]) (curbar ++ [yesCon], Nothing) xs
          noCase = mkCase (mkCons cname (prevargs ++ [(x1, x2)] ++ xs)) (curbar ++ [noCon "prf"]) Nothing (Tm $ noConPrf "prf")
       in [mkCase (mkCons cname (prevargs ++ [(x1, x2)] ++ xs)) curbar (Just (ITmFuncCall (ITmVar "decEq") [x1, x2])) (Nest (yesCase ++ [noCase]))]

mkCase :: (ITm, ITm) -> List ITm -> Maybe ITm -> IImplCaseBody -> IImplCase
mkCase iArgs iBarArgs iWith iCaseBody =
  IImplCase
    { iArgs,
      iWith,
      iBarArgs,
      iCaseBody
    }

-- takes in a list of constructors, returns the constructor pairs for each case
generateCases :: List IConstructor -> Maybe (List (IConstructor, IConstructor))
generateCases [] = Just []
generateCases [x] = Just [(x, x)]
generateCases (x : y : xs) =
  let xfst = (x, x) : map (x,) (filter (\x' -> tySame (iConTy x') (iConTy x)) (y : xs))
      xfst' = if tySame (iConTy y) (iConTy x) then xfst ++ [(y, x)] else xfst
   in (xfst' ++) <$> (if null xs then Just [(y, y)] else generateCases (y : xs))

tySame :: ITy -> ITy -> Bool
tySame (ITyApp a xs) (ITyApp b ys) = a == b && all tmSame (zip xs ys)
tySame (ITyTm t) (ITyTm u) = tmSame (t, u)
tySame (ITyList t) (ITyList u) = tySame t u
tySame (ITyFunc _) _ = False
tySame _ (ITyFunc _) = False
tySame x y = x == y

tmSame :: (ITm, ITm) -> Bool
tmSame (ITmTy t1, ITmTy t2) = tySame t1 t2
tmSame (ITmCon a xs, ITmCon b ys) = a == b && all tmSame (zip xs ys)
tmSame (ITmList t xs, ITmList u ys) = tySame t u && all tmSame (zip xs ys)
tmSame (ITmVar _, _) = True
tmSame (_, ITmVar _) = True
tmSame (x, y) = x == y