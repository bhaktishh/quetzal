{-# LANGUAGE NamedFieldPuns #-}
{-# HLINT ignore "Use if" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module PToI where

import qualified Data.Bifunctor
import Data.Char (toLower, toUpper)
import Data.List (nub, nubBy, unsnoc)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isNothing, maybeToList)
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
trTm (PTmDot t1 f args) = ITmFuncCall (trTm f) (trTm t1 : map trTm args)
trTm (PTmTernary t1 t2 t3) = convIf (trTm t1) (trTm t2) (trTm t3)
trTm (PTmDotRec a b) = ITmDot (trTm a) (trTm b)
trTm (PTmPair a b) = ITmPair (trTm a) (trTm b)
trTm PTmThis = ITmVar "this"
trTm PTmIO = ITmVar "IO"

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

trFunc :: Func -> M.Map String ITy -> IFunc
-- when under a run directive, the function is run under the fsm idxm
-- any IO statements must be lifted
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff, funcDirective = d@(Just (Directive _ (DRun {directiveReturns = (dRet, mrvar), directiveWith, directiveStTrans = (stIn, stOut)})))}) m =
  if funcRetTy == dRet
    then
      ( let args' = map trAnnParam funcArgs
            outerLHS = ITmFuncCall (ITmVar funcName) (map (ITmVar . getIAnnParamVar) args')
            str = fsmName d
            iFuncName = funcName ++ "\'"
            outerRHS = mkFSMExecOuterBody funcName directiveWith str
            m' = M.insert "this" (ITyTm $ trTm directiveWith) m
            innerLHS = ITmFuncCall (ITmVar iFuncName) (map (ITmVar . getIAnnParamVar) args')
            (db, w) = trMonadListStmt f (funcDirective f) m' (unblock funcBody) []
            innerRHS = ITmDo db
            f' =
              IFunc
                { iFuncName,
                  iFuncArgs = args',
                  iFuncBody = [(innerLHS, innerRHS)],
                  iFuncRetTy = ITyApp (ITyVar ("Idxm" ++ str)) [ITmTy (trTy funcRetTy), trTm stIn, mkStOut stOut mrvar],
                  iWhere = w
                }
         in IFunc
              { iFuncName = funcName,
                iFuncArgs = args',
                iFuncBody = [(outerLHS, outerRHS)],
                iFuncRetTy = ITyIO (trTy funcRetTy),
                iWhere = [ITmFunc f']
              }
      )
    else error "return type in function and directive do not match"
-- functions with action directives
-- take in and return concrete resource
-- TODO return mdir
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff, funcDirective = d@(Just (Directive (DFSM resTy _) (DAction _ _)))}) m =
  let iResTy = trTy resTy
      args' = IAnnParam ("this", iResTy) True : map trAnnParam funcArgs
      iFuncRetTy = maybe (ITyPair (trTy funcRetTy) iResTy) (const (ITyIO (ITyPair (trTy funcRetTy) iResTy))) funcEff
      fLHS = ITmFuncCall (ITmVar funcName) (map (ITmVar . getIAnnParamVar) args')
      (fRHS, w) = trMonadListStmt f d m (unblock funcBody) []
   in IFunc
        { iFuncName = funcName,
          iFuncArgs = args',
          iFuncBody = [(fLHS, ITmDo fRHS)],
          iFuncRetTy,
          iWhere = w
        }
-- IO and functions with no effect
trFunc f@(Func {funcName, funcArgs, funcBody, funcRetTy, funcEff, funcDirective}) m =
  let args' = map trAnnParam funcArgs
      fLHS = ITmFuncCall (ITmVar funcName) (map (ITmVar . getIAnnParamVar) args')
      (fRHS, w) = maybe (trListStmt f m (unblock funcBody) []) (const (let (rhs, w') = trMonadListStmt f Nothing m (unblock funcBody) [] in (ITmDo rhs, w'))) funcEff
   in IFunc
        { iFuncName = funcName,
          iFuncArgs = args',
          iFuncBody = [(fLHS, fRHS)],
          iFuncRetTy = if isNothing funcEff then trTy funcRetTy else ITyIO (trTy funcRetTy),
          iWhere = w
        }

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
    { recDeclTyName,
      recDeclConName,
      recDeclParams,
      recDeclFields
    } =
    IRecDecl
      { iRecDeclName = recDeclTyName,
        iRecDeclParams = map trAnnParam recDeclParams,
        iRecDeclConstructor = recDeclConName,
        iRecDeclFields = map (trAnnParam . (`AnnParam` True)) recDeclFields
      }

-- TODO decide what to do with resConc
-- outerFuncName    initVar, initCall  <resTy>_<stTy>
mkFSMExecOuterBody :: String -> PTm -> String -> ITm
mkFSMExecOuterBody f initCall str =
  let runFunc = "run" ++ str
      (resVal, resConc) = (ITmVar "resVal", ITmVar "resConc")
      f' = f ++ "\'"
   in ITmDo
        [ ITmDoLet "this" Nothing (trTm initCall),
          -- todo change for ioref
          ITmDoBind [resVal, resConc] (ITmFuncCall (ITmVar runFunc) [ITmVar "this", ITmVar f']),
          ITmDoPure resVal
        ]

mkUpper :: PTm -> PTm
mkUpper (PTmVar (x : xs)) = PTmVar $ toUpper x : xs
mkUpper (PTmCon (x : xs) args) = PTmCon (toUpper x : xs) args
mkUpper (PTmFuncCall t []) = mkUpper t
mkUpper x = x

unblock :: Stmt -> List Stmt
unblock (StBlock s) = s
unblock x = [x]

-- args      og func  ctx map             body         where        (body, where)
trListStmt :: Func -> M.Map String ITy -> List Stmt -> List ITm -> (ITm, List ITm)
trListStmt _ _ [StReturn t] w = (trTm t, w)
trListStmt _ _ [] w = (ITmUnit, w)
trListStmt _ _ (StBlock _ : _) _ = error "no TL block inside block allowed"
trListStmt f ctx (StDeclAssign mty lhs rhs : xs) w =
  let (rest, w') = trListStmt f (M.insert lhs (maybe ITyHole trTy mty) ctx) xs w
   in (ITmLet lhs (trTy <$> mty) (trTm rhs) rest, w')
trListStmt f ctx (StSkip : xs) w = trListStmt f ctx xs w
trListStmt _ _ (StReturn _ : _) _ = error "return should be the last statement in the block"
trListStmt f ctx (StIf t s1 s2 : xs) w =
  let (t1, w1) = trListStmt f ctx (unblock s1 ++ xs) w
      (t2, w2) = trListStmt f ctx (unblock s2 ++ xs) w
   in (ITmIf (trTm t) t1 t2, nub (w1 ++ w2))
trListStmt f ctx (StEIf t s1 s2 : xs) w =
  let (t1, w1) = trListStmt f ctx (unblock s1 ++ xs) w
      (t2, w2) = trListStmt f ctx (unblock s2 ++ xs) w
   in (convIf (trTm t) t1 t2, nub (w1 ++ w2))
trListStmt f ctx (StAssign x t : xs) w =
  let (t', w') = trListStmt f ctx xs w
   in (ITmLet x (M.lookup x ctx) (trTm t) t', w')
trListStmt f ctx (StDot x g args : xs) w =
  let (t', w') = trListStmt f ctx xs w
   in (ITmLet (myShowTm x) Nothing (ITmFuncCall (trTm g) (trTm x : map trTm args)) t', w')
trListStmt f ctx (StWhile condition body : xs) w = trWhile f ctx condition body xs w False
trListStmt f ctx (StEWhile condition body : xs) w = trWhile f ctx condition body xs w True
trListStmt f ctx (StSwitch (Switch {switchOn, cases, defaultCase}) : xs) w =
  let tmp = map (\(Case caseOn caseBody) -> (if null caseOn then replicate (length switchOn) ITmWildCard else map trTm caseOn, trListStmt f ctx (unblock caseBody ++ xs) w)) (cases ++ maybeToList defaultCase)
      branches = map (\(caseOn, (itm, w')) -> ((caseOn, itm), w')) tmp
   in (ITmMatch (map trTm switchOn) (map fst branches), concatMap snd branches)

-- returns funcBody : ITm, funcWhere : [ITm]
trWhile :: Func -> M.Map String ITy -> PTm -> Stmt -> List Stmt -> List ITm -> Bool -> (ITm, [ITm])
trWhile f ctx condition body xs w isE =
  let f_rec_name = funcName f ++ "_rec" ++ show (length w)
      args = nubBy (\x y -> getIAnnParamVar x == getIAnnParamVar y) $ map trAnnParam (funcArgs f) ++ map (`IAnnParam` True) (M.toList ctx)
      iArgsVars = map (ITmVar . getIAnnParamVar) args
      argsVars = map (PTmVar . getIAnnParamVar) args
      rCall = PTmFuncCall (PTmVar f_rec_name) argsVars
      (bdy, w') = trListStmt f ctx (unblock body ++ [StReturn rCall]) w
      innerFunc =
        IFunc
          { iFuncName = f_rec_name,
            iFuncArgs = args,
            iFuncBody = [],
            iFuncRetTy = trTy (funcRetTy f),
            iWhere = []
          }
      (rest, w'') = trListStmt f ctx xs w
      innerBodyLHS = ITmFuncCall (ITmVar f_rec_name) iArgsVars
      innerBodyRHS = (if isE then convIf else ITmIf) (trTm condition) bdy rest
      innerFunc' = innerFunc {iFuncBody = [(innerBodyLHS, innerBodyRHS)]}
   in (trTm rCall, ITmFunc innerFunc' : nub (w' ++ w''))

fsmName :: Maybe Directive -> String
fsmName (Just (Directive (DFSM resourceTy stateTy) _)) = myShowTy resourceTy ++ "_" ++ myShowTy stateTy
fsmName Nothing = error "no directive!"

-- three cases: fsm exec, fsm action, IO
-- fsm exec and fsm action need access to `this` variable
-- fsm action needs to return pair of rval and resource
-- fsm exec needs to lift to IO if IO is used
-- lifting is only done in run function helper
-- args           og func  monad info      ctx map            body          where       (body, where)
trMonadListStmt :: Func -> Maybe Directive -> M.Map String ITy -> List Stmt -> List ITm -> (List ITmDo, List ITm)
--------------------------------------------------------------------------
-- block must end with return statement
-- for actions, add resource variable (this) to return
trMonadListStmt _ (Just (Directive _ (DAction _ _))) _ [StReturn tm] w = ([ITmDoPure (ITmPair (trTm tm) (ITmVar "this"))], w)
-- for run functions (inner), return `Pure<fsmName>` tm
trMonadListStmt _ d@(Just (Directive _ (DRun {}))) _ [StReturn tm] w =
  let pureTm = "Pure" ++ fsmName d
   in ([ITmDoTm (ITmFuncCall (ITmVar pureTm) [trTm tm])], w)
-- for pure monadic functions, simply wrap in pure
trMonadListStmt _ Nothing _ [StReturn tm] w = ([ITmDoPure (trTm tm)], w)
--------------------------------------------------------------------------
-- if end of block does not have a return statement, insert one
-- for actions, add resource variable (this) to return
trMonadListStmt _ (Just (Directive _ (DAction _ _))) _ [] w = ([ITmDoPure (ITmPair ITmUnit (ITmVar "this"))], w)
-- for run statements, return `Pure<fsmName> ()`
trMonadListStmt _ d@(Just (Directive _ (DRun {}))) _ [] w =
  let pureTm = "Pure" ++ fsmName d
   in ([ITmDoTm (ITmFuncCall (ITmVar pureTm) [ITmUnit])], w)
-- for monads with no directive, simply wrap in pure
trMonadListStmt _ _ _ [] w = ([ITmDoPure ITmUnit], w)
---------------------------------------------------------------------------
trMonadListStmt _ _ _ (StBlock _ : _) _ = error "no TL block inside block allowed"
trMonadListStmt g mdir ctx (StDeclAssign mty lhs rhs : xs) w =
  let imty = trTy <$> mty
      (rest, w') = trMonadListStmt g mdir (M.insert lhs (fromMaybe ITyHole imty) ctx) xs w
   in case rhs of
        PTmDot x f args ->
          let tm = case (mdir, x) of
                -- action directive, bind to pair with `this`, and add `this` to function args
                (Just (Directive _ (DAction {})), PTmThis) -> ITmDoBind [ITmVar lhs, ITmVar "this"] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                -- (Just str, PTmVar v) | str == v -> ITmDoBind [ITmVar lhs, ITmVar str] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                -- run directive, transform from function to uppercase constructor
                (Just (Directive _ (DRun {})), PTmThis) ->
                  let fCon = mkUpper f
                   in ITmDoBind [ITmVar lhs] (trTm fCon)
                -- run directive, lift IO
                (Just (Directive _ (DRun {})), PTmIO) ->
                  let lift = "Lift" ++ fsmName (funcDirective g)
                   in ITmDoBind [ITmVar lhs] (ITmFuncCall (ITmVar lift) [ITmFuncCall (trTm f) (map trTm args)])
                -- anything else, IO function
                (_, PTmIO) -> ITmDoBind [ITmVar lhs] (ITmFuncCall (trTm f) (map trTm args))
                (_, _) -> error $ "incorrect use of dot notation: mdir= " ++ show mdir ++ ", x= " ++ show x ++ ", fName = " ++ funcName g
           in (tm : rest, w')
        _ ->
          let tm = ITmDoLet lhs imty (trTm rhs)
           in (tm : rest, w ++ w')
trMonadListStmt g mdir ctx (StAssign var tm : xs) w = case M.lookup var ctx of
  Nothing -> error "assign without declare"
  Just ty ->
    let (rest, w') = trMonadListStmt g mdir ctx xs w
     in case tm of
          PTmDot x f args ->
            let itm = case (mdir, x) of
                  -- IO call in IO function
                  (Nothing, PTmIO) -> ITmDoBind [ITmVar var] (ITmFuncCall (trTm f) (map trTm args))
                  -- this in action
                  (Just (Directive _ (DAction {})), PTmThis) -> ITmDoBind [ITmVar var, ITmVar "this"] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                  -- this in run
                  (Just (Directive _ (DRun {})), PTmThis) ->
                    let fCon = mkUpper f
                     in ITmDoBind [ITmVar var] (trTm fCon)
                  -- IO in run
                  (Just (Directive _ (DRun {})), PTmIO) ->
                    let lift = "Lift" ++ fsmName (funcDirective g)
                     in ITmDoBind [ITmVar var] (ITmFuncCall (ITmVar lift) [ITmFuncCall (trTm f) (map trTm args)])
                  -- (Just str, PTmVar v) | str == v -> ITmDoBind [ITmVar var, ITmVar str] (ITmFuncCall (trTm f) (trTm x : map trTm args))
                  (_, _) -> error "incorrect use of dot notation"
             in (itm : rest, w')
          _ ->
            let itm = ITmDoLet var (Just ty) (trTm tm)
             in (itm : rest, w')
trMonadListStmt g mdir ctx (StDot x f args : xs) w =
  let (rest, w') = trMonadListStmt g mdir ctx xs w
      itm = case (mdir, x) of
        -- bind to unit, this
        (Just (Directive _ (DAction {})), PTmThis) -> ITmDoBind [ITmUnit, ITmVar "this"] (ITmFuncCall (trTm f) (ITmVar "this" : map trTm args))
        -- transform to constructor, bind
        (Just (Directive _ (DRun {})), PTmThis) -> ITmDoBind [ITmWildCard] (trTm (mkUpper f))
        -- lift to IO, bind to _
        (Just (Directive _ (DRun {})), PTmIO) -> ITmDoBind [ITmWildCard] (ITmFuncCall (ITmVar ("Lift" ++ fsmName (funcDirective g))) [ITmFuncCall (trTm f) (map trTm args)])
        -- bind to _ so we can add an explicit return
        (_, PTmIO) -> ITmDoBind [ITmWildCard] (ITmFuncCall (trTm f) (map trTm args))
        (_, _) -> error ("incorrect use of dot notation: mdir = " ++ show mdir ++ ", x = " ++ show x)
   in (itm : rest, w ++ w')
trMonadListStmt f mdir ctx (StIf c t e : xs) w =
  let (t', wt) = trMonadListStmt f mdir ctx (unblock t ++ xs) w
      (e', we) = trMonadListStmt f mdir ctx (unblock e ++ xs) w
   in ([ITmDoIf (trTm c) (ITmDo t') (ITmDo e')], nub (wt ++ we))
trMonadListStmt f mdir ctx (StEIf c t e : xs) w =
  let (t', wt) = trMonadListStmt f mdir ctx (unblock t ++ xs) w
      (e', we) = trMonadListStmt f mdir ctx (unblock e ++ xs) w
      itm = convIOIf (trTm c) (ITmDo t') (ITmDo e')
   in ([itm], nub (wt ++ we))
trMonadListStmt f mdir ctx (StSwitch (Switch switchOn cases defaultCase) : xs) w =
  let tmp = map (\(Case caseOn caseBody) -> (if null caseOn then replicate (length switchOn) ITmWildCard else map trTm caseOn, trMonadListStmt f mdir ctx (unblock caseBody ++ xs) w)) (cases ++ maybeToList defaultCase)
      branches = map (\(caseOn, (itm, w')) -> ((caseOn, ITmDo itm), w')) tmp
   in ([ITmDoCase (map trTm switchOn) (map fst branches)], concatMap snd branches)
trMonadListStmt f mdir ctx (StWhile condition body : xs) w = trMonadWhile f mdir ctx condition body xs w False
trMonadListStmt f mdir ctx (StEWhile condition body : xs) w = trMonadWhile f mdir ctx condition body xs w True
trMonadListStmt f mdir ctx (StSkip : xs) w = trMonadListStmt f mdir ctx xs w
trMonadListStmt _ _ _ (StReturn _ : _) _ = error "return must be last statement in block"

-- args:= og func -> <IO | fsm> -> ctx -> cond -> bdy -> tail -> where block -> isEWhile
-- returns:= funcBody : List ITmDo, funcWhere : List ITm
trMonadWhile :: Func -> Maybe Directive -> M.Map String ITy -> PTm -> Stmt -> List Stmt -> List ITm -> Bool -> ([ITmDo], [ITm])
trMonadWhile f mdir ctx condition body xs w isE =
  let f_rec_name = funcName f ++ "_rec" ++ show (length w)
      args = nub $ map trAnnParam (funcArgs f) ++ map (`IAnnParam` True) (M.toList ctx)
      argsVars = map (ITmVar . getIAnnParamVar) args
      rCall = ITmDoPure $ ITmFuncCall (ITmVar f_rec_name) argsVars
      (bdy, w') = trMonadListStmt f mdir ctx (unblock body) w
      innerFunc =
        IFunc
          { iFuncName = f_rec_name,
            iFuncArgs = args,
            iFuncBody = [],
            iFuncRetTy = trTy (funcRetTy f),
            iWhere = []
          }
      (rest, w'') = trMonadListStmt f mdir ctx xs w
      innerBodyLHS = ITmFuncCall (ITmVar f_rec_name) argsVars
      innerBodyRHS = ITmDo [(if isE then convIOIf else ITmDoIf) (trTm condition) (ITmDo (bdy ++ [rCall])) (ITmDo rest)]
      innerFunc' = innerFunc {iFuncBody = [(innerBodyLHS, innerBodyRHS)]}
   in ([rCall], ITmFunc innerFunc' : nub (w' ++ w''))

convIOIf :: ITm -> ITm -> ITm -> ITmDo
convIOIf c t e = ITmDoCase [trBool c] [([ITmCon "Yes" [ITmVar "Refl"]], t), ([ITmCon "No" [ITmVar "noprf"]], e)]

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

-- run resource (action >>= cont) = do
--    (res, resource) <- run resource action
--    run store (cont res)
mkRunBind :: String -> String -> String -> (ITm, ITm)
mkRunBind _ funcName resVar =
  let action = ITmVar "action"
      cont = ITmVar "cont"
      run = ITmVar funcName
      resource = ITmVar resVar
   in (ITmFuncCall run [resource, ITmBind action cont], ITmDo [ITmDoBind [ITmVar "res", resource] (ITmFuncCall run [resource, action]), ITmDoTm (ITmFuncCall run [resource, ITmFuncCall cont [ITmVar "res"]])])

-- run resource (Pure<fsmName> x) = pure (x, resource)
--         idxmName -> runFuncName -> resourceVar -> (LHS, RHS)
mkRunPure :: String -> String -> String -> (ITm, ITm)
mkRunPure fsmStr funcName resVar =
  let x = ITmVar "x"
      vPure = ITmVar $ "Pure" ++ fsmStr
      fPure = ITmVar "pure"
      resource = ITmVar resVar
      run = ITmVar funcName
   in (ITmFuncCall run [resource, ITmFuncCall vPure [x]], ITmFuncCall fPure [ITmPair x resource])

-- run resource (Lift<fsmName> io) = (\t => (t, resource)) <$> io
mkRunLift :: String -> String -> String -> (ITm, ITm)
mkRunLift fsmStr funcName resVar =
  let resource = ITmVar resVar
      run = ITmVar funcName
      lift = ITmVar $ "Lift" ++ fsmStr
      io = ITmVar "io"
      t = ITmVar "t"
   in (ITmFuncCall run [resource, ITmFuncCall lift [io]], ITmFuncCall (ITmVar "map") [ITmLam [t] (ITmPair t resource), io])

-- Pure<fsmName> : (x : ty) -> resTy ty (st x) st
mkConPure :: String -> String -> IConstructor
mkConPure fsmStr resTy =
  let st = ITmVar "st"
      x = ITmVar "x"
      ty = ITmVar "ty"
   in IConstructor
        { iConName = "Pure" ++ fsmStr,
          iConArgs = [IAnnParam ("x", ITyTm ty) True],
          iConTy = ITyApp (ITyVar resTy) [ty, ITmFuncCall st [x], st]
        }

--   Lift : IO ty -> Resource ty st (const st)
mkConLift :: String -> String -> IConstructor
mkConLift fsmStr resTy =
  let st = ITmVar "st"
      ty = ITmVar "ty"
      fConst = ITmVar "const"
   in IConstructor
        { iConName = "Lift" ++ fsmStr,
          iConArgs = [noAnnIParam (ITyIO (ITyTm ty))],
          iConTy = ITyApp (ITyVar resTy) [ty, st, ITmFuncCall fConst [st]]
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
          iConArgs = [noAnnIParam (ITyApp (ITyVar resTy) [a, st1, st2]), noAnnIParam (ITyFunc [(Just "x", ITyTm a), (Nothing, ITyApp (ITyVar resTy) [b, ITmFuncCall st2 [ITmVar "x"], st3])])],
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
      mcons = map (\f -> f str iFuncName resVar) [mkRunPure, mkRunBind, mkRunLift]
      cons = map (mkRunAction iFuncName resVar . iConName) (iTyDeclConstructors decl)
      declArg = noAnnIParam (ITyApp (ITyVar idxmName) $ map ITmVar $ filter (not . null) $ zipWith (curry (\(IAnnParam (str, _) b, i) -> if b && not (null str) then str else if b then "var" ++ show i else "")) (iTyDeclParams decl) [1 ..])
   in -- iFuncBody = mcons ++ cons
      IFunc
        { iFuncName,
          iFuncArgs = [noAnnIParam concTy, declArg],
          iFuncBody = mcons ++ cons,
          iFuncRetTy = ITyIO $ ITyPair (ITyTm (ITmVar "ty")) concTy,
          iWhere = []
        }

trFSM :: FSM -> (ITyDecl, IFunc)
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
      idxm = idxm' {iTyDeclConstructors = confuncs ++ map (\f -> f showFSM idxmName) [mkConPure, mkConBind, mkConLift]}
   in (idxm, run)

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

-- --------------------------
-- automatic generation of decidable equality
-- ----------------------------

-- dependent pattern matching via if statements
convIf :: ITm -> ITm -> ITm -> ITm
convIf c t e = ITmMatch [trBool c] [([ITmCon "Yes" [ITmVar "Refl"]], t), ([ITmCon "No" [ITmVar "noprf"]], e)]

mapFromFuncArgs :: List AnnParam -> M.Map String PTy -> M.Map String PTy
mapFromFuncArgs [] m = m
mapFromFuncArgs ((AnnParam (ty, var) _) : xs) m = mapFromFuncArgs xs (M.insert var ty m)

mapToAnnParam :: M.Map String PTy -> List AnnParam
mapToAnnParam m = map (\(v, ty) -> AnnParam (ty, v) True) (M.toList m)

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
                iBody = concatMap (getCases . Data.Bifunctor.bimap (tms "1") (tms "2")) cases
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
getCases (c1@(ITmCon v1 args1), c2@(ITmCon v2 args2)) =
  if v1 == v2
    then
      ( case length args1 == length args2 of
          True -> case null args1 of
            True -> [mkCase (c1, c2) [] Nothing (Tm $ ITmCon "Yes" [ITmVar "Refl"])]
            False ->
              let pairedargs = zip args1 args2
               in doEverything v1 [] ([], Nothing) pairedargs
          False -> error "dawg dis is Wrong"
      )
    else [mkCase (c1, c2) [] Nothing (Tm noImpossible)]
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