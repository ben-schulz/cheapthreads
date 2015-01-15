--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/PreDefun.hs
--
-- general functions used by the defunctionalizer, including:
--
--   * transformations on the abstract syntax tree to be performed
--   before defunctionalizing a CT program;
--
--   * predicates for identifying 'get' and 'put';
--
--   * error handlers;
--
-- code originally located in ./DefunK.hs
--
-- put here 11.02.09
--
-- Schulz
--

module CT.Defunctionalizer.PreDefun where

import CT.Syntax
import CT.Defunctionalizer.DefunTypes
import CT.Defunctionalizer.DFBuiltIns
import CT.Defunctionalizer.BMonad

import Data.List

--
-- please note that we assume that the typechecker
-- ensures correctly typed expressions in the
-- state monad; the defunctionalizer will
-- (at this point) throw away the types of
-- expressions
--
--
-- 29.01.09 Schulz

--
-- all state components are initially empty, i.e. 'DFNil'
--
-- also note that since the state is represented as an
-- association list, State layers must have unique names
--
-- 29.01.09 Schulz

--
-- currently, state component "x" is set to value Param "x",
-- except for the return value, which is still Nil
--
-- 01.03.09

--                               --
-- DEFUNCTIONALIZER PREPROCESSOR --
--                               --

prepast :: CtsProg -> [CtsDecl]
prepast (CtsProg ds) =
  let fenv1 = mkFEnv $ ds ++ builtindecs
      rwn = rwnullary fenv1 ds
      rwv = uniqlbv rwn
      fenv2 = mkFEnv $ rwv ++ builtindecs -- questionable; see log 17.07.09
  in
    inline fenv2 fenv2 rwv

-- this makes several crucial assumptions
-- about the language; see log (01.03.09)


--
-- this function is just for general purpose
-- debugging output; it doesn't serve a fixed
-- or essential purpose
--
debugast :: [CtsDecl] -> String
debugast ds = show $ mkFEnv ds
--debugast ds = show $ mkFEnv $ uniqlbv $ rwnullary (mkFEnv ds) ds

--                  --
-- INITIALIZE STATE --
--                  --

--                                               --
-- top-level function for creating initial state --
--                                               --

--
-- IMPORTANT:
-- changed this so that the default K components,
-- i.e. req, rsp, ports, rts, go at the FRONT
-- of the list, for easier access
--
-- 06.07.09 Schulz
--
--
mkState :: [CtsDecl] -> KState
mkState ds = defaultK ++ (foldr ((++) . mkKState) [ ] ds)


--
-- revised to use conditional types:
--
mkStatePlus :: [CtsDecl] -> KStatePlus
mkStatePlus ds =
  let newdefaultK = map (\(x, v) -> (x, V v)) defaultK
  in
    newdefaultK ++ (foldr ((++) . mkKStatePlus) [ ] ds)

--
-- transform a declaration into a (sub)state
--
mkKState :: CtsDecl -> KState
mkKState (CtsMonadDecl _ _ [ ])     = error "no layers in State monad"
mkKState (CtsMonadDecl _ k ls) -- create registers for K-monad
  | k == kIdent =
    let g  = \ (CtsStateLayer t name) ->
               let y = name ++ typetoken ++ showtype_vhdl t
               in
                 (y, DFParam name)
      in
      map g ls
  | otherwise = [ ]
mkKState (CtsFunDecl _ f args term) =  -- create LBV state components
  let g = mkprime . mklocal f
      h = \ y -> (y, DFParam y)
  in let lbvs = getlbvs f term 
     in
       (map (h . g) args) ++ lbvs
mkKState _ = [ ]  -- no other declarations determine state arity

--
-- adapted for conditional types:
--
mkKStatePlus :: CtsDecl -> KStatePlus
mkKStatePlus (CtsMonadDecl _ _ [ ])     = error "no layers in State monad"
mkKStatePlus (CtsMonadDecl _ k ls) -- create registers for K-monad
  | k == kIdent =
    let g  = \ (CtsStateLayer t name) ->
               let y = name ++ typetoken ++ showtype_vhdl t
               in (y, V $ DFParam name)
      in
      map g ls
  | otherwise = error $ "the state monad is called 'K'," ++
                        " in the parlance of our times, man"
mkKStatePlus (CtsFunDecl _ f args term) =  -- create LBV state components
  let g = mkprime . mklocal f
      h = \ y -> (y, V $ DFParam y)
  in let lbvs = getlbvsPlus f term 
     in
       (map (h . g) args) ++ lbvs
mkKStatePlus _ = [ ]  -- no other declarations determine state arity



--
-- separate external memories from other state components; these need
-- to be written out separately at code generation
--
-- 2009.11.16 Schulz
--
mkMems :: [CtsDecl] -> [Mem]
mkMems ((CtsMonadDecl _ _ ls):ds) =
  let ts = map mkMem ls
      f  = (\v -> \ms -> case v of
                           Nothing -> ms
                           Just m  -> (m:ms))
  in
    (foldr f [] ts) ++ (mkMems ds)

mkMems (_:ds) = mkMems ds
mkMems [ ] = [ ]

mkMem :: CtsMonadLayer -> Maybe Mem
mkMem (CtsStateLayer TyMemory m) = Just (Mem m)
mkMem _ = Nothing

--
-- collect all lambda-bound variables from
-- 'bind' or 'fix' sub-expressions within an expression
--
getlbvsPlus :: CtsIdent -> CtsExpr -> KStatePlus
getlbvsPlus f (CtsBind e1 x e2 t) =
  let  lbvs = (getlbvsPlus f e1) ++ (getlbvsPlus f e2)
--       (TyMonadic _ t') = typeOf e1  -- this ommission is temporary;
                                       -- see log (06.07.09)
--       y = x ++ typetoken ++ (showtype_vhdl t')
       y = x ++ typetoken ++ " teh_borked_typ3"  -- i.e. temporary (06.07.09)
  in
    (y, V $ DFParam y) : lbvs
getlbvsPlus f (CtsFixApp (_:ps) body args t) =
  let ts = map typeOf args
      z = zip ps ts
      h = \ (u, v) -> let w = u ++ typetoken ++ (showtype_vhdl v)
                      in (w, V $ DFParam w)
      lbvs = (getlbvsPlus f body) ++ (foldr ((++) . (getlbvsPlus f)) [ ] args)
  in
    (map h $ z) ++ lbvs         -- don't use or rename the first
                                -- parameter for state; see log (17.03.09)
getlbvsPlus f (CtsSemiFixApp _ (_:ps) body args t) =
  let ts = map typeOf args
      z = zip ps ts
      h = \ (u, v) -> let w = u ++ typetoken ++ (showtype_vhdl v)
                      in (w, V $ DFParam w)
      lbvs = (getlbvsPlus f body) ++ (foldr ((++) . (getlbvsPlus f)) [ ] args)
  in
    (map h $ z) ++ lbvs         -- same as fix; don't use or rename the first
                                -- parameter for state; (2009.11.09)
getlbvsPlus f (CtsApp _ args _) = foldr ((++) . (getlbvsPlus f)) [ ] args
getlbvsPlus f (CtsInfixApp e1 _ e2 _) = (getlbvsPlus f e1) ++ (getlbvsPlus f e2)
getlbvsPlus f (CtsConstrApp c args _) = foldr ((++) . (getlbvsPlus f)) [ ] args
getlbvsPlus f (CtsLitExpr _ _) = [ ]
getlbvsPlus f (CtsVar _ _) = [ ]
getlbvsPlus f (CtsNeg e _) = getlbvsPlus f e
getlbvsPlus f (CtsIfThenElse b ifc elsec _) =
  (getlbvsPlus f b) ++ (getlbvsPlus f ifc) ++ (getlbvsPlus f elsec)
getlbvsPlus f (CtsCase cof alts _) =
  let exprs = map (\ (CtsAlt _ e) -> e) alts
  in
  (getlbvsPlus f cof) ++ (foldr ((++) . (getlbvsPlus f)) [ ] exprs)
getlbvsPlus f (CtsTuple cs _) = foldr ((++) . getlbvsPlus f) [ ] cs
getlbvsPlus f (CtsUnit _) = [ ]
getlbvsPlus f (CtsBindNull e1 e2 _) = (getlbvsPlus f e1) ++ (getlbvsPlus f e2)
getlbvsPlus f (CtsReturn _ _) = [ ]
getlbvsPlus f x = error $ "in getlbvs: no case for " ++ show x

--
-- old version with old types:
--
getlbvs :: CtsIdent -> CtsExpr -> KState
getlbvs f (CtsBind e1 x e2 t) =
  let  lbvs = (getlbvs f e1) ++ (getlbvs f e2)
--       (TyMonadic _ t') = typeOf e1  -- this ommission is temporary;
                                       -- see log (06.07.09)
--       y = x ++ typetoken ++ (showtype_vhdl t')
       y = x ++ typetoken ++ " teh_borked_typ3"  -- i.e. temporary (06.07.09)
  in
    (y, DFParam y) : lbvs
getlbvs f (CtsFixApp (_:ps) body args t) =
  let ts = map typeOf args
      z = zip ps ts
      h = \ (u, v) -> let w = u ++ typetoken ++ (showtype_vhdl v)
                      in (w, DFParam w)
      lbvs = (getlbvs f body) ++ (foldr ((++) . (getlbvs f)) [ ] args)
  in
    (map h $ z) ++ lbvs         -- don't use or rename the first
                                -- parameter for state; see log (17.03.09)
getlbvs f (CtsApp _ args _) = foldr ((++) . (getlbvs f)) [ ] args
getlbvs f (CtsInfixApp e1 _ e2 _) = (getlbvs f e1) ++ (getlbvs f e2)
getlbvs f (CtsConstrApp c args _) = foldr ((++) . (getlbvs f)) [ ] args
getlbvs f (CtsLitExpr _ _) = [ ]
getlbvs f (CtsVar _ _) = [ ]
getlbvs f (CtsNeg e _) = getlbvs f e
getlbvs f (CtsIfThenElse b ifc elsec _) =
  (getlbvs f b) ++ (getlbvs f ifc) ++ (getlbvs f elsec)
getlbvs f (CtsCase cof alts _) =
  let exprs = map (\ (CtsAlt _ e) -> e) alts
  in
  (getlbvs f cof) ++ (foldr ((++) . (getlbvs f)) [ ] exprs)
getlbvs f (CtsTuple cs _) = foldr ((++) . getlbvs f) [ ] cs
getlbvs f (CtsUnit _) = [ ]
getlbvs f (CtsBindNull _ _ _) = [ ]
getlbvs f (CtsReturn _ _) = [ ]
getlbvs f x = error $ "in getlbvs: no case for " ++ show x

--
-- sift out function declarations;
-- these are used to evaluate function applications
--
mkFEnv :: [CtsDecl] -> FEnv
mkFEnv = foldr c [ ]
           where
             c decl xs = case decl of
                           (CtsFunDecl _ f args body) -> (f, (args, body)) : xs
                                                    
                           _ -> xs


--                                             --
-- TRANSFORMATIONS ON THE ABSTRACT SYNTAX TREE -- 
--                                             --

--
-- force unique names in lambda-bound variables
-- of abstract syntax tree:
--
-- (under the reasonable assumption that all declared
-- functions have unique identifiers)
--

--
-- added 'tagfix' to tag fix applications
-- so that they can be recognized and permitted
-- as 'undeclared functions' by the inliner
--
-- 20.07.09 Schulz
--
uniqlbv :: [CtsDecl] -> [CtsDecl]
uniqlbv ds = map forcenames ds

forcenames :: CtsDecl -> CtsDecl
forcenames (CtsFunDecl l f ps e) =
  let newps = map (mkprime . mklocal f) ps
      e' = forcenamesexpr f e
      e'' = tagfix [ ] e'
  in
    CtsFunDecl l f newps e''
forcenames x = x


tagfix :: [CtsIdent] -> CtsExpr -> CtsExpr
tagfix ks d@(CtsApp f args t) =
  let args' = map (tagfix ks) args
  in
    if elem f ks 
    then
      (CtsApp (f ++ fixfix) args t)
    else
      d

tagfix ks (CtsFixApp (k:ps) e args t) =
  let e'    = tagfix (k:ks) e
      args' = map (tagfix ks) args -- fixpoint should not occur in the args
  in
    CtsFixApp (k:ps) e' args' t

tagfix ks (CtsSemiFixApp sent (k:ps) e args t) =
  let e'    = tagfix (k:ks) e
      args' = map (tagfix ks) args -- fixpoint should not occur in the args
      sent' = (tagfix ks) sent     -- fixpoint should not occur guard expression
  in
    CtsSemiFixApp sent' (k:ps) e' args' t

tagfix ks (CtsFixApp [ ] _ _ _) = error "in tagfix: bad fixpoint application"

tagfix ks (CtsInfixApp e1 f e2 t) =
  let e1' = tagfix ks e1
      e2' = tagfix ks e2
      f'  = if elem f ks then (f ++ fixfix) else f
  in
    CtsInfixApp e1' f' e2' t

tagfix ks (CtsConstrApp c es t) =
  let es' = map (tagfix ks) es
  in
    CtsConstrApp c es' t

tagfix ks e@(CtsVar _ _)     = e
tagfix ks e@(CtsLitExpr _ _) = e
tagfix ks (CtsNeg e t) = CtsNeg (tagfix ks e) t
tagfix ks (CtsIfThenElse b e1 e2 t) =
  let b' = tagfix ks b
      e1' = tagfix ks e1
      e2' = tagfix ks e2
  in
    CtsIfThenElse b' e1' e2' t

tagfix ks (CtsCase e alts t) =
  let e'    = tagfix ks e
      alts' = map (\(CtsAlt p x) -> (CtsAlt p (tagfix ks x))) alts
  in
    CtsCase e' alts' t

tagfix ks (CtsTuple es t) = CtsTuple (map (tagfix ks) es) t
tagfix ks (CtsList es t) = CtsList (map (tagfix ks) es) t
tagfix ks e@(CtsUnit _) = e
tagfix ks (CtsBind e1 x e2 t) =
  let e1' = tagfix ks e1
      e2' = tagfix ks e2
  in
    CtsBind e1' x e2' t
tagfix ks (CtsBindNull e1 e2 t) =
  let e1' = tagfix ks e1
      e2' = tagfix ks e2
  in
    CtsBindNull e1' e2' t
tagfix ks (CtsReturn e t) = CtsReturn (tagfix ks e) t
tagfix ks e = error $ "in tagfix: no case for " ++ (show e)

--
-- change all variable references within an expression
-- to reflect the changes made to the variable names
-- (to ensure uniqueness in the state);
--
-- note that this function assumes variables are not replicated
-- in enclosing scopes
--
forcenamesexpr :: CtsIdent -> CtsExpr -> CtsExpr
forcenamesexpr f (CtsVar x t) = CtsVar (mkprime $ mklocal f x) t
forcenamesexpr f (CtsApp g args t) = CtsApp g (map (forcenamesexpr f) args) t
forcenamesexpr f (CtsFixApp ps body args t) =
  let newargs = map (forcenamesexpr f) args
      newps = (head ps) : (map (mkprime . mklocal f) $ tail ps)  -- see log (17.03.09)
      newbody = forcenamesexpr f body
  in
    CtsFixApp newps newbody newargs t
forcenamesexpr f (CtsSemiFixApp sent ps body args t) =
  let newargs = map (forcenamesexpr f) args
      newps = (head ps) : (map (mkprime . mklocal f) $ tail ps)  -- see log (17.03.09)
      newbody = forcenamesexpr f body
      newsent = forcenamesexpr f sent
  in
    CtsSemiFixApp newsent newps newbody newargs t
forcenamesexpr f (CtsInfixApp e1 x e2 t) = forcenamesexpr f (CtsApp x [e1,e2] t)
forcenamesexpr f (CtsConstrApp c args t) =
  let newargs = map (forcenamesexpr f) args
  in
    CtsConstrApp c newargs t
forcenamesexpr f x@(CtsLitExpr _ _) = x
forcenamesexpr f (CtsNeg e t) = CtsNeg (forcenamesexpr f e) t
forcenamesexpr f (CtsIfThenElse b ifc elsec t) =
  let n00b = forcenamesexpr f b
      newif = forcenamesexpr f ifc
      newelse = forcenamesexpr f elsec
  in
    CtsIfThenElse n00b newif newelse t
forcenamesexpr f (CtsCase cof alts t) =
  let newalts = map (\ (CtsAlt p e) -> (CtsAlt p (forcenamesexpr f e))) alts
      newof = forcenamesexpr f cof
  in
    CtsCase newof newalts t
forcenamesexpr f (CtsTuple cs t) = CtsTuple (map (forcenamesexpr f) cs) t
forcenamesexpr f x@(CtsUnit _) = x
forcenamesexpr f (CtsBind e1 x e2 t) =
  let new1 = forcenamesexpr f e1
      new2 = forcenamesexpr f e2
      newx = mkprime $ mklocal f x
  in
    CtsBind new1 newx new2 t
forcenamesexpr f (CtsBindNull e1 e2 t) =
  let new1 = forcenamesexpr f e1
      new2 = forcenamesexpr f e2
  in
    CtsBindNull new1 new2 t
forcenamesexpr f (CtsReturn e t) = CtsReturn (forcenamesexpr f e) t

--
-- rewrite nullary function applications
-- that have been parsed as variables
-- (frontend currently parses application of arity-zero
-- functions as variable names)
--
-- 27.02.09 Schulz

rwnullary :: FEnv -> [CtsDecl] -> [CtsDecl]
rwnullary env ds = map (rwnullarydec env) ds

rwnullarydec :: FEnv -> CtsDecl -> CtsDecl
rwnullarydec env (CtsFunDecl p f args body) =
  let newbody = rwnullaryexpr env body
  in
    CtsFunDecl p f args newbody
rwnullarydec _ x = x

rwnullaryexpr :: FEnv -> CtsExpr -> CtsExpr
rwnullaryexpr env (CtsVar x t)
  | (isGetid x) = (CtsApp x [ ] t)  -- only put is a "special" nullary app
  | otherwise =
    case lookup x env of
      Nothing     -> CtsVar x t
      Just (p, e) -> case p of
                       [ ]  -> CtsApp x [ ] t  -- rewrite to nullary application
                       _    -> badApp x
rwnullaryexpr env (CtsApp f args t) =
  let newargs = map (rwnullaryexpr env) args
  in
    CtsApp f newargs t
rwnullaryexpr env (CtsFixApp ps body args t) =
  let newbody = rwnullaryexpr env body
      newargs = map (rwnullaryexpr env) args
  in
    CtsFixApp ps newbody newargs t
rwnullaryexpr env (CtsSemiFixApp sent ps body args t) =
  let newbody = rwnullaryexpr env body
      newargs = map (rwnullaryexpr env) args
      newsent = rwnullaryexpr env sent
  in
    CtsSemiFixApp newsent ps newbody newargs t
rwnullaryexpr env (CtsInfixApp e1 f e2 t) =
  rwnullaryexpr env (CtsApp f [e1, e2] t)
rwnullaryexpr env (CtsConstrApp con args t) =
  let newargs = map (rwnullaryexpr env) args
  in
    CtsConstrApp con newargs t
rwnullaryexpr env (CtsLitExpr x t) = (CtsLitExpr x t)
rwnullaryexpr env (CtsNeg e t) =
  let newe = rwnullaryexpr env e
  in
    CtsNeg e t
rwnullaryexpr env (CtsIfThenElse b e1 e2 t) =
  let n00b = rwnullaryexpr env b
      newe1 = rwnullaryexpr env e1
      newe2 = rwnullaryexpr env e2
  in
    CtsIfThenElse n00b newe1 newe2 t
rwnullaryexpr env (CtsCase c alts t) =
  let newc = rwnullaryexpr env c
      newalts = map (\ (CtsAlt p e) -> (CtsAlt p (rwnullaryexpr env e))) alts
  in
    CtsCase newc newalts t
rwnullaryexpr env (CtsTuple cs t) =
  let newcs = map(rwnullaryexpr env) cs
  in
    CtsTuple newcs t
rwnullaryexpr env (CtsUnit t) = (CtsUnit t)
rwnullaryexpr env (CtsBind e1 x e2 t) =
  let newe1 = rwnullaryexpr env e1
      newe2 = rwnullaryexpr env e2
  in
    CtsBind newe1 x newe2 t
rwnullaryexpr env (CtsBindNull e1 e2 t) =
  let newe1 = rwnullaryexpr env e1
      newe2 = rwnullaryexpr env e2
  in
    CtsBindNull newe1 newe2 t
rwnullaryexpr env (CtsReturn e t) =
  let newe = rwnullaryexpr env e
  in
    CtsReturn newe t

--
-- inline all function applications,
-- i.e. replace function appplication with
-- an appropriate expression substitution
--

inline :: FEnv -> FEnv -> [CtsDecl] -> [CtsDecl]
inline [ ] env ds = map (inlinedec env) ds
inline (_:fs) env ds =
  let newenv = map (\ (f, (ps, e)) -> (f, (ps, inlineexpr env e))) env
      newdecs = map (inlinedec newenv) ds
  in
    inline fs newenv newdecs

--
-- note that fixpoints should not appear
-- in 'get' or 'put', so that these cases
-- do not need to be dealt with for the
-- purposes of defunctionalization
--
-- 09.02.09 Schulz
--

--
-- inline all function applications in a declaration;
-- only function declarations need to be dealt with,
-- since only these will be defunctionalized
--

inlinedec :: FEnv -> CtsDecl -> CtsDecl
inlinedec env (CtsFunDecl p f args body) =
  let e = inlineexpr env body
  in
    (CtsFunDecl p f args e)
inlinedec _ d = d

--
-- inline all function applications in an expression;
-- note that 'get' and 'put' applications are not inlined;
-- however, any function apps possibly occurring in their
-- arguments should be inlined
--
-- 09.02.09 Schulz
--
inlineexpr :: FEnv -> CtsExpr -> CtsExpr
inlineexpr ds q@(CtsApp f args t)
--  | elem f $ map fst ds = q -- i.e. if 'f' is a builtin, leave it alone
  | (isGet q || isPut q || isStep q || isSignal q) =  -- need case for 'signal'
    let newargs = map (inlineexpr ds) args
    in
      CtsApp f newargs t
  | otherwise =
    if (tail fixfix) == (last $ words f) -- see log 20.07.09
    then
      q  -- i.e. if this an application of the fixpoint, do nothing to it
    else
      -- otherwise, substitute the appropriate expression
      case lookup f ds of
        Nothing -> varNotFound $ "in CtsApp in inlineexpr: " ++ f
        Just e  -> let y = inlineexpr ds (snd e)
                   in
                     fBindLocal (fst e, y) args
inlineexpr ds (CtsFixApp params body args t) =
  let newbody = inlineexpr ds body
      newargs = map (inlineexpr ds) args
  in
    CtsFixApp params newbody newargs t
inlineexpr ds (CtsSemiFixApp sent params body args t) =
  let newbody = inlineexpr ds body
      newargs = map (inlineexpr ds) args
      newsent = inlineexpr ds sent
  in
    CtsSemiFixApp newsent params newbody newargs t
inlineexpr ds (CtsInfixApp e1 f e2 t) =
  inlineexpr ds (CtsApp f [e1, e2] t)
inlineexpr ds (CtsConstrApp con args t) =
  let newargs = map (inlineexpr ds) args
  in
    CtsConstrApp con newargs t
inlineexpr ds l@(CtsLitExpr _ _) = l
inlineexpr ds v@(CtsVar _ _) = v
inlineexpr ds (CtsNeg e t) = CtsNeg (inlineexpr ds e) t
inlineexpr ds (CtsIfThenElse b ifc elsec t) =
  let n00b = inlineexpr ds b
      newif = inlineexpr ds ifc
      newelse = inlineexpr ds elsec
  in
    CtsIfThenElse n00b newif newelse t
inlineexpr ds (CtsCase caseof alts t) =
  let newof = inlineexpr ds caseof
      newalts = map (\ (CtsAlt p e) -> (CtsAlt p $ inlineexpr ds e)) alts
  in
    CtsCase newof newalts t
inlineexpr ds (CtsTuple es t) = CtsTuple (map (inlineexpr ds) es) t
inlineexpr ds u@(CtsUnit _) = u
inlineexpr ds (CtsBind e1 x e2 t) =
  let new1 = inlineexpr ds e1
      new2 = inlineexpr ds e2
  in
    CtsBind new1 x new2 t
inlineexpr ds (CtsBindNull e1 e2 t) =
  let new1 = inlineexpr ds e1
      new2 = inlineexpr ds e2
  in
    CtsBindNull new1 new2 t
inlineexpr ds (CtsReturn e t) = CtsReturn (inlineexpr ds e) t
  

fBindLocal :: ([CtsIdent], CtsExpr) -> [CtsExpr] -> CtsExpr
fBindLocal (xs, e) ys =
  let z = zip xs ys
      m (x,y) expr = subst (x,y) expr
  in
    foldr m e z

--
-- replace all occurrences of parameter x with expression y
-- in a given expression;
--
-- again we assume correctness of types
-- from the frontend
--
subst :: (CtsIdent, CtsExpr) -> CtsExpr -> CtsExpr
subst (x,y) (CtsVar v t) | v == x    = y
                         | otherwise = CtsVar v t
subst _ (CtsLitExpr c t) = CtsLitExpr c t
subst (x, y) (CtsFixApp params body args t) =
  let newargs = map (subst (x,y)) args
      newbody = subst (x, y) body
  in
    CtsFixApp params newbody newargs t
subst (x, y) (CtsSemiFixApp sent params body args t) =
  let newargs = map (subst (x,y)) args
      newbody = subst (x, y) body
      newsent = subst (x, y) sent
  in
    CtsSemiFixApp newsent params newbody newargs t
subst (x,y) (CtsApp f args t) =
  let newargs = map (subst (x,y)) args
  in
    CtsApp f newargs t
subst (x,y) (CtsInfixApp e1 f e2 t) = subst (x,y) (CtsApp f [e1, e2] t)
subst (x,y) (CtsConstrApp c args t) =
  let newargs = map (subst (x,y)) args
  in
    CtsConstrApp c newargs t
subst (x,y) (CtsNeg e t) = CtsNeg (subst (x,y) e) t
subst (x,y) (CtsIfThenElse b e1 e2 t) =
  let n00b    = subst (x,y) b
      newif   = subst (x,y) e1
      newelse = subst (x,y) e2
  in
    CtsIfThenElse n00b newif newelse t
subst (x,y) (CtsCase ofe alts t) =        -- SEE NOTE IN LOG (09.02.09)
  let newof   = subst (x,y) ofe
      newalts = map (\ (CtsAlt p e) -> (CtsAlt p $ subst (x,y) e)) alts
  in
    CtsCase newof newalts t
subst (x,y) (CtsTuple es t) = CtsTuple (map (subst (x,y)) es) t
subst _ (CtsUnit t) = CtsUnit t
subst (x,y) (CtsBind e1 f e2 t) =
  let newe1 = subst (x,y) e1
      newe2 = subst (x,y) e2
  in
    CtsBind newe1 f newe2 t
subst (x,y) (CtsBindNull e1 e2 t) =
  let newe1 = subst (x,y) e1
      newe2 = subst (x,y) e2
  in
    CtsBindNull newe1 newe2 t
subst (x,y) (CtsReturn e t) = CtsReturn (subst (x,y) e) t
--subst _ e = error $ "in subst : no case for " ++ show e

--            --
-- MISCELLANY --
--            --

nameOfDec :: CtsDecl -> CtsIdent
nameOfDec (CtsFunDecl _ x _ _) = x
nameOfDec _ = ""

--
-- remove the type annotation from a preprocessed register label
--
dropType :: CtsIdent -> CtsIdent
dropType x = init $ foldr g "" (f $ words x)
             where
               f u = case u of
                       [v] -> [v]
                       w   -> init w
               g s t = s ++ (' ':t)

--
-- drop the types from a K-component
--
cleanTypes :: (CtsIdent, DefunVal) -> (CtsIdent, DefunVal)
cleanTypes (x, (DFParam y)) = (dropType x, DFParam (dropType y))
cleanTypes (x, y) = (dropType x, y)

--
-- redone to use conditional values:
--
cleanTypesPlus :: (CtsIdent, RHVal) -> (CtsIdent, RHVal)
cleanTypesPlus (x, V (DFParam y)) = (dropType x, V $ DFParam (dropType y))
cleanTypesPlus (x, y) = (dropType x, y)

--                    --
-- UTILITY PREDICATES --
--                    --

--
-- force a unique identifier
--
-- by convention, this is done
-- by appending the name of the function
-- in which the variable is used
--

mklocal :: CtsIdent -> CtsIdent -> CtsIdent
mklocal f x = x ++ (' ':f)

--
-- simple kludge to get rid of the unwanted ticks in
-- identifier names; in reality, these should really be
-- prohibited by the parser
--

mkprime :: CtsIdent -> CtsIdent
mkprime x = foldr f "" x where
              f = \c -> \s -> if (c == '\'') then "_prime" ++ s
                              else (c:s)

--
-- 'put' and 'get' are yielded by application
-- in the abstract expression syntax;
-- in particular, they should appear as:
--
--   CtsApp getNameK [ ] TyMonadic "K" a
--
--   CtsApp putNameK [ ] TyMonadic "K" ( )
--
-- where "Name" is a valid CtsIdent
--
-- 29.01.09 Schulz


--
-- identify a "get" application
--

--
-- expeditiously modified to accomodate
-- type-checker circumvention
--
-- 06.07.09 Schulz
--

isGet :: CtsExpr -> Bool
isGet (CtsApp name _ _) -- former (06.07.09)
--isGet (CtsApp name _ (TyMonadic kIdent _)) -- former (06.07.09)
--  | 'K' == (last name) && "get" == (take 3 name)  = True  -- former (06.07.09)
  | "get" == (take 3 name)  = True
  | otherwise = False
isGet _ = False

--
-- identify a "put" application
--

--
-- expeditiously modified to accomodate
-- type-checker circumvention
--
-- 06.07.09 Schulz
--

isPut :: CtsExpr -> Bool
isPut (CtsApp name _ _) -- former (06.07.09)
-- isPut (CtsApp name _ (TyMonadic kIdent _)) -- former (06.07.09)
--  | 'K' == (last name) && "put" == (take 3 name)  = True -- former (06.07.09)
  | "put" == (take 3 name)  = True -- former (06.07.09)
  | otherwise = False
isPut _ = False

--
-- identify a "get" keyword
--
isGetid :: CtsIdent -> Bool
isGetid xs | 'K' == (last xs) && "get" == (take 3 xs)  = True
           | otherwise = False
--
-- identify a "get" keyword
--
isPutid :: CtsIdent -> Bool
isPutid xs | 'K' == (last xs) && "put" == (take 3 xs)  = True
           | otherwise = False

--
-- identify a "get" keyword
--
isStepid :: CtsIdent -> Bool
isStepid xs = "step" == (take 4 xs) -- to handle stepRe (08.07.09)
{-
isStepid xs | 'R' == (last xs) && "step" == (take 4 xs)  = True
           | otherwise = False
-}

--
-- this is preliminary, until exact 'step' keyword is known
--
isStep :: CtsExpr -> Bool
isStep (CtsApp f args t) | isStepid f  = True
                         | otherwise   = False
isStep _ = False

--
-- same thing with 'signal' as with 'step':
--
isSignal :: CtsExpr -> Bool
isSignal (CtsApp f args t) | isSignalid f  = True
                           | otherwise   = False
isSignal _ = False

--
-- may have to change convention later, as keywords vary
--
isSignalid :: CtsIdent -> Bool
isSignalid f = (take 6 f) == "signal"


--
-- identify the main function
-- 
isMain :: CtsDecl -> Bool
isMain (CtsFunDecl _ x _ _) | x == "main"  = True
                            | otherwise    = False
isMain _ = False

--
-- identify a recursive call (within fix)
--

isRec :: CtsIdent -> Bool   -- THIS IS A KLUDGE DO NOT LEAVE IT HERE
isRec _ = True

--                --
-- ERROR HANDLERS --
--                --

varNotFound :: CtsIdent -> a
varNotFound x = error $ "couldn't locate binding " ++ x

badApp :: CtsIdent -> a
badApp x = error $ "in function application: " ++ x
                   ++ " called with wrong number of arguments"

badType :: String -> a
badType x = error $ "ill-typed expression " ++ x

patMatchFail :: String -> String -> a
patMatchFail expr alts = error $ "non-exhaustive patterns; couldn't match "
                           ++ expr ++ "to case alternatives " ++ alts


-- THIS IS THE END OF THE FILE --
