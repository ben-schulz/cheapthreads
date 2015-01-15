--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/DefunR.hs
--
-- defunctionalizer for the R monad, and top-level entry point
-- to the defunctionalizer generally
--
-- put here 11.02.09 Schulz
--


module CT.Defunctionalizer.DefunR where

import Control.Monad
import Data.List
import CT.Syntax
import CT.Defunctionalizer.DefunTypes
import CT.Defunctionalizer.PreDefun
import CT.Defunctionalizer.DefunK
import CT.Defunctionalizer.DefunM
import CT.Defunctionalizer.BMonad


--
-- the environment for a fixpoint is extended
-- with the formal (non-kappa) parameters,
-- and these are bound for each recursive call
--
-- 16.02.09 Schulz

--                       --
-- MAIN DEFUNCTIONALIZER --
--                       --

--
-- a slightly expanded, slightly hacky, new entry point:
--
defunTop :: CtsProg -> SysConfig
defunTop p@(CtsProg ds) =
  let ts  = defunPlus p
      ast = prepast p
      ks  = nub $ map cleanTypesPlus (mkStatePlus ast)
      ms  = mkMems ds
  in
    (ks, ms, ts)

--
-- old entry-point:
--
defunPlus :: CtsProg -> [Transition]
defunPlus ds =
  let ast = prepast ds
      main = head $ foldr (\ x -> \ y -> if (isMain x) then x:y else y) [ ] ast
      kstate = nub $ map cleanTypesPlus (mkStatePlus ast)   -- see log 10.04.09
                                                            -- also (2009.11.13)
      rules = (defundecPlus kstate main) >>= \rs ->

               -- make a transition to the final state:
               get >>= \i ->
               return $ (Left ((PCI i, kstate), (PCL exit_label, kstate))) : rs

      init = case main of   -- see log 01.04.09
               CtsFunDecl _ _ _ (CtsFixApp (k:ps) _ args _) ->
                                 let vals   = map (evalCtsExprPlus kstate) args
                                     new    = zip ps vals
                                     istate =  foldr
                                                 (uncurry writeKPlus)
                                                   kstate new
                                 in
                                 Left ((PCL init_label, kstate),
                                        (PCL $ k ++ fix_init_label, istate))

      -- same as case for 'fix':

               CtsFunDecl _ _ _ (CtsSemiFixApp sent (k:ps) _ args _) ->
                                 let vals   = map (evalCtsExprPlus kstate) args
                                     new    = zip ps vals
                                     istate =  foldr
                                                 (uncurry writeKPlus)
                                                   kstate new
                                 in
                                   Left ((PCL init_label, kstate),
                                          (PCL $ k ++ fix_init_label, istate))
                                  

      -- case when 'main' does not begin with a fixpoint:
               _    -> 
                                 Left ((PCL init_label, kstate),
                                        (PCI 0, kstate))
  in
--    (map Left handler_routine) ++
    (init : ((runM rules) (\ _ -> [ ]) 0 [ ] [ ])) -- i.e. project out of M

--
-- old version with old types:
--

--
-- shut off to prevent extraneous type errors while working
--
-- 20.07.09 Schulz
--
{-
defun :: CtsProg -> [RRule]
defun ds =
  let ast = prepast ds
      main = head $ foldr (\ x -> \ y -> if (isMain x) then x:y else y) [ ] ast
      kstate = map cleanTypes (mkState ast)   -- see log 10.04.09
      rules = defundec kstate main
      init = case main of   -- see log 01.04.09
               CtsFunDecl _ _ _ (CtsFixApp (k:ps) _ args _) ->
                                 let vals = map (evalCtsExpr kstate) args
                                     new = zip ps vals
                                     istate =  foldr (uncurry writeK) kstate new
                                 in
                                 ((PCL init_label, kstate),
                                  (PCL $ k ++ fix_init_label, istate))
                                  
               _                                    -> 
                                 ((PCL init_label, kstate),
                                  (PCI 0 , kstate))
  in
--    handler_routine ++    -- temporary for type consistency 16.07.09
    (init : ((runM rules) (\ v -> [ ]) 0 [ ] [ ])) -- i.e. project out of M
-}

--
-- defunctionalize a given declaration
--

-- shut off to prevent extraneous type errors 20.07.09
{-
defundec :: KState -> CtsDecl -> M [RRule]
defundec k (CtsFunDecl _ _ _ body) = defunR k body
defundec _ _ = return [ ]
-}

--
-- new version with new types
--
defundecPlus :: KStatePlus -> CtsDecl -> M [Transition]
defundecPlus k (CtsFunDecl _ _ _ body) = defunRPlus k body
defundecPlus _ _ = return [ ]

--                      --
--  DEFUNCTIONALIZE FIX --
--                      --
--
-- DEPRECATED
--
-- 24.02.09 Schulz
--
{-
defunfix :: KState -> CtsDecl -> M [RRule]
defunfix s (CtsFixFunDecl _ k args body) =
  do
    i <- get
    b <- rdEnv
    r <- let ext x v f = \ n -> if n == x then v else f n
             b' = ext k args b
         in
           inEnv b' $ defunR s body
    return $ ((PCL $ k ++ fixfix, s), (PCI i, s)) : r
-}

--                         --
-- R-DEFUNCTIONALIZER --
--                         --

-- NOTE THAT
-- we assume that defunK disregards the type signiture
-- i.e. defunK (x :: t1) evaluates identically to defunK (x :: t2)

defunRPlus :: KStatePlus -> CtsExpr -> M [Transition]
defunRPlus s (CtsApp f args _)
  | isStepid f =
    counter >>= \ i ->
    let l    = s
        r    = defunKPlus expr l
        expr = case args of
                     [v] -> v
                     _   -> badApp f
        cs   = fst $ spreadR r
        ks   = snd $ spreadR r
        ts   = map (\k -> ((PCI i, l), (PCI $ i + 1, k))) ks
    in
      case cs of
        [_]   -> return (map Left ts)            -- see log (2009.11.12)
        (_:cs') -> return (map Right (zip cs' $ tail ts)) 
                                                    -- if conditional, drop the
                                                    -- place-holder at the head
                                                    -- (2009.11.17)
      

--      return [((PCI i, l), (PCI $ i + 1, r))]

  --
  -- currently assuming no 'if-then-else' expressions in any
  -- argument of a function application other than 'step' (2009.11.12)
  --


  | isSignalid f = 
      case args of
        [(CtsConstrApp p [] TyInPort), q] -> let x = (V (DFParam p))
                                             -- 'x' is the port label
                                             in
                                               counter >>= \i ->
                                               return  -- see (2009.12.14)
                                                 [Left ((PCI i, s),
                                                        (PCI $ i + 1,
                                                        writeKPlus vIdent x s))]

        [(CtsConstrApp p [] TyOutPort), q] -> let v = evalCtsExprPlus s q
                                               -- 'v' is the signal code
                                              in
                                                counter >>= \i ->
                                                return
                                                  [Left ((PCI i, s),
                                                         (PCI $ i + 1,
                                                          writeKPlus p v s))]

        [_, _] -> error "first argument of \'signal\' must specify a port\n"

        _      -> error $ "signal called with wrong number of arguments: \n" ++
                          (show args) ++ "\n"
       

  -- assumed no 'if-then-else' values here either: (2009.11.12)

  | isRec f =
    rdEnv >>= \ rho ->
    let fps    = rho f
        argvs  = map (evalCtsExprPlus s) args
        deltas = map (uncurry writeKPlus) (zip fps argvs)
        delta = foldr (.) id deltas
        (l, r) = (s, delta s)
        mkrectrans x y k i = [Left ((PCI i, x), (PCL k, y))]
    in
--      counter >>= return . return . mkrectrans l r f
      counter >>= return . mkrectrans l r f

{-

--
-- this case is now defunct; it was anincomplete implementation of
-- signalling that now serves no good purpose; it has been superseded
-- by the new case above
--
-- 2009.12.11 Schulz
--

  | signalRe == f  =
      counter >>= \ i ->
      let [v, _, rsp, ports] = take 4 s
      in
        case args of
          [psi] -> let sv  = case evalCtsExprPlus s psi of
                               (V sig) -> (V sig)
                               _       -> error "conditional in signal value\n"

                       req = (reqIdent, sv)
                       rts = (rtsIdent, V (DFInt i))
                       rest = drop 5 s
                   in
                     return [ Left
                              ((PCI i, s),
                              (PCL handlerL,[v,req,rsp,ports,rts] ++ rest))]
                               
          _     -> error "in defunR: signalRe called with too many arguments"
-}


  | otherwise = error $ "in defunR: attempt to defunctionalize " ++
                        "non-step application " ++ "\'" ++ f ++ "\'"


defunRPlus s (CtsFixApp (k:params) body args t) =
  do
--    i <- get  -- see log 2009.11.10
    i  <- counter
    i' <- get
    b  <- rdEnv
    r  <- let ext x v f = \ n -> if n == x then v else f n
         in
           let b' = ext k params b
           in
             inEnv b' $ defunRPlus s body

    --
    -- see note on the analogous let-binding below (2009.11.10 Schulz)
    --
    init <- let initvals = mkInitsPlus s params args
            in
              return $ Left ((PCI i, s), (PCL k, s))
--              return ((PCL $ k ++ fix_init_label, s), (PCL k, s))

    return $ init : (Left ((PCL k, s), (PCI i', s))) : r

--
-- case for semifix; this is similar to fix, except that
-- there is an additional transition to an additional 'exit' state
--

defunRPlus s (CtsSemiFixApp sent (k:params) body args t) =
  do
--    i <- get   -- see log 2009.11.10
    i  <- counter
    i' <- get
    b  <- rdEnv
    r  <- let ext x v f = \ n -> if n == x then v else f n
         in
           let b' = ext k params b
           in
             inEnv b' $ defunRPlus s body

    -- it doesn't appear that let-binding below  is actually getting used;
    -- this is either a logic error or a vestige from an earlier change
    -- revist this at a later time (2009.11.10 Schulz)

    init <- let initvals = mkInitsPlus s params args
            in
              return $ Left ((PCI i, s), (PCL k, s))
--              return ((PCL $ k ++ fix_init_label, s), (PCL k, s))

    i'' <- get  -- counter is incremented by recursive call above

    cond <- return $ toGuard s sent

    -- conditional transition from k to first state inside the loop:
    first <- return $ Right (cond, ((PCL k, s), (PCI i', s)))

    -- conditional from k to next numbered state outside of loop;
    -- 'semifix guard stmt' works like 'while (guard) {stmt}'
    exit <- return $ Right (negateCond cond, ((PCL k, s), (PCI i'', s)))

--    return $ init : ((PCL k, s), (PCI i', s)) : r
    return $ init : first : exit : r



defunRPlus s (CtsReturn expr t) =
  counter >>= \i -> 
  let l = s
      r = (defunKPlus $ CtsReturn expr t) l
  in
    return [Left ((PCI i, l), (PCI $ i + 1, r))]

defunRPlus s (CtsBindNull e1 e2 _) =
  do
    r1 <- defunRPlus s e1
    r2 <- defunRPlus s e2
    return (r1 ++ r2)

defunRPlus s (CtsBind e1 x e2 _) =
  do
    r1 <- defunRPlus s e1
    r2 <- defunRPlus s e2
    return $ (defunRBindPlus x r1) ++ r2

-- Why is this still here?  (2009.11.10)
defunRPlus _ x = return [ ] -- this case is a kludge; DO NOT LEAVE IT HERE


--
-- spread "unblurred" values from the K-defunctionalizer out into
-- distinct transitions
--
spreadR :: KStatePlus -> ([BoolGuard], [KStatePlus])
spreadR k =
  let ks = unblurK k
  in
    (map fst ks, map snd ks)


--
-- old version with old types:
--

--
-- shut off to prevent extraneous type errors during work
--
-- 20.07.09 Schulz
--

{-
defunR :: KState -> CtsExpr -> M [RRule]
defunR s (CtsApp f args _)
  | isStepid f = counter >>= \ i -> let l = s
                                        r = (defunK expr) l
                                        expr = case args of
                                                 [v] -> v
                                                 _   -> badApp f
                                    in
                                      return [((PCI i, l), (PCI $ i + 1, r))]
  | signalRe == f  =
      counter >>= \ i ->
      let [v, _, rsp, ports] = take 4 s
      in
        case args of
          [psi] -> let req = (reqIdent, evalCtsExpr s psi)
                       rts = (rtsIdent, DFInt i)
                       rest = drop 5 s
                   in
                     return [
                             ((PCI i, s),
                             (PCL handlerL,[v,req,rsp,ports,rts] ++ rest))]
                               
          _     -> error "in defunR: signalRe called with too many arguments"

  | isRec f =
    rdEnv >>= \ rho ->
    let fps = rho f
        deltas = map (uncurry writeK) (zip fps (map (evalCtsExpr s) args))
        delta = foldr (.) id deltas
        (l, r) = (s, delta s)
        mkrectrans x y k i = ((PCI i, x), (PCL k, y))
    in
      counter >>= return . return . mkrectrans l r f
  | otherwise = error $ "in defunR: attempt to defunctionalize " ++
                        "non-step application " ++ "\'" ++ f ++ "\'"
defunR s (CtsFixApp (k:params) body args t) =
  do
    i <- get
    b <- rdEnv
    r <- let ext x v f = \ n -> if n == x then v else f n
         in
           let b' = ext k params b
           in
             inEnv b' $ defunR s body
    init <- let initvals = mkInits s params args
            in
              return ((PCL $ k ++ fix_init_label, s), (PCL k, s))
--              return ((PCL $ k ++ fix_init_label, initvals), (PCL k, s))
    return $ init : ((PCL k, s), (PCI i, s)) : r

defunR s (CtsReturn expr t) =
  counter >>= \ i -> let l = s
                         r = (defunK $ CtsReturn expr t) l
                      in
                        return [((PCI i, l), (PCI $ i + 1, r))]
defunR s (CtsBindNull e1 e2 _) =
  do
    r1 <- defunR s e1
    r2 <- defunR s e2
    return (r1 ++ r2)

defunR s (CtsBind e1 x e2 _) =
  do
  r1 <- defunR s e1
  r2 <- defunR s e2
  return $ (defunRBind x r1) ++ r2

defunR _ x = return [ ] -- this case is a kludge; DO NOT LEAVE IT HERE
-}

--
-- helper function used in the R-defunctionalizer bind case:
--
defunRBind :: CtsIdent -> [RRule] -> [RRule]
defunRBind v =
  liftM (\ ((i1, s1), (i2, s2)) -> ((i1, s1), (i2, upd v s2)))

--
-- same as above, with revised types:
--
--
--defunRBindPlus :: CtsIdent -> [RRulePlus] -> [RRulePlus]
--
-- revising types again (2009.11.12)
--
--
-- currently assuming only unconditional values, again (2009.11.12)
--
defunRBindPlus :: CtsIdent -> [Transition] -> [Transition]
defunRBindPlus v =
  let f t = case t of
             (Left ((i1, s1), (i2,s2)))      -> Left ((i1, s1), 
                                                      (i2, updPlus v s2))
             (Right (b, ((i1,s1), (i2,s2)))) -> Right (b,
                                                  ((i1, s1), 
                                                   (i2, updPlus v s2)))
  in
    liftM f

--  liftM (\ (Left ((i1, s1), (i2, s2))) -> Left ((i1, s1), (i2, updPlus v s2)))
--  liftM (\ (Left ((i1, s1), (i2, s2))) -> Left ((i1, s1), (i2, updPlus v s2)))

--
-- the definitions of the following functions 
-- are generated by MonadLab and located in module DefunM;
-- we use synonyms only for clarity
--

get :: M Int
get = getStoM

put :: Int -> M ( )
put = putStoM

rdEnv :: M Bindings
rdEnv = rdEnvM

inEnv :: Bindings -> M a -> M a
inEnv = inEnvM

counter :: M Int
counter = get >>= \ i -> put(i + 1) >> return i

--
-- make the initial values for a fixpoint application
--

-- shut off to prevent extraneous type errors 20.07.09
{-
mkInits :: KState -> [CtsIdent] -> [CtsExpr] -> KState
mkInits k xs vs = zip xs (map (evalCtsExpr k) vs)
-}

--
-- redone with new types:
--
mkInitsPlus :: KStatePlus -> [CtsIdent] -> [CtsExpr] -> KStatePlus
mkInitsPlus k xs vs = zip xs (map (evalCtsExprPlus k) vs)

--
-- separate a K-state of conditional values into multiple distinct states
-- guarded by conditions:
--
-- 28.07.09 Schulz
--
-- this function will return a single-element list of the KState
-- corresponds to one consisting of only unconditional values
--
-- 2009.11.12 Schulz
--
--
-- 
--
-- unblurK :: KStatePlus -> [(BoolGuard, KState)]
--
-- changed the type; unblurring still produces flat, unconditional
-- values, but we have changed to the 'Plus' type for the
-- sake of type consistency elsewhere
--
-- 2009.11.12 Schulz
--
unblurK :: KStatePlus -> [(BoolGuard, KStatePlus)]
unblurK k =
  let k'  = map (\(x, b) -> (x, severB b)) k

      -- get the list of all conditions for this state
      gcs = \x -> \cs -> case x of
                          Right _     -> cs
                          Left (c, _) -> c:cs
      cs  = nub $ foldr (++) [ ] $
              foldr ((:) . (\(_, ys) -> foldr gcs [ ] ys)) [ ] k'

      -- compare conditions in the severed state for equality;
      -- non-conditionals trivially match all conditions
      prt = \y -> \x -> case x of
                          Left (c, _) -> c == y
                          Right _     -> True

      -- separate the lists of "possible states" into distinct states;
      -- assume that each component has EXACTLY one value per condition
      -- treating non-conditionals as "wildcards",
      -- and reserving a special "always true" case for unconditionals
      pss = foldr
              ((:) .
                (\c -> map (\(x, ys) -> (x, head $ filter (prt c) ys)) k'))
              [ ] cs

      -- project out of 'Either'
      une = \x -> case x of
                    Left (_, y) -> (V y)
                    Right y     -> (V y)

      in
        (BGConstant True, k) :
          (zip cs $ map (\xs -> map (\(x, ys) -> (x, une ys)) xs) pss)





-- THIS IS THE END OF THE FILE --
