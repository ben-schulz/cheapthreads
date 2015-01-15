--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/DFun/DFunK.hs
--
-- the state-layer ("K") defunctionalizer
--
-- put here 2010.02.15
--
-- Schulz
--

module CT.DFun.DFunK where


import CT.DFun.FSM

import CT.ANAST
import CT.INAST


--
-- top-level call to the K-defunctionalizer:
--
-- produce a tree of state-actions (i.e. Mealy transductions)
-- from a K-typed term; each leave of the tree corresponds
-- to the body of an FSMLang transition whose guard corresponds
-- to a path through the tree
--
--
-- three syntactic transformations are performed on the input term,
-- namely:
--
--   +  'liftcond': hoisting of if-then-else occuring in the
--      non-monadic argument of 'put' or return using:
--
--        put G (if b then x else y)  <==>  if b then (put G x) else (put G y)
--
--        eta (if b then x else y)  <==>  if b then (eta x) else (eta y)
--
--  +  'liftcase': a similar hoisting, but for 'case' expressions;
--     note that the result of applying this transformation after 'liftcond'
--     is to place all 'if-then-else' scopes above 'get', 'put', and 'return',
--     and to place all 'case' expressions above 'if-then-else'
--
--  +  'rassoc': right association of all binds in the input term,
--     so that the term resembles a (right-recursive) list structure
--     built using (>>=) and (>>) as connectives.  This transformation
--     is a simple application of the familiar monad laws.
--
--  'dfunk' itself produces a tree-like structure that reflects the control
--  flow necessary to realize any conditional assignments, with all
--  CT syntactic structures (which are presumed well-typed) converted into
--  FSMLang assignments.
--
dfunk :: INAST -> KSplit STMod
dfunk k =
  let k' = (mksplit . rassocbind . liftcase . liftcond) k
  in
    splitmap tostmod k'



--
-- transform a K-typed term into the intermediate
-- state-modifier representation used to generate the
-- body of an FSMLang transition:
--

tostmod :: INAST -> STMod

tostmod (CTGetIN x _)      = [(Sig retval, MX $ FSMSig x)]

tostmod (CTPutIN x e _)    = [(Sig retval, MX FSMUnit),
                             (Sig x,      MX $ toFSMExpr e)]
                          
tostmod (CTReturnIN e _)   = [(Sig retval, MX $ toFSMExpr e)]

tostmod (CTReadIN m i _)   = [(Sig retval, MRef m $ toFSMExpr i)]

tostmod (CTWriteIN m i e _)  = [(Sig retval, MX FSMUnit),
                                (Mem m (toFSMExpr i), MX $ toFSMExpr e)]


--
-- sum-type for propagating conditions upward
-- to the state-transition type;
--
-- the tree structure is isomorphic to the transitions
-- that will result at the higher levels
--
data KSplit a = K (SplitNode a)
              
              -- " e >>= \x -> e' "
              | KBind (SplitNode a) String (KSplit a)

              -- " e >> e' "
              | KNullBind (SplitNode a) (KSplit a)


data SplitNode a = R1 a  -- anything not involving an "if-then-else"

                 -- "if b then x else y"
                 | R2 BoolExpr (SplitNode a) (SplitNode a)


--
-- map a function onto the leaves of the tree:
--
splitmap :: (a -> b) -> KSplit a -> KSplit b
splitmap f (KBind e x r)   = KBind (nodemap f e) x (splitmap f r)
splitmap f (KNullBind e r) = KNullBind (nodemap f e) (splitmap f r)
splitmap f (K x)           = K (nodemap f x)

nodemap :: (a -> b) -> (SplitNode a) -> (SplitNode b)
nodemap f (R1 x)     = R1 (f x)
nodemap f (R2 b x y) = R2 b (nodemap f x) (nodemap f y)


--
-- a syntactic transformation that removes conditional expressions
-- from the arguments of 'put' and 'return', so that all actions
-- on state components of the FSM are strictly unconditional
--
-- essentially, we just lift all conditional expressions that might
-- (and legally could) appear as the argument to one of 'get', 'put'
-- or 'return', and use the lifted expressions to form a tree structure
-- reflecting the low-level control flow implied by the K-action
--
-- see log (2010.02.16) for more details;
--
-- REVISION: see also log (2010.03.15), in which the
-- details of the transformation have been changed,
-- in reaction to the discovery that the original
-- transformation was incorrect.
--
-- 2010.03.15 Schulz
--
liftcond :: INAST -> INAST

-- the unary cases:
liftcond (CTPutIN x e t) =
  case (liftcond e) of

    --
    -- put (if b then x else y) <==> if b then (put x) else (put y)
    --
    (CTBranchIN b a a' _) -> CTBranchIN b
                               (liftcond $ CTPutIN x a t)
                               (liftcond $ CTPutIN x a' t) t

    _                      -> CTPutIN x e t

liftcond (CTReturnIN e t) =
  case (liftcond e) of

    --
    -- return (if b then x else y) <==> if b then (return x) else (return y)
    --
    (CTBranchIN b a a' _) -> CTBranchIN b
                                (liftcond $ CTReturnIN a t)
                                (liftcond $ CTReturnIN a' t) t

    _                      -> CTReturnIN e t

liftcond (CTPrim1aryIN op e t) =
  case (liftcond e) of

    --
    -- op (if b then x else y) <==> if b then (op x) else (op y)
    --
    (CTBranchIN b a a' _) -> CTBranchIN b
                                (liftcond $ CTPrim1aryIN op a t)
                                (liftcond $ CTPrim1aryIN op a' t) t

    _                      -> CTPrim1aryIN op e t



liftcond (CTPrim2aryIN op e e' t) =

  case (liftcond e, liftcond e') of
  (CTBranchIN b x y _, CTBranchIN b' x' y' t') -> CTBranchIN b

                                                    (CTBranchIN b'

                                                      (liftcond $
                                                        CTPrim2aryIN op x x' t')

                                                      (liftcond $
                                                        CTPrim2aryIN op x y' t')
                                                      t
                                                    )

                                                    (CTBranchIN b'
                                                      (liftcond $
                                                        CTPrim2aryIN op y x' t')

                                                      (liftcond $
                                                        CTPrim2aryIN op y y' t')
    
                                                      t
                                                    )
                                                      t


  -- conditional on the left:
  --
  -- (if b then x else y) 'op' z  <==>  if b then (x 'op' z) else (y 'op' z)
  --
  (CTBranchIN b x y _, z)                        -> CTBranchIN b

                                                      (liftcond $
                                                        CTPrim2aryIN op x z t)

                                                      (liftcond $
                                                        CTPrim2aryIN op y z t) t

  -- conditional on the right:
  --
  -- x 'op' (if b then y else z)  <==>  if b then (x 'op' y) else (x 'op' z)
  --
  (x, CTBranchIN b y z t')                        -> CTBranchIN b

                                                       (liftcond $
                                                         CTPrim2aryIN op x y t')

                                                       (liftcond $
                                                         CTPrim2aryIN op x z t')
                                                       t

  -- no conditionals, no change:
  _                                               -> CTPrim2aryIN op e e' t


-- anything else simply propagates up
liftcond x = x




liftcase :: INAST -> INAST

-- the unary cases:
liftcase (CTPutIN x e t) =
  case (liftcase e) of

    (CTCaseIN y alts _)    -> CTCaseIN y
                                (map
                                  (\(p, a) ->
                                    (p, liftcase $ CTPutIN x a t)) alts) t
                                  

    _                      -> CTPutIN x e t

liftcase (CTReturnIN e t) =
  case (liftcase e) of

    (CTCaseIN y alts _)    -> CTCaseIN y
                                (map
                                  (\(p, a) ->
                                    (p, liftcase $ CTReturnIN a t)) alts) t

    _                      -> CTReturnIN e t

liftcase (CTPrim1aryIN op e t) =
  case (liftcase e) of

    (CTCaseIN y alts _)    -> CTCaseIN y
                                (map
                                  (\(p, a) ->
                                    (p, liftcase $ CTPrim1aryIN op a t)) alts) t

    _                      -> CTPrim1aryIN op e t



liftcase (CTPrim2aryIN op e e' t) =

  case (liftcase e, liftcase e') of

  -- 
  -- both conditionals:
  --
  (CTCaseIN m alts t', CTCaseIN m' alts' t'') -> let l   = map (\(p, a) ->
                                                                (p, liftcase a))

                                                     as  = l alts

                                                     c'  = CTCaseIN m'
                                                             (l alts') t''

                                                     as' = foldr
                                                           (\(p, a) -> \as ->

                                                             (p,
                                                              liftcase $
                                                               CTPrim2aryIN op
                                                                 a c' t):as

                                                           ) [] as

                                                 in
                                                   CTCaseIN m as' t'


  --
  -- conditional on the left:
  --
  (CTCaseIN m alts _, z)                      -> let alts' = foldr
                                                             (\(p, a) -> \as ->

                                                               (p,
                                                                 liftcase $
                                                                  CTPrim2aryIN
                                                                    op
                                                                      a z t):as

                                                             ) [] alts
                                                 in
                                                   CTCaseIN m alts' t


  --
  -- conditional on the right:
  --
  (x, CTCaseIN m alts _)                      -> let alts' = foldr
                                                             (\(p, a) -> \as ->

                                                               (p,
                                                                 liftcase $
                                                                  CTPrim2aryIN
                                                                    op
                                                                      x a t):as

                                                             ) [] alts
                                                 in
                                                   CTCaseIN m alts' t




  -- no conditionals, no change:
  _                                               -> CTPrim2aryIN op e e' t



-- anything else simply propagates up
liftcase x = x






--
-- split a lifted-conditional K-term up into a tree-structure
-- isomorphic to the transition behavior it specifies in FSMLang;
--
-- this structure is used to produce the appropriate guarded transitions
-- at the resumptive level;
--
-- this consists of two parts: first, actions within binds are collected
-- into a list-like structure; second, actions containing conditions are
-- split into tree-like structures residing within the list.  The result
-- is something like an eccentric DAG, in which there is a unique
-- initial and terminal node, and in which some nodes may temporarily
-- fork along parallel paths before rejoining
--
-- see log (2010.02.16) for more details, and some discussion of the issues
--
-- see also log (2010.03.16) for more issues, and revisions
--


--
-- we assume, here, that every K-term can be decomposed in
-- terms of left-associative binds:
--
mksplit :: INAST -> KSplit INAST
mksplit (CTBindIN e e' _) =
  case e' of
    (CTLamIN x e'' _) -> KBind (splitcond e) x (mksplit e'')
    _                 -> error $ "\nNeed to write procedure calls for DFunK!\n"

mksplit (CTNullBindIN e e' _) = KNullBind (splitcond e) (mksplit e')

--
-- this corresponds to the final term in the bind:
--
mksplit x = K (splitcond x)



--
-- split lifted-conditional K-actions into
-- binary trees with CT expressions at the leaves and
-- boolean expressions at the internal nodes:
--
splitcond :: INAST -> SplitNode INAST

-- this is where all branches in the tree originate:
splitcond (CTBranchIN b e e' t) = R2 (toBoolExpr b) (splitcond e) (splitcond e')

-- primitives:
splitcond (CTPrim1aryIN op e t)    = downpropun (CTPrim1aryIN op)
                                                (splitcond e) t
splitcond (CTPrim2aryIN op e e' t) = downpropbin (CTPrim2aryIN op)
                                                 (splitcond e) (splitcond e') t

splitcond (CTReturnIN e t)      = downpropun CTReturnIN (splitcond e) t
splitcond (CTPutIN x e t)       = downpropun (CTPutIN x) (splitcond e) t

-- anything that belongs here and doesn't take an expression argument
-- is necessarily unconditional:
splitcond x = R1 x




--
-- propagate a binary connective downard:
--
downpropbin :: (INAST -> INAST -> AN -> INAST) ->
               SplitNode INAST -> SplitNode INAST -> AN -> SplitNode INAST

downpropbin f (R2 b x y) z t = R2 b (downpropbin f x z t) (downpropbin f y z t)
downpropbin f x (R2 b y z) t = R2 b (downpropbin f x y t) (downpropbin f x z t)
downpropbin f (R1 x) (R1 y) t = R1 (f x y t)


-- propagate a unary connective downward:
downpropun :: (INAST -> AN -> INAST) -> SplitNode INAST -> AN -> SplitNode INAST
downpropun f (R2 b x y) t = R2 b (downpropun f x t) (downpropun f y t)
downpropun f (R1 x) t     = R1 (f x t)



--
-- reassociate (abstract) binds to the right
-- i.e. so that a term has the same recursive structure as a list
--
rassocbind :: INAST -> INAST
rassocbind (CTBindIN e e' t) =

  case (rassocbind e) of

    (CTBindIN f (CTLamIN x f' t')  t'') -> CTBindIN f
                                             (CTLamIN x
                                               (rassocbind
                                                 (CTBindIN f' e' t'')) t') t
                                                 
    (CTBindIN f f' t')                  -> CTBindIN f
                                             (rassocbind
                                               (CTBindIN f' e' t')) t
                                                 


    (CTNullBindIN f f' t')              -> CTNullBindIN f
                                              (rassocbind
                                                (CTBindIN f' e' t')) t
                                                 

    _                                   -> CTBindIN e (rassocbind e') t


-- again, same as for bind:
rassocbind (CTNullBindIN e e' t) =

  case (rassocbind e) of

    (CTBindIN f (CTLamIN x f' t')  t'') -> CTBindIN f
                                             (CTLamIN x
                                               (rassocbind
                                                 (CTNullBindIN f' e' t'')) t') t
                                                 
    (CTBindIN f f' t')                  -> CTBindIN f
                                             (rassocbind
                                               (CTNullBindIN f' e' t')) t
                                                 


    (CTNullBindIN f f' t')              -> CTNullBindIN f
                                              (rassocbind
                                                (CTNullBindIN f' e' t')) t
                                                 

    _                                   -> CTNullBindIN e (rassocbind e') t



-- anything not consisting of a bind 
rassocbind x = x




-- THIS IS THE END OF THE FILE --
