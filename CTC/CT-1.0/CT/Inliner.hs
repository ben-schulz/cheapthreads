--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Inliner.hs
--
-- a maximally aggressive inliner;
--
-- this code transforms the list of function declarations output by the
-- parser-typechecker into a single term rooted in the 'main' function
--
-- At the moment, we assume that there is no mutual
-- recursion, i.e. if f calls g, then g does not call f.
--
--
-- put here 2010.02.05
--
-- Schulz
--

module CT.Inliner where

import CT.Syntax
import CT.INAST
import CT.ANAST
import CT.TypeChecker

import CT.MonadicConstructions


--
-- top-level call to the inliner:
--
--inline :: ANProg -> INProg
--inline = prj_fe . inline_interp . toinprog
inline = prj_fe . inline_interp . noinline
  


--inline_interp :: ANProg -> FE INProg
inline_interp (INProg ((d@(INFunDec ((f, t), (xs, _))), ds), (dats, mons))) =

{-
  let (mn:fs)   = map (\((x, y), (z, w)) ->
                        (INFunDec ((x, y), (z, toinast w)))) (d:ds)
-}

  let (mn:fs)   = (d:ds)

      -- produce representation of all declared functions as lambdas:
      (mn':fs') = map funtolam (mn:fs)
  in

    -- make the initial environment, binding
    -- function identifiers to their corresponding lambdas:
    mkfenv (mn':fs') >>= \rho ->

    -- starting from this environment, do the inlining:
    inEnv rho
    (
      foldr
        (\(INFunDec ((f, t), (ps, a))) -> \m ->

          beta_rx a >>= \a' ->       -- inline the function body

          -- update the environment to reflect inlining done:
          extfenv f
            (snd $ funtolam (INFunDec ((f, t), (ps, a')))) >>= \rho' ->

          inEnv rho' m               -- do the rest, in the updated env
        )

          -- return the resulting AST, rooted in main;
          -- we use the non-lambdified 'mn', since otherwise
          -- would result in duplicate parameters

          (let mn'' = (\(INFunDec x) -> x) mn
            in
            (beta_rx (snd $ snd mn''))
          )

            fs

    ) >>= \ast ->

    return $ INProg ((INFunDec ((f, t), (xs, ast)), []), (dats, mons))


--
-- interpret the annotated AST in a way that produces
-- beta reduction and evaluation of all variables
-- that reference declared functions (variables that
-- do NOT correspond to declared functions are not evaluated)
--
beta_rx :: INAST -> FE INAST

--
-- the following three cases are the important ones:
--

-- application:

                           -- special case for transforming 'fix',
                           -- getting rid of application and moving
                           -- initial-state arguments inside the production:

beta_rx (CTAppIN (CTFixIN a t) a' t')    = beta_rx a >>= \b ->
                                           beta_rx a' >>= \b' ->

                                           let f = CTFixIN b t
                                           in
                                             return $ CTFixAppIN f [b'] t'

beta_rx e@(CTAppIN a a' t) | isfixapp e  =

                             beta_rx a >>= \(CTFixAppIN b bs _) ->
                             beta_rx a' >>= \b' ->
                             return (CTFixAppIN b (bs ++ [b']) t)

                           -- look up a function identifier in the environment,
                           -- and apply beta-reduction to the result
                           | isvarapp e  =

                             let k = nameofvarapp a
                             in
                               rdEnv >>= \rho ->
                               case (rho k) of

                                 (Left b)       -> beta_rx (CTAppIN b a' t)
  
                                 -- this case should only correspond to
                                 -- application of the loop-function in 'fix':

                                 (Right Wrong)  -> beta_rx a >>= \b ->
                                                   beta_rx a' >>= \b' -> 
                                                   return $
                                                   CTRecAppIN b b' t

                           -- normal beta-reduction:
                           | otherwise =

                             beta_rx a' >>= \b ->
                             pusharg b >>
                             beta_rx a

-- lambdas:

beta_rx (CTLamIN x e t) = poparg >>= \a' ->
                          case a' of

                            -- in this case, the lambda is actually
                            -- being applied to something:
                            (Just a) -> extfenv x a >>= \rho ->
                                        inEnv rho (beta_rx e)

                            -- in this case, the lambda stays
                            -- where it is, i.e. it is the header
                            -- of a 'fix' or a function declared
                            -- as a lambda:
                            Nothing  -> beta_rx e >>= \e' ->
                                        return (CTLamIN x e' t)


-- get the body of a function, if applicable
-- (we need this case for the possibility of
-- nullary declarations, e.g. constants):
beta_rx v@(CTVarIN x _)  = rdEnv >>= \rho ->
                           case (rho x) of
                             Right Wrong -> return v
                             Left f      -> return f


--
-- the rest are a completely straightforward
-- crawl over the tree::
--

-- the monad operations:
beta_rx (CTBindIN a a' t)        = beta_rx a >>= \b ->
                                   beta_rx a' >>= \b' ->
                                   return (CTBindIN b b' t)

beta_rx (CTNullBindIN a a' t)    = beta_rx a >>= \b ->
                                   beta_rx a' >>= \b' ->
                                   return (CTNullBindIN b b' t)

beta_rx (CTReturnIN a t)         = beta_rx a >>= \b -> 
                                   return (CTReturnIN b t)

beta_rx (CTPutIN x a t)          = beta_rx a >>= \b ->
                                   return (CTPutIN x b t)

beta_rx (CTStepIN a t)           = beta_rx a >>= \b ->
                                   return (CTStepIN b t)

beta_rx (CTResumeIN a t)         = beta_rx a >>= \b ->
                                   return (CTResumeIN b t)

beta_rx (CTResumeReIN a a' t)    = beta_rx a >>= \b ->
                                   beta_rx a' >>= \b' -> 
                                   return (CTResumeReIN b b' t)

beta_rx (CTLoopIN a t)           = beta_rx a >>= \b ->
                                   return (CTLoopIN b t)

beta_rx (CTLoopAppIN r as t)     = (foldr
                                     (\a -> \m ->
                                       beta_rx a >>= \b ->
                                       m >>= \bs ->
                                       return (b:bs)
                                     ) (return []) as

                                   ) >>= \bs ->

                                   beta_rx r >>= \r' ->
                                   return (CTLoopAppIN r' bs t)

beta_rx (CTFixIN a t)            = beta_rx a >>= \b ->
                                   return (CTFixIN b t)

beta_rx (CTFixAppIN a as t)      = beta_rx a >>= \b ->

                                   (
                                     foldr
                                     (\a' -> \m ->
                                       beta_rx a' >>= \b' ->
                                       m >>= \bs' ->
                                       return (b':bs')
                                     )
                                       (return []) as

                                   ) >>= \bs ->
                                   return $ CTFixAppIN b bs t


beta_rx (CTSignalIN a t)         = beta_rx a >>= \b ->
                                   return (CTSignalIN b t)


beta_rx (CTGetReqIN a t)         = beta_rx a >>= \b ->
                                   return (CTGetReqIN b t)

beta_rx (CTPrim1aryIN op a t)    = beta_rx a >>= \b ->
                                   return (CTPrim1aryIN op b t)

beta_rx (CTPrim2aryIN op a a' t) = beta_rx a >>= \b ->
                                   beta_rx a' >>= \b' ->
                                   return (CTPrim2aryIN op b b' t)

beta_rx (CTPrim3aryIN op a a' a'' t) = beta_rx a >>= \b ->
                                       beta_rx a' >>= \b' ->
                                       beta_rx a'' >>= \b'' ->
                                       return (CTPrim3aryIN op b b' b'' t)

beta_rx (CTBranchIN g a a' t)    = beta_rx g >>= \g' ->
                                   beta_rx a >>= \b ->
                                   beta_rx a' >>= \b' ->
                                   return (CTBranchIN g' b b' t)

beta_rx (CTCaseIN o ((p,a):as) t)   = beta_rx o >>= \o' -> 
                                      beta_rx a >>= \b ->

                                      (
                                      foldr
                                        (\(p,a) -> \m -> 

                                          beta_rx a >>= \b ->
                                          m >>= \bs ->
                                          return ((p,b):bs)
                                        )

                                          (return [(p,b)])
                                            as

                                      ) >>= \as' ->
                                      return (CTCaseIN o' as' t)

beta_rx (CTPairIN a a' t) = beta_rx a >>= \b ->
                            beta_rx a' >>= \b' ->
                            return (CTPairIN b b' t)


beta_rx (CTListIN as t)   = (
                              foldr
                                (\a -> \m ->

                                  beta_rx a >>= \b ->
                                  m >>= \bs ->
                                  return (b:bs)
                                )
                                  (return [])
                                    as

                            ) >>= \as' ->

                            return (CTListIN as' t)


--
-- default case: syntactic productions
-- that don't involve an expression as an argument
-- are invariant under inlining.
--
beta_rx a = return a



--
-- top-level call to the default pass
-- i.e. mark recursive calls but don't inline
--
--noinline :: ANProg -> INProg
noinline = prj_re . noinline_interp



noinline_interp :: INProg -> RE INProg
noinline_interp (INProg ((mn, fs), (dats, mons))) =

    -- starting from the empty environment, crawl the tree
    -- of the body of each function dec and mark all recursive calls:
    inEnv initrenv
    (
      foldr
        (\(INFunDec ((f, t), (ps, a))) -> \m ->

          tagrec a >>= \a' ->       -- crawl the ast
          m >>= \ds ->
          return ((INFunDec ((f, t), (ps, a'))):ds)
        )
          (return []) (mn:fs)

    ) >>= \(mn':fs') ->

    return $ INProg ((mn', fs'), (dats, mons))



--
-- TAG RECURSIVE CALLS
--
-- this is the default pass that occurs in place of the inliner;
-- only recursive applications are marked as such; no other chnages occur
--

--
-- this function is deprecated, due to the abandonment of 'fix'
-- as our iterative operator
--
-- (2010.09.21) Schulz
--
tagrec :: INAST -> RE INAST

-- application:

--
-- check whether an applied variable is a tail-call:
--
tagrec (CTAppIN (CTVarIN x t) a' t') = rdEnv >>= \rho ->
                                       tagrec a' >>= \b' ->
                                       if (rho x)
                                       then
                                         return $ CTRecAppIN (CTVarIN x t) b' t'
                                       else
                                         return $ CTAppIN (CTVarIN x t) b' t'


tagrec (CTAppIN a a' t) = tagrec a >>= \b ->
                          tagrec a' >>= \b' ->

                          case b of

                             -- the recursive mark propagates to the
                             -- entire application, which associates left:
                             -- 
                             (CTRecAppIN _ _ _) -> return $ CTRecAppIN b b' t

                             -- otherwise, no recursion, leave it
                             _                  -> return $ CTAppIN b b' t


tagrec (CTFixAppIN a as t) = tagrec a >>= \b ->

                             (
                               foldr
                               (\a' -> \m ->

                                 tagrec a' >>= \b' ->
                                 m >>= \bs' ->
                                 return (b':bs')

                               )
                                 (return []) as

                             ) >>= \bs ->

                             return $ CTFixAppIN b bs t


tagrec (CTFixIN a t)    = let k = lampof a
                          in

                            -- put the first paramter in the
                            -- environment of recursives,
                            scoperec k >>= \rho ->

                            -- traverse the loop body:
                            inEnv rho (tagrec a) >>= \b ->
                            return (CTFixIN b t)



--
-- everything else is nothing more than a
-- straightforward crawl over the tree:
--

-- lambdas:

tagrec (CTLamIN x e t) =           tagrec e >>= \e' ->
                                   return $ CTLamIN x e' t

-- the monad operations:
tagrec (CTBindIN a a' t)        = tagrec a >>= \b ->
                                  tagrec a' >>= \b' ->
                                  return (CTBindIN b b' t)

tagrec (CTNullBindIN a a' t)    = tagrec a >>= \b ->
                                  tagrec a' >>= \b' ->
                                  return (CTNullBindIN b b' t)

tagrec (CTReturnIN a t)         = tagrec a >>= \b -> 
                                  return (CTReturnIN b t)

tagrec (CTPutIN x a t)          = tagrec a >>= \b ->
                                  return (CTPutIN x b t)

tagrec (CTStepIN a t)           = tagrec a >>= \b ->
                                  return (CTStepIN b t)

tagrec (CTResumeIN a t)         = tagrec a >>= \b ->
                                  return (CTResumeIN b t)

tagrec (CTLoopIN a t)           = tagrec a >>= \b ->
                                  return (CTLoopIN b t)

tagrec (CTSignalIN a t)         = tagrec a >>= \b ->
                                  return (CTSignalIN b t)

tagrec (CTPrim1aryIN op a t)    = tagrec a >>= \b ->
                                  return (CTPrim1aryIN op b t)

tagrec (CTPrim2aryIN op a a' t) = tagrec a >>= \b ->
                                  tagrec a' >>= \b' ->
                                  return (CTPrim2aryIN op b b' t)

tagrec (CTPrim3aryIN op a a' a'' t) = tagrec a >>= \b ->
                                      tagrec a' >>= \b' ->
                                      tagrec a'' >>= \b'' ->
                                      return (CTPrim3aryIN op b b' b'' t)

tagrec (CTBranchIN g a a' t)    = tagrec g >>= \g' ->
                                  tagrec a >>= \b ->
                                  tagrec a' >>= \b' ->
                                  return (CTBranchIN g' b b' t)

tagrec (CTCaseIN o ((p,a):as) t)   = tagrec o >>= \o' -> 
                                     tagrec a >>= \b ->

                                     (
                                      foldr
                                        (\(p,a) -> \m -> 

                                          tagrec a >>= \b ->
                                          m >>= \bs ->
                                          return ((p,b):bs)
                                        )

                                          (return [])
                                            as

                                      ) >>= \as' ->
                                      return (CTCaseIN o' ((p,b):as') t)

tagrec (CTPairIN a a' t) = tagrec a >>= \b ->
                           tagrec a' >>= \b' ->
                           return (CTPairIN b b' t)


tagrec (CTListIN as t)   = (
                             foldr
                               (\a -> \m ->

                                 tagrec a >>= \b ->
                                 m >>= \bs ->
                                 return (b:bs)
                               )
                                 (return [])
                                   as

                           ) >>= \as' ->

                           return (CTListIN as' t)


--
-- default case: syntactic productions
-- that don't involve an expression as an argument
-- are invariant under inlining.
--
tagrec a = return a




--                           --
-- DATA STRUCTURES USED HERE --
--                           --


--
-- INLINING PASS MONAD
--



--
-- we structure the inliner in a way similar
-- to a monadic interpreter (as in the type inferencer);
--
-- interpretation here just corresponds to beta reduction
-- on any instance of 'CTAppIN' and evaluation of variables
-- in an environment consisting of declared functions
--
--

type FEnv = CTIdent -> Either INAST Wrong

type FE a = EnvT FEnv (StateT [INAST] Id) a

unleft :: Either a b -> a
unleft (Left x) = x


-- this is isn't really "wrong"; 
-- it's just a place-holder
-- that works essentially like 'Nothing':
--
data Wrong = Wrong deriving Show


--
-- project out of the monad:
--
prj_fe :: FE a -> a
prj_fe (ENV x) = fst $ deId ((deST (x (initfenv))) [])


--
-- the initial environment;
--
-- by convention, everything is mapped to 'Wrong';
-- we might want to enforce this with a static
-- check for declared function, since 'Wrong'
-- just directs the interpreter not to evaluate a variable
--

initfenv :: FEnv
initfenv = \_ -> Right Wrong


--
-- extend the environment:
--
extfenv :: CTIdent -> INAST -> FE FEnv
extfenv x a =
  rdEnv >>= \rho ->
  return (tweek x (Left a) rho)  -- 'tweek' defined in TypeChecker


--
-- push an argument onto the stack:
--
pusharg :: INAST -> FE ()
pusharg a =
  liftEnv
  (
    get >>= \as ->
    upd (\_ -> (a:as)) >>
    return ()
  )

--
-- pop an argument off the stack:
--
-- note that we use a "safe-pop";
-- this is because we may encounter
-- an empty stack for some lambdas,
-- e.g. the one appearing inside of a 'fix'
--
poparg :: FE (Maybe INAST)
poparg =

  liftEnv
  (
    get >>= \as ->
    (
      upd (\_ -> case as of
                   (_:xs) -> xs
                   []     -> []
          )

    ) >>

    return (
             case as of
               (x:_) -> Just x
               []    -> Nothing
           )
  )



--
-- DEFAULT PASS MONAD
--

--
-- a simpler monad, which we use for the default, non-inlining pass;
-- this maintains an environment of recursively bound identifiers
--

type REnv = CTIdent -> Bool

type RE = EnvT REnv Id

--
-- by default, everything is assumed NOT to be a recursive call
--
initrenv :: REnv
initrenv = \_ -> False

--
-- extend the environment:
--
extrenv :: CTIdent -> Bool -> RE REnv
extrenv x a =
  rdEnv >>= \rho ->
  return (tweek x a rho)  -- 'tweek' defined in TypeChecker

--
-- mark a variable as a recursive call:
--
scoperec :: CTIdent -> RE REnv
scoperec x = extrenv x True

--
-- project out of the monad:
--
prj_re :: RE a -> a
prj_re (ENV x) = deId (x initrenv)


--                --
-- INITIALIZATION -- 
--                --


--
-- make the initial environment from the output of the typechecker:
--
mkfenv :: [((CTIdent, CTTy), INAST)] -> FE FEnv
mkfenv =

  foldr

  (\d -> \m ->

    extfenv (fst $ fst d) (snd d) >>= \rho ->
    inEnv (rho) m
  )
  (rdEnv)


--
-- this takes the parameters appearing in the function
-- declaration header and turns them into parameters in
-- a lambda expression; i.e.
--
--   f x y = expr
--
-- becomes:
--
--   f = \x -> \y -> expr
--
-- this is to facilitate the inlining procedure above
-- 
--
funtolam  :: INFunDec -> ((CTIdent, CTTy), INAST)
funtolam (INFunDec ((f, t), (xs, a))) =

  let ts  = zip xs (abstolist t)

      a' = foldr
             (\(x, t) -> \e -> CTLamIN x e (CTAbsTy t (typeofinast e)))
               a ts
  in
    ((f, t), a')
  
    
--
-- turn an arrow type into a list of types:
--
abstolist :: CTTy -> [CTTy]
abstolist (CTAbsTy a b) = a:(abstolist b)
abstolist t             = [t]


--
-- pick out an application as involving
-- 'fix' or not:
--
isfixapp :: INAST -> Bool
isfixapp (CTAppIN a@(CTAppIN _ _ _) _ _) = isfixapp a
isfixapp (CTAppIN (CTFixIN _ _) _ _)   = True

isfixapp _ = False


--
-- get the recursive binding out of a 'fix' header:
--
fixrecof :: INAST -> CTIdent
fixrecof (CTFixIN (CTLamIN x _ _) _) = x


--
-- simple break-out case for variables in 'beta_rx' 
--
isvarapp :: INAST -> Bool
isvarapp (CTAppIN (CTVarIN _ _) _ _) = True
isvarapp (CTAppIN a _ _)             = isvarapp a
isvarapp _ = False

nameofvarapp :: INAST -> CTIdent
nameofvarapp (CTAppIN a _ _) = nameofvarapp a
nameofvarapp (CTVarIN x _)   = x



-- THIS IS THE END OF THE FILE --
