--
-- this is ~/cheapthreads/CTC/CT-1.0/RSPLam/Compile/ScopeVars.hs
--
-- a simple alpha-conversion on the AST that makes scope-behavior
-- explicit by ensuring that all variables have unique identifiers
--
-- lifted out of the CT compiler and slightly modified for use with
-- the RPS demonstration compiler
--
-- copied here 2010.12.28
--
-- Schulz
--

module Compile.ScopeVars where

import Compile.RSyntax

import MonadicConstructions


--
-- top-level call:
--

{-
scopevars :: Prog -> Prog
scopevars p@(Prog ((mn, fs), (dats, mons))) =

  prj_sv $

  (

    let fns = funnames p  -- collect declared function names
    in

    -- make an initial keylist accounting for all declared
    -- function identifiers:
    (
      foldr
      (\f -> \m ->

        incvar f >>= \n ->
        extvenv f n >>= \rho ->
        inEnv rho m >>= \rho' ->
        return rho'
      )
        (rdEnv) fns

    ) >>= \rho ->

    inEnv rho
    (

    foldr
    (\(FunDec ((f, t), (xs, e))) -> \m ->

      -- tag the string in the function declaration
      -- for consistency with markings in the expression body
      let f' = f ++ (show initvct)
      in

      -- make a new scope consisting of the function parameters:
      (
        foldr
        (\x -> \m ->

          incvar x >>= \n ->
          extvenv x n >>= \rho ->

          let x' = markvar x n
          in
            inEnv rho m >>= \(rho, xs') ->
            return (rho, (x':xs'))
        )
          (rdEnv >>= \rho -> return (rho, []))
            xs

      ) >>= \(rho, xs') ->


      -- interpret the function body in the new variable scope:
      inEnv rho (sv_interp e) >>= \e' ->
      m >>= \fs' ->

      let d' = (FunDec ((f', t), (xs', e')))
      in
        return (d':fs')

    )
      (return []) (mn:fs)

  ) >>= \(mn':fs') ->

  return $ Prog ((mn', fs'), (dats, mons))
  )
-}


--
-- each identifier is mapped to a counter in some environment;
-- the counter is incremented each time a new scope
-- involving that variable is encountered
--
-- the counter is used to tag repeated variables in different
-- scopes with unique integer suffixes
--
--
data Binding = Var
             | Rec
             deriving Show

type VEnv = CTIdent -> (Int, Binding)

type SV a = EnvT VEnv (StateT [(CTIdent, Int)] Id) a

initvenv :: VEnv
initvenv = \_ -> (0, Var)

initvct :: Int
initvct = 0

--
-- project out of the monad
--
prj_sv :: SV a -> a
prj_sv (ENV x) = fst $ deId ((deST (x (initvenv))) [])



--
-- counter value of a given variable:
--
ctof :: String -> SV Int
ctof x =
  liftEnv $ 
    get >>= \s -> case lookup x s of
                    Nothing -> return 0
                    Just n  -> return n

--
-- increment a scope-counter in the keylist:
--
incvar :: CTIdent -> SV Int
incvar v =

  liftEnv $

    get >>= \vs ->

    case (lookup v vs) of

      -- if the variable is in the keylist, increment its counter
      -- and return the new value:
      (Just n) -> upd
                    (\ss ->

                      map
                        (\(x, u) -> if x /= v then (x, u) else (x, u + 1))
                          ss
                    ) >>
                    return (n + 1)

      -- if the variable isn't present, add it
      -- at the initial counter value:
      Nothing       -> upd (\ss -> (v, initvct):ss) >> return initvct


markvar :: CTIdent -> Int -> CTIdent
--markvar x n = x ++ (show n)
markvar x _ = x


--
-- extend the environment:
--
extvenv :: CTIdent -> Int -> SV VEnv
extvenv x v = rdEnv >>= \rho ->
              case (rho x) of
                (_, b) -> return $ tweek rho x (v, b)

markrec :: CTIdent -> Int -> SV VEnv
markrec x v = rdEnv >>= \rho ->
              return $ tweek rho x (v, Rec)

tweek :: (Eq a) => (a -> b) -> a -> b -> (a -> b)
tweek f x v = \y -> if y == x then v else f y



--
-- the basic rules and procedure:
--
--   + every declared function represents a new scope
--     containing its declared parameters;
--
--   + every lambda in an expression represents a new scope
--     containing its formal parameter;
--
--   + every alternative in a 'case' statement represents a new scope
--     containing all pattern variables in its matching pattern;
--
-- Every identifier appearing in the code is associated to
-- an integer counter in a keylist carried by the State component.
-- Each time a new scope is entered, the tree crawl proceeds in
-- a new environment in which all variables being added are associated
-- to their current keylist-counter value plus one.  This disambiguates
-- variables occuring in nested scopes.
--

sv_interp :: CTExpr -> SV CTExpr


sv_interp (CTApp a@(CTVar x) a') = rdEnv >>= \rho ->
                                   sv_interp a >>= \b ->
                                   sv_interp a' >>= \b' ->
                                   case (rho x) of

                                      (_, Rec) -> return (RecApp b b')

                                      _        -> return (CTApp b b')


sv_interp (CTApp a a')    = sv_interp a >>= \b ->
                            sv_interp a' >>= \b' ->
                            return $ CTApp b b'


sv_interp (CTLam x a)     = incvar x >>= \n ->
                            extvenv x n >>= \rho ->
                            inEnv rho (sv_interp a) >>= \b ->
                            let x' = markvar x n
                            in
                              return $ CTLam x' b

{-
sv_interp (CTFixApp a as t) = sv_interp a >>= \b ->
                                
                              (
                                foldr
                                (\a' -> \m ->

                                  sv_interp a' >>= \b' ->
                                  m >>= \bs' ->
                                  return (b':bs')

                                )
                                  (return []) as

                              ) >>= \bs ->
                                  
                              return $ CTFixApp b bs t

-}

sv_interp (CTBind a a')   = sv_interp a >>= \ b ->
                            sv_interp a' >>= \b' ->
                            return $ CTBind b b'


sv_interp (CTNullBind a a') = sv_interp a >>= \b ->
                              sv_interp a' >>= \b' ->
                              return $  CTNullBind b b'


sv_interp (CTReturn a)    = sv_interp a >>= \b ->
                            return $ CTReturn b
                                      

sv_interp (CTPut x a)     = sv_interp a >>= \b ->
                            return $ CTPut x b


{-
sv_interp (CTLoop a t)      = sv_interp a >>= \b ->
                            return (CTLoop b t)

sv_interp (CTLoopApp a as t) = sv_interp a >>= \b ->
                               (foldr
                                 (\a' -> \m ->
                                   sv_interp a' >>= \b' ->
                                   m >>= \bs' ->
                                   return (b':bs')
                                 ) (return []) as
                               ) >>= \bs ->
                               return (CTLoopApp b bs t)
-}

sv_interp (CTFix (CTLam k t)) = incvar k >>= \n ->
                                markrec k n >>= \rho -> 
                                inEnv rho (sv_interp t) >>= \t' ->
                                let k' = markvar k n
                                in
                                  return (CTFix (CTLam k' t'))


sv_interp RdEnv             = return RdEnv

sv_interp (InEnv r t)       = sv_interp r >>= \r' ->
                              sv_interp t >>= \t' ->
                              return (InEnv r' t')

sv_interp (Resume r v)      = sv_interp r >>= \r' ->
                              sv_interp v >>= \v' ->
                              return (Resume r' v')

sv_interp (XEnv h x v)    = sv_interp h >>= \h' ->
                            sv_interp v >>= \v' ->
                            return (XEnv h' x v')

sv_interp (Lkp x)         = return (Lkp x)

sv_interp (CTSignal a)    = sv_interp a >>= \b ->
                            return $ CTSignal b

sv_interp (CTGetReq a)    = sv_interp a >>= \b ->
                            return $ CTGetReq b

sv_interp (CTPrim1ary op a) = sv_interp a >>= \b ->
                              return $ CTPrim1ary op b


sv_interp (CTPrim2ary op a a') = sv_interp a >>= \b ->
                                 sv_interp a' >>= \b' -> 
                                 return $ CTPrim2ary op b b'
                                         

sv_interp (CTPrim3ary op a a' a'') = sv_interp a >>= \b ->
                                     sv_interp a' >>= \b' -> 
                                     sv_interp a'' >>= \b'' -> 
                                     return $ CTPrim3ary op b b' b''


sv_interp (CTBranch a a' a'') = sv_interp a >>= \b ->
                                sv_interp a' >>= \b' -> 
                                sv_interp a'' >>= \b'' -> 
                                return $ CTBranch b b' b''

--
-- variables in patterns need to be scoped also
--
-- 2010.05.14 Schulz
--
sv_interp (CTCase o as) = sv_interp o >>= \o' -> 

                          (
                            foldr
                            (\(p, a) -> \m ->

                              sv_patinterp p >>= \(vs, p') ->

                              (
                                foldr
                                (\(v, n) -> \m ->

                                  extvenv v n >>= \rho ->
                                  inEnv rho m

                                )  (rdEnv) vs

                              ) >>= \rho ->

                              inEnv rho (sv_interp a) >>= \a' ->
                              m >>= \as' ->
                              return ((p', a'):as')
                            )
                              (return []) as

                          ) >>= \as' -> 

                          return $ CTCase o' as'

sv_interp (CaseStar o as) = sv_interp o >>= \o' -> 

                          (
                            foldr
                            (\(p, a) -> \m ->

                              sv_patinterp p >>= \(vs, p') ->

                              (
                                foldr
                                (\(v, n) -> \m ->

                                  extvenv v n >>= \rho ->
                                  inEnv rho m

                                )  (rdEnv) vs

                              ) >>= \rho ->

                              inEnv rho (sv_interp a) >>= \a' ->
                              m >>= \as' ->
                              return ((p', a'):as')
                            )
                              (return []) as

                          ) >>= \as' -> 

                          return $ CaseStar o' as'


sv_interp (CTCon c as)  = (

                            foldr
                            (\a -> \m ->
                              sv_interp a >>= \a' ->
                              m >>= \as' ->
                              return (a':as')
                            )
                              (return []) as

                          ) >>= \as' -> 

                          return $ CTCon c as'

sv_interp (CTPair a a') = sv_interp a >>= \b ->
                          sv_interp a' >>= \b' -> 
                          return $ CTPair b b'

sv_interp (CTVar v)     = rdEnv >>= \rho ->
                          let v' = markvar v ((fst . rho) v)
                          in
                            return $ CTVar v'

sv_interp x = return x


--
-- interpret a pattern; return a list of newly
-- bound identifiers, and the alpha-converted pattern
--
sv_patinterp :: CTPat -> SV ([(CTIdent, Int)], CTPat)

sv_patinterp (PNest p t)     = sv_patinterp p >>= \(vs, p') ->
                               return (vs, PNest p' t)

sv_patinterp (PTuple p q t) = sv_patinterp p >>= \(vs, p') ->
                              sv_patinterp q >>= \(vs', q') ->
                              return ((vs ++ vs'), PTuple p' q' t)

sv_patinterp (PList ps t)    = (
                                 foldr
                                 (\p -> \m ->

                                   sv_patinterp p >>= \(vs, p') ->
                                   m >>= \(vs', ps') ->
                                   return ((vs ++ vs') , p':ps')

                                 ) (return ([], [])) ps

                               ) >>= \(vs, ps') ->

                               return (vs, PList ps' t)

sv_patinterp (PCons p q t)  = sv_patinterp p >>= \(vs, p') ->
                              sv_patinterp q >>= \(vs', q') -> 
                              return (vs ++ vs', PCons p' q' t)


sv_patinterp (PCon x ps t)   = (
                                 foldr
                                 (\p -> \m ->

                                   sv_patinterp p >>= \(vs, p') ->
                                   m >>= \(vs', ps') ->
                                   return ((vs ++ vs') , p':ps')

                                 ) (return ([], [])) ps

                               ) >>= \(vs, ps') ->

                               return (vs, PCon x ps' t)

sv_patinterp (PPause p t)    = sv_patinterp p >>= \(vs, p') ->
                               return (vs, PPause p' t)

sv_patinterp (PDone p t)     = sv_patinterp p >>= \(vs, p') ->
                               return (vs, PDone p' t)

sv_patinterp (PPauseRe p t)  = sv_patinterp p >>= \(vs, p') ->
                               return (vs, PPauseRe p' t)

sv_patinterp (PDoneRe p t)   = sv_patinterp p >>= \(vs, p') ->
                               return (vs, PDoneRe p' t)

sv_patinterp (PVar v t)      = incvar v >>= \n ->
                               let v' = markvar v n
                                   p' = PVar v' t
                               in
                                 return ([(v, n)], p')

sv_patinterp x               = return ([], x)



-- THIS IS THE END OF THE FILE --
