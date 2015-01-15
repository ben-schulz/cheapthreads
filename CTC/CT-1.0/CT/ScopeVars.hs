--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/ScopeVars.h
--
-- a simple alpha-conversion on the AST that makes scope-behavior
-- explicit by ensuring that all variables have unique identifiers
--
-- put here 2010.03.27
--
-- Schulz
--

module CT.ScopeVars where

import CT.Syntax
import CT.INAST

import CT.MonadicConstructions


--
-- top-level call:
--

scopevars :: INProg -> INProg
scopevars p@(INProg ((mn, fs), (dats, mons))) =

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
    (\(INFunDec ((f, t), (xs, e))) -> \m ->

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

      let d' = (INFunDec ((f', t), (xs', e')))
      in
        return (d':fs')

    )
      (return []) (mn:fs)

  ) >>= \(mn':fs') ->

  return $ INProg ((mn', fs'), (dats, mons))
  )


--
-- each identifier is mapped to a counter in some environment;
-- the counter is incremented each time a new scope
-- involving that variable is encountered
--
-- the counter is used to tag repeated variables in different
-- scopes with unique integer suffixes
--
--
type VEnv = CTIdent -> Int

type SV a = EnvT VEnv (StateT [(CTIdent, Int)] Id) a

initvenv :: VEnv
initvenv = \_ -> 0

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
markvar x n = x ++ (show n)


--
-- extend the environment:
--
extvenv :: CTIdent -> Int -> SV VEnv
extvenv x v = rdEnv >>= \rho ->
              return $ tweek rho x v

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

sv_interp :: INAST -> SV INAST


sv_interp (CTAppIN a a' t)    = sv_interp a >>= \b ->
                                sv_interp a' >>= \b' ->
                                return $ CTAppIN b b' t

  
sv_interp (CTRecAppIN a a' t) = sv_interp a >>= \b ->
                                sv_interp a' >>= \b' ->
                                return $ CTRecAppIN b b' t


sv_interp (CTLamIN x a t)     = incvar x >>= \n ->
                                extvenv x n >>= \rho ->
                                inEnv rho (sv_interp a) >>= \b ->
                                let x' = markvar x n
                                in
                                  return $ CTLamIN x' b t

sv_interp (CTFixAppIN a as t) = sv_interp a >>= \b ->
                                
                                (
                                  foldr
                                  (\a' -> \m ->

                                    sv_interp a' >>= \b' ->
                                    m >>= \bs' ->
                                    return (b':bs')

                                  )
                                    (return []) as

                                ) >>= \bs ->
                                  
                                return $ CTFixAppIN b bs t


sv_interp (CTBindIN a a' t)   = sv_interp a >>= \ b ->
                                sv_interp a' >>= \b' ->
                                return $ CTBindIN b b' t


sv_interp (CTNullBindIN a a' t) = sv_interp a >>= \b ->
                                  sv_interp a' >>= \b' ->
                                  return $  CTNullBindIN b b' t


sv_interp (CTReturnIN a t)    = sv_interp a >>= \b ->
                                return $ CTReturnIN b t
                                      

sv_interp (CTPutIN x a t)     = sv_interp a >>= \b ->
                                return $ CTPutIN x b t

sv_interp (CTPushIN x a t)    = sv_interp a >>= \b ->
                                return $ CTPushIN x b t


sv_interp (CTReadIN x a t)    = sv_interp a >>= \b ->
                                return $ CTReadIN x b t

sv_interp (CTWriteIN x a a' t) = sv_interp a >>= \b ->
                                 sv_interp a' >>= \b' -> 
                                 return $ CTWriteIN x b b' t

sv_interp (CTStepIN a t)      = sv_interp a >>= \b ->
                                return $ CTStepIN b t


sv_interp (CTResumeIN a t)    = sv_interp a >>= \b ->
                                return $ CTResumeIN b t

sv_interp (CTResumeReIN a a' t)    = sv_interp a >>= \b ->
                                     sv_interp a' >>= \b' ->
                                     return $ CTResumeReIN b b' t

sv_interp (CTLoopIN a t)      = sv_interp a >>= \b ->
                                return (CTLoopIN b t)

sv_interp (CTLoopAppIN a as t) = sv_interp a >>= \b ->
                                 (foldr
                                   (\a' -> \m ->
                                     sv_interp a' >>= \b' ->
                                     m >>= \bs' ->
                                     return (b':bs')
                                   ) (return []) as
                                 ) >>= \bs ->
                                 return (CTLoopAppIN b bs t)

sv_interp (CTFixIN a t)       = sv_interp a >>= \b ->
                               return $ CTFixIN b t


sv_interp (CTSignalIN a t)    = sv_interp a >>= \b ->
                                return $ CTSignalIN b t

sv_interp (CTGetReqIN a t)    = sv_interp a >>= \b ->
                                return $ CTGetReqIN b t

sv_interp (CTPrim1aryIN op a t) = sv_interp a >>= \b ->
                                  return $ CTPrim1aryIN op b t


sv_interp (CTPrim2aryIN op a a' t) = sv_interp a >>= \b ->
                                     sv_interp a' >>= \b' -> 
                                     return $ CTPrim2aryIN op b b' t
                                         

sv_interp (CTPrim3aryIN op a a' a'' t) = sv_interp a >>= \b ->
                                         sv_interp a' >>= \b' -> 
                                         sv_interp a'' >>= \b'' -> 
                                         return $ CTPrim3aryIN op b b' b'' t


sv_interp (CTBranchIN a a' a''  t) = sv_interp a >>= \b ->
                                     sv_interp a' >>= \b' -> 
                                     sv_interp a'' >>= \b'' -> 
                                     return $ CTBranchIN b b' b'' t

--
-- VARIABLES IN PATTERNS NEED TO BE SCOPED ALSO
--
-- 2010.05.14 Schulz
--
sv_interp (CTCaseIN o as t) = sv_interp o >>= \o' -> 

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

                              return $ CTCaseIN o' as' t


sv_interp (CTConIN c as t)  = (

                                foldr
                                (\a -> \m ->
                                  sv_interp a >>= \a' ->
                                  m >>= \as' ->
                                  return (a':as')
                                )
                                  (return []) as

                              ) >>= \as' -> 

                              return $ CTConIN c as' t

sv_interp (CTPairIN a a' t) = sv_interp a >>= \b ->
                              sv_interp a' >>= \b' -> 
                              return $ CTPairIN b b' t

sv_interp (CTVarIN v t)     = rdEnv >>= \rho ->
                              let v' = markvar v (rho v)
                              in
                                return $ CTVarIN v' t

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
