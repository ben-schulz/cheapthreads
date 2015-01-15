--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Uncase
--
-- a simple syntactic transformation on INAST that transforms
-- case statements with nested patterns into nested case statements
-- with simple patterns;
--
-- put here 2010.03.16
--

module CT.Uncase where

import CT.Syntax
import CT.INAST
import CT.MonadicConstructions
import Control.Monad
import Data.Maybe




--
-- the top-level: unnest the patterns in a case expression:
--

uncase :: INProg -> INProg
uncase (INProg ((mn, fs), (ds, ms))) =

  prj_unc $   -- do everything in the monad, then project out:

  (
    foldr
    (\(INFunDec ((f, t), (xs, a))) -> \m ->

      uncase_interp a >>= \(_, a') ->
      m >>= \ds ->
      return (ds ++ [INFunDec ((f, t), (xs, a'))])

    ) (return []) (mn:fs)

  ) >>= \fs'' -> 

  let mn' = last fs''
      fs' = init fs''
  in
    return $ INProg ((mn', fs'), (ds, ms))

--
-- we maintain a counter for generating new variables:
--
type UNC a = StateT Int Id a

newcasevar :: UNC String
newcasevar =
  get >>= \i ->
  upd (\_ -> i + 1) >>
  return (casevar ++ (show i))


prj_unc :: UNC a -> a
prj_unc s = fst $ deId $ (deST s) init_unc

init_unc :: Int
init_unc = 0



--
-- the transformation:
--
-- the transformation works by "pushing out" all nested patterns
-- in each alternative of a 'case' expression, replacing them
-- with an equivalent sequence of nested case statements; this procedure
-- is then repeated on the generated expressions until no more nested
-- paterns remain
--
-- call structure looks like:
--
--  uncase_interp -> alttocase -> uncase_interp
--
-- first return is the match-expression currently in scope;
-- second return is the transformed expression
--

uncase_interp :: INAST -> UNC (INAST, INAST)
uncase_interp (CTCaseIN x alts t) = let alts'' = tails alts
                                    in

                                      (
                                        foldr
                                        (\(a, as) -> \m ->

                                          let cse = CTCaseIN x as t
                                          in
                                            uncase_interp cse >>= \(_, e') ->

                                            alttocase e' as a >>= \(p',a') ->
                                            uncase_interp a' >>= \(_, a'') ->
                                            m >>= \alts' ->


                                            return ((p', a''):alts')
                                        )
                                          (return []) alts''

                                      ) >>= \alts' ->

                                      case alts' of
                                        (a:as) -> return
                                                    (x,
                                                      CTCaseIN x (as ++ [a]) t)

                                        _      -> return
                                                    (x,
                                                      CTCaseIN x alts' t)


--
-- the remaining cases simply crawl the expression tree,
-- looking for 'case':
--
uncase_interp (CTAppIN a a' t)    = uncase_interp a >>= \(_, b) ->
                                    uncase_interp a' >>= \(_, b') ->
                                    let x = CTAppIN b b' t
                                    in
                                      return (x, x)

uncase_interp (CTRecAppIN a a' t) = uncase_interp a >>= \(_, b) ->
                                    uncase_interp a' >>= \(_, b') ->
                                    let x = CTRecAppIN b b' t
                                    in
                                      return (x, x)

uncase_interp (CTLamIN x a t)     = uncase_interp a >>= \(_, b) ->
                                    let y = CTLamIN x b t
                                    in
                                      return (y, y)
                                      

uncase_interp (CTBindIN a a' t)   = uncase_interp a >>= \(_, b) ->
                                    uncase_interp a' >>= \(_, b') ->
                                    let x = CTBindIN b b' t
                                    in
                                      return (x, x)
                                      

uncase_interp (CTNullBindIN a a' t) = uncase_interp a >>= \(_, b) ->
                                      uncase_interp a' >>= \(_, b') ->
                                      let x = CTNullBindIN b b' t
                                      in
                                        return (x, x)
                                        

uncase_interp (CTReturnIN a t)    = uncase_interp a >>= \(_, b) ->
                                    let x = CTReturnIN b t
                                    in
                                      return (x, x)
                                      

uncase_interp (CTPutIN x a t)     = uncase_interp a >>= \(_, b) ->
                                    let y = CTPutIN x b t
                                    in
                                      return (y, y)
                                      

uncase_interp (CTReadIN x a t)    = uncase_interp a >>= \(_, b) ->
                                    let y = CTReadIN x b t
                                    in
                                      return (y, y)

uncase_interp (CTWriteIN x a a' t) = uncase_interp a >>= \(_, b) ->
                                     uncase_interp a' >>= \(_, b') -> 
                                     let y = CTWriteIN x b b' t
                                     in
                                       return (y, y)

uncase_interp (CTStepIN a t)      = uncase_interp a >>= \(_, b) ->
                                    let x = CTStepIN b t
                                    in
                                      return (x, x)

{-
-- CHANGE THIS:
-- later, as in, when we get rid of the list argument:
-- (2010.03.25) Schulz
--
uncase_interp (CTFixIN a as t)    = uncase_interp a >>= \(_, b) ->
                                    let x = CTFixIN b as t -- whatever
                                    in
                                      return (x, x)
-}

uncase_interp (CTFixIN a t)       = uncase_interp a >>= \(_, b) ->
                                    let x = CTFixIN b t
                                    in
                                      return (x, x)

uncase_interp (CTFixAppIN a as t) = uncase_interp a >>= \(_, b) ->

                                    (
                                      foldr
                                      (\a' -> \m ->

                                        uncase_interp a' >>= \(_, b') ->
                                        m >>= \bs' ->
                                        return (b':bs')

                                      )
                                        (return []) as

                                    ) >>= \bs ->

                                    let x = CTFixAppIN b bs t
                                    in
                                      return (x, x)

uncase_interp (CTSignalIN a t)    = uncase_interp a >>= \(_, b) ->
                                    let x = CTSignalIN b t
                                    in
                                      return (x, x)


uncase_interp (CTPrim1aryIN op a t) = uncase_interp a >>= \(_, b) ->
                                      let x = CTPrim1aryIN op b t
                                      in
                                        return (x, x)

uncase_interp (CTPrim2aryIN op a a' t) = uncase_interp a >>= \(_, b) ->
                                         uncase_interp a' >>= \(_, b') -> 
                                         let x = CTPrim2aryIN op b b' t
                                         in
                                           return (x, x)
                                         

uncase_interp (CTPrim3aryIN op a a' a'' t) = uncase_interp a >>= \(_, b) ->
                                             uncase_interp a' >>= \(_, b') -> 
                                             uncase_interp a'' >>= \(_, b'') -> 
                                             let x = CTPrim3aryIN op b b' b'' t
                                             in
                                               return (x, x)
                                              

uncase_interp (CTBranchIN a a' a''  t) = uncase_interp a >>= \(_, b) ->
                                         uncase_interp a' >>= \(_, b') -> 
                                         uncase_interp a'' >>= \(_, b'') -> 
                                         let x = CTBranchIN b b' b'' t
                                         in
                                           return (x, x)
                                           

uncase_interp (CTPairIN a a' t) = uncase_interp a >>= \(_, b) ->
                                  uncase_interp a' >>= \(_, b') -> 
                                  let x = CTPairIN b b' t
                                  in
                                    return (x, x)
                                  

uncase_interp x = return (x, x)


--
-- unpack a nested pattern into an equivalent series of
-- nested case statements
--

alttocase :: INAST -> [(CTPat, INAST)] -> (CTPat, INAST) -> UNC (CTPat, INAST)

                 -- if no nesting in the pattern, nothing to do:
alttocase x alts (p, a) | (unnested p) =

                          return (p, a)

                        -- otherwise, generate the corresponding nested cases:
                        | otherwise  =

                          -- push the nested patterns out of the current pat:
                          pushpats p >>= \(p', ps') ->
 
                          -- form the new case statements:
--                          let a' = altprop x alts $ stretchcase a ps'
                          let a' = stretchcase x a ps'
                          in

                            -- and then continue the process 
                            -- at the next level of nesting:
                            uncase_interp a' >>= \(x', a'') -> 
                            alttocase x' alts (p', a'')


--
-- make a succession of new case statements corresponding
-- to the list of given pattern-ident pairs:
--
-- first argument is the 'default' case that each
-- alternative should fall through to;
--
-- second argument is the list of identifier-pattern
-- pairs corresponding to patterns that are being unnested
--
{-
mkcases :: INAST -> [(CTIdent, CTPat)] -> INAST
mkcases dlt (a:as) =

  let v  = CTVarIN (fst a) dumbt
      a' = CTCaseIN v [(snd a, dlt)]
  in

    foldl
    (\(CTCaseIN v' as' t) -> \x ->


    )
      a' as
-}
  

--
-- push nested patterns out and replace them with
-- fresh variables;
--
-- in codomain, first component is argument with nested pats removed;
-- second is a keylist of the patterns replaced and the variables
-- to which they are bound;
--
-- note that we only push out compound patterns; simple ones
-- (i.e. literals, variables, and wildcards) all stay put
--
pushpats :: CTPat -> UNC (CTPat, [(CTIdent, CTPat)])

pushpats (PNest p _) = pushpats p  -- 'PNest' is actually just a wrapper

pushpats (PCon d ps t) = -- For each compound subpattern, generate a fresh variable
                         -- and replace the subpattern with a "PVar" on that variable.
                         -- Return the new pattern resulting from this substitution,
                         -- and a list generated pattern variables paired with the
                         -- patterns they replaced.
                         mapM (\p -> if simplepat p
                                       then return (p,Nothing)
                                       else newcasevar >>= \ v -> return (PVar v (typeofpat p),Just v)) ps
                           >>= \ subpatsandnewvars ->
                         let
                             subpats  = map fst subpatsandnewvars
                             newpvars = catMaybes $ map (\(p, mV) -> case mV of
                                                                        (Just v) -> Just (v,p)
                                                                        Nothing  -> Nothing) subpatsandnewvars
                             newpat   = PCon d subpats t
                         in
                           return
                             (newpat, newpvars)

--
-- all of the following are really just explicit
-- versions of the above, without the fold:
--

pushpats (PTuple p p' t) = if (simplepat p)
                           then
                             if (simplepat p')
                             then
                               return
                                 -- both patterns simple:
                                 (PTuple p p' t, [])

                             else
                               newcasevar >>= \v' ->
                               return
                                 -- only first pattern simple:
                                 (PTuple p (PVar v' (typeofpat p')) t,
                                   [(v', p')])
                                 

                           else
                             newcasevar >>= \v ->
                             if (simplepat p')
                             then
                               return

                                 -- only second pattern simple:
                                 (PTuple (PVar v (typeofpat p)) p' t, [(v, p)])
                                 

                             else
                               newcasevar >>= \v' ->
                               return

                                 -- both patterns compound
                                 (PTuple
                                   (PVar v (typeofpat p))
                                     (PVar v' (typeofpat p')) t,
                                       [(v, p), (v', p')])


pushpats (PList ps t)   = (
                           foldr
                           (\p -> \m ->

                              -- make fresh variable for each compound pattern:
                              if (simplepat p)
                              then
                                m
                              else
                                newcasevar >>= \v ->
                                m >>= \vs ->
                                return (vs ++ [(v, p)])
                           ) (return []) ps

                         ) >>= \vs ->
  
                         let newpvars = map (\(v, p) -> PVar v (typeofpat p)) vs
                             newpat   = PList newpvars t
                         in
                           return
                             (newpat, vs)


pushpats (PCons p p' t) = if (simplepat p)
                          then
                             newcasevar >>= \v ->
                             if (simplepat p')
                             then
                               newcasevar >>= \v' ->
                               return
                                 (PCons
                                   (PVar v (typeofpat p))
                                     (PVar v' (typeofpat p')) t,
                                       [(v, p), (v', p')])
                             else
                               return
                                 (PCons (PVar v (typeofpat p)) p' t,
                                   [(v, p)])
                           else
                             if (simplepat p')
                             then
                               newcasevar >>= \v' ->
                               return
                                 (PCons p (PVar v' (typeofpat p')) t,
                                   [(v', p')])
                             else
                               return
                                 (PCons p p' t, [])
  


pushpats (PPause p t) = if (simplepat p)
                        then 
                          newcasevar >>= \v ->
                          return (PPause (PVar v (typeofpat p)) t, [(v, p)])
                        else
                          return (PPause p t, [])

pushpats (PDone p t)  = if (simplepat p)
                        then 
                          newcasevar >>= \v ->
                          return (PDone (PVar v (typeofpat p)) t, [(v, p)])
                        else
                          return (PDone p t, [])

--
-- identical to the two cases preceding:
--
pushpats (PPauseRe p t) = if (simplepat p)
                          then 
                            newcasevar >>= \v ->
                            return (PPauseRe (PVar v (typeofpat p)) t, [(v, p)])
                          else
                            return (PPauseRe p t, [])

pushpats (PDoneRe p t)  = if (simplepat p)
                          then 
                            newcasevar >>= \v ->
                            return (PDoneRe (PVar v (typeofpat p)) t, [(v, p)])
                          else
                            return (PDoneRe p t, [])


-- default case: anything else admits no nesting,
-- so nothing to push:
pushpats x = return (x, [])



--
-- take a list of variable-pattern pairs and stretch
-- it out into a sequence of 'case' statements:
--
stretchcase :: INAST -> INAST -> [(CTIdent, CTPat)] -> INAST
stretchcase dlt e ps =

  let alt = (Wildcard dumbt, dlt)
  in

    if (emptycase dlt)
    then
      foldr
--        (\(v, p) -> \m -> CTCaseIN (CTVarIN v dumbt) [(p, m)] dumbt)
        (\(v, p) -> \m ->
          CTCaseIN (CTVarIN v (typeofpat p)) [(p, m)] (typeofinast m))
            e ps
    else
      foldr
--        (\(v, p) -> \m -> CTCaseIN (CTVarIN v dumbt) [(p, m), alt] dumbt)
        (\(v, p) -> \m ->
          CTCaseIN (CTVarIN v (typeofpat p)) [(p, m), alt] (typeofinast m))
            e ps


emptycase :: INAST -> Bool
emptycase (CTCaseIN _ [] _) = True
emptycase _                 = False


--
-- propagate a sequence of fall-through alternatives
-- through a sequence of nested case statements:
--
{-
altprop :: INAST -> [(CTPat, INAST)] -> INAST -> INAST
altprop x alts (CTCaseIN x' alts' t) =

  let alts''  = foldr (\(p, a) -> \m -> (p, (altprop x alts a)):m) [] alts'
      cse     = CTCaseIN x alts'' dumbt
      pat'    = (Wildcard, cse)
  in
    CTCaseIN x' (alts ++ [pat']) t


altprop _ _ e = e
-}
    


--
-- predicate for classifying patterns as simple,
-- i.e. as involving no possibility of nesting:
--
simplepat :: CTPat -> Bool
simplepat (PLit _ _)      = True
simplepat (PVar _ _)      = True
simplepat (PNest p _)     = simplepat p
simplepat (Wildcard _)    = True
simplepat _               = False

--
-- identify a pattern as simplified:
--
unnested :: CTPat -> Bool
unnested (PCon _ ps _)   = all simplepat ps
unnested (PTuple p p' _) = (simplepat p) && (simplepat p')
unnested (PList ps _)    = all simplepat ps
unnested (PCons p p' _)  = (simplepat p) && (simplepat p')
unnested (PPause p _)    = simplepat p
unnested (PDone p _)     = simplepat p
unnested (PPauseRe p _)  = simplepat p
unnested (PDoneRe p _)   = simplepat p
unnested x               = simplepat x


--
-- a simple trick for threading the alternatives
-- through as an argument:
--
tails :: [a] -> [(a, [a])]
tails (x:xs) = (x, xs):(tails xs)
tails []     = []


--
-- our default tag for the compiler-generated variables:
--
casevar :: String
casevar = "__casevar__"

--
-- a dummy type variable we use
-- for generated expressions, since
-- propagating the types would be too cumbersome
--
dumbt :: CTTy
dumbt = CTTyVar "__casety__"


-- THIS IS THE END OF THE FILE --
