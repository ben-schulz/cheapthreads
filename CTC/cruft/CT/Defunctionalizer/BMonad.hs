--
-- this is b.hs
--
-- formulation of the Conditional-Value monad
--
-- put here 14.07.09 Schulz
--

module CT.Defunctionalizer.BMonad where

--
-- a class of conditions that can evaluate
-- into boolean values
--
class Condition a where
  evalCond :: a -> Bool
  negateCond   :: a -> a
  conjunctCond :: a -> a -> a
  disjunctCond :: a -> a -> a

--
-- the Conditional Value Monad:
--

data (Condition c) => B c a = V a | C c (B c a) (B c a)

instance (Condition c) => Monad (B c) where
  return = V
  (V x) >>= f = f x
  (C p b1 b2) >>= f = let b1' = b1 >>= f
                          b2' = b2 >>= f
                      in
                        subsume (C p b1' b2')

--
-- we need an 'Eq' instance to use the defunctionalizer:
--

instance (Condition c, Eq c, Eq a) => Eq (B c a) where
  (V x) == (V y)                = x == y
  (C p b1 b2) == (C p' b1' b2') = (p == p') && (b1 == b1') && (b2 == b2')
  _ == _ = False

--
-- subsume means:
--
-- apply the condition occuring at the top
-- downward through the subterms, e.g.,
--
-- turn this:
--
-- (*) if p1 then e1
--     else
--       if p2 then e2
--       else
--         e3
--
-- into this:
--
-- if p1 then e1
-- else
--   if (not p1) && p2 then e2
--   else
--     e3
--
-- note that the control flow realized by the sub-expression
-- beginning at the second 'if' is now equivalent to that in (*),
-- i.e. evaluating the subexpression gives the value e2 exactly
-- when evaluating (*) gives the value e2
-- 
--

subsume :: (Condition c) => B c a -> B c a
subsume (C p b1 b2) = C p (refine p b1) (refine (negateCond p) b2)
subsume (V x)       = (V x)

--
-- refine means:
--
-- narrow the condition so that its value becomes contingent
-- on that of another condition, i.e.
--
-- turn this:
--
--   if p then e1 else e2
--
-- into this:
--
--   if (p && p') then e1 else e2
--

refine :: (Condition c) => c -> B c a -> B c a
refine p (C p' b1 b2) = C (conjunctCond p p') b1 b2
refine _ (V x)        = (V x)


-- note that we could define 'refine' so that:
--
--   refine p (V x) = C p (V x) y
--
-- with 'y' equal to anything.  This would vary
-- the behavior of 'B' somewhat, since it would essentially
-- add a 'wildcard' case as a final 'else' corresponding
-- to something not at all contingent on 'p'.
--
-- Potentially, could be expressed as some sort of 'nil'
-- value, though its real meaning in such a situation would
-- seem to consist of some undefined behavior in the case
-- that p is false.
--
-- To put it another way, this would be like an 'if'
-- with no 'else'.



--
-- project out of the monad:
--
-- This simply runs the control flow specified in the term,
-- according to how the conditions evaluate
--
runB :: (Condition c) => B c a -> a
runB (V x)       = x
runB (C p b1 b2) = if (evalCond p) then (runB b1) else (runB b2)

--
-- separate the branches of a B-term into a list of terms of the form:
--
--   C c (V x) (V y)
--
-- This is used by the defunctionalizer to obtain the conditional
-- values, on the assumption that the term has been properly subsumed
-- in binding (see definitions of '>>=' and 'subsume' above)
--
severB :: (Condition c) => B c a -> [Either (c, a) a]
severB (C c (V x) (V y)) = [Left (c, x), Left (negateCond c, y)]
severB (C c (V x) b') = (Left (c, x)):(severB b')
severB (C c b (V y)) = (Left (negateCond c, y)):(severB b)
severB (C c b1 b2) = (severB b1) ++ (severB b2)
severB (V x) = [Right x]

{---------------------------------------------------------------------

Without building the abstract term, the above monad would be
effectively equivalent to this:

data B a = V a | C Bool (B a) (B a)

instance Monad B where
  return            = V
  (V x) >>= f       = f x
  (C p b1 b2) >>= f = if p then (b1 >>= f) else (b2 >>= f)

with no non-proper morphisms
---------------------------------------------------------------------}
