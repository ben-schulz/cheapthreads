--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/InterpRe.hs
--
-- a monadic-style interpreter for PCF;
--
-- iteration three: factoring of the resumptive interpreter into source
-- term and handler;
--
-- put here (2010.12.06)
--
-- Schulz
--

module Interpreters.InterpRe where

import Prelude 

import PCF.Syntax
import MonadicConstructions

--
-- values in the factored reactive interpreter;
--
-- note that pure functions have been replaced by closures,
-- reflecting the removal of the environment monad;
--
data V_Re = Wrong 
          | Num Int
          | Bol Bool
          | Cl Name Env (Re V_Re)
          | RecCl Name Env (Re V_Re)


instance Show V_Re where
    show Wrong         = "Wrong"
    show (Num i)       = show i
    show (Bol b)       = show b
    show (Cl _ _ _)    = "<closure>"
    show (RecCl _ _ _) = "<recclosure>"

type Env = [(Name, V_Re)]

data Req = Cont
         | MkCl Name (Re V_Re)
         | MkRecCl Name (Re V_Re)
         | Ap V_Re V_Re
         | AppEnv Name


data Rsp = Ack
         | Val V_Re

type R a = ResT Id a

type Re a = ReactT Req Rsp Id a


sched :: (Re V_Re -> R (Re V_Re)) -> Re V_Re -> R V_Re
sched f (D v) = Done v
sched f phi   = f phi >>= \phi' -> sched f phi'


exec :: Env -> Re V_Re -> R V_Re
exec rho t = sched (hand rho) t


hand :: Env -> Re V_Re -> R (Re V_Re)
hand rho (P (Cont, r))                 = step_R (r Ack)
hand rho (P (MkCl x phi, r))           = step_R (r (Val (Cl x rho phi)))

hand rho (P (MkRecCl x phi, r))        = exec
                                           (xEnv rho x
                                             (RecCl x rho phi)) phi >>= \v -> 
                                         step_R (r (Val v))

hand rho (P (Ap (Cl x rho' phi) v, r)) = exec (xEnv rho' x v) phi >>= \v' ->
                                         step_R (r (Val v'))

hand rho (P (Ap _ v, r))               = step_R (r (Val Wrong))

hand rho (P (AppEnv x, r)) = case (lkp x rho) of

                             -- recursive call:
                             (RecCl x rho' phi) -> let rho'' = xEnv rho' x
                                                               (RecCl x rho phi)
                                                   in
                                                     exec rho'' phi >>= \v ->
                                                     step_R (r (Val v))

                             -- any other value:
                             v                  -> step_R (r (Val v))


--
-- whereas the control primitives 
--

hand rho (D v)                         = return (D v)


--
-- the interpreter:
--

initenv = []

interp_re :: Term -> V_Re
interp_re t = (deId . run_R) (exec initenv (interp t))

interp :: Term -> Re V_Re
interp (Lam x t)  = mkfun x (interp t)

interp (App t t') = interp t' >>= \a ->
                    interp t >>= \f ->
                    apply f a

interp (Inc t)    = interp t >>= \v ->
                    case v of
                      (Num n) -> return (Num (n + 1))
                      _       -> return Wrong


interp (Dec t)    = interp t >>= \v -> 
                    case v of
                      (Num n) -> return (Num (n - 1))
                      _       -> return Wrong

interp (ZTest t)  = interp t >>= \v ->
                    case v of
                      (Num 0) -> return (Bol True)
                      (Num _) -> return (Bol False)
                      _       -> return Wrong

interp (EF t t' t'') = interp t >>= \b ->
                       case b of
                         (Bol False) -> interp t''
                         (Bol True)  -> interp t'
                         _           -> return Wrong

interp (Mu x t)   = mkrecfun x (interp t)

interp (Var x)    = signalV (AppEnv x)

interp (Con n)    = return (Num n)

interp (Bit b)    = return (Bol b)


--                                       --
-- Characteristic Interpreter Morphisms: --
--                                       --

signalV :: Req -> Re V_Re
signalV q = P (q, \(Val v) -> return (return v))


xEnv :: Env -> Name -> V_Re -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
lkp :: Name -> Env -> V_Re
lkp x ((y,b):bs) = if x == y then b else lkp x bs
lkp x [] = Wrong


--
-- form an application:
--
apply :: V_Re -> V_Re -> Re V_Re
apply f v = signalV (Ap f v)


--
-- create a function from an abstraction:
--
mkfun :: Name -> Re V_Re -> Re V_Re
mkfun x f = signalV (MkCl x f)

--
-- create a recursive closure:
--
mkrecfun :: Name -> Re V_Re -> Re V_Re
mkrecfun x f = signalV (MkRecCl x f)



-- THIS IS THE END OF THE FILE --
