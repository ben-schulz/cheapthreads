--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/InterpErr.hs
--
-- a monadic-style interpreter for PCF;
--
-- a repurposing of the RPS demonstration: adding an 'Error' state
-- instead of 'Wrong', as an entry point into an exposition of XPL;
--
--
-- put here (2010.12.12)
--
-- Schulz
--

module Interpreters.InterpErr where

import Prelude 

import PCF.Syntax
import MonadicConstructions

--
-- values in the factored reactive interpreter;
--
-- note that pure functions have been replaced by closures,
-- reflecting the removal of the environment monad;
--
data V_Err = Num Int
           | Bol Bool
           | Cl Name Env (Re V_Err)
           | RecCl Name Env (Re V_Err)


instance Show V_Err where
    show (Num i)    = show i
    show (Bol b)    = show b
    show (Cl _ _ _) = "<closure>"

type Env = [(Name, V_Err)]

data Req = Cont
         | MkCl Name (Re V_Err)
         | MkRecCl Name (Re V_Err)
         | Ap V_Err V_Err
         | AppEnv Name

         -- primitives pushed up into the handler
         -- by the addition of error to the interpreter:
         | QInc V_Err
         | QDec V_Err
         | QZ V_Err
         | QB V_Err


data Rsp = Ack
         | Val V_Err

type R a = ErrT Id a

type Re a = ReactT Req Rsp Id a


sched :: (Re V_Err -> R (Re V_Err)) -> Re V_Err -> R V_Err
sched f (D v) = OK v
sched f phi   = f phi >>= \phi' -> sched f phi'


exec :: Env -> Re V_Err -> R V_Err
exec rho t = sched (hand rho) t


hand :: Env -> Re V_Err -> R (Re V_Err)
hand rho (P (Cont, r))                 = step_Err (r Ack)
hand rho (P (MkCl x phi, r))           = step_Err (r (Val (Cl x rho phi)))

hand rho (P (MkRecCl x phi, r))        = exec
                                           (xEnv rho x
                                             (RecCl x rho phi)) phi >>= \v -> 
                                         step_Err (r (Val v))

hand rho (P (Ap (Cl x rho' phi) v, r)) = exec (xEnv rho' x v) phi >>= \v' ->
                                         step_Err (r (Val v'))

hand rho (P (Ap _ _, _))               = Err

hand rho (P (AppEnv x, r)) = lkp x rho >>= \v -> 
                             case v of

                             -- recursive call:
                             (RecCl x rho' phi) -> let rho'' = xEnv rho' x
                                                               (RecCl x rho phi)
                                                   in
                                                     exec rho'' phi >>= \v ->
                                                     step_Err (r (Val v))

                             -- any other value:
                             v                  -> step_Err (r (Val v))


hand rho (P (QInc (Num n), r))         = step_Err (r (Val (Num (n + 1))))
hand rho (P (QInc _, r))               = Err

hand rho (P (QDec (Num n), r))         = step_Err (r (Val (Num (n - 1))))
hand rho (P (QDec _, r))               = Err

hand rho (P (QZ (Num 0), r))           = step_Err (r (Val (Bol True)))
hand rho (P (QZ (Num _), r))           = step_Err (r (Val (Bol False)))
hand rho (P (QZ _, r))                 = Err

hand rho (P (QB (Bol False), r))       = step_Err (r (Val (Bol False)))
hand rho (P (QB (Bol True), r))        = step_Err (r (Val (Bol True)))
hand rho (P (QB _, r))                 = Err

hand rho (D v)                         = return (D v)


--
-- the interpreter:
--

initenv = []

interp_err :: Term -> Maybe V_Err
interp_err t = (deId . prj_err) (exec initenv (interp t))

interp :: Term -> Re V_Err
interp (Lam x t)  = mkfun x (interp t)

interp (App t t') = interp t' >>= \a ->
                    interp t >>= \f ->
                    apply f a

interp (Inc t)    = interp t >>= \v ->
                    signalV (QInc v)


interp (Dec t)    = interp t >>= \v -> 
                    signalV (QDec v)

interp (ZTest t)  = interp t >>= \v ->
                    signalV (QZ v)

interp (EF t t' t'') = interp t >>= \b ->
                       signalV (QB b) >>= \v ->
                       case v of
                         (Bol False) -> interp t''
                         (Bol True)  -> interp t'

interp (Mu x t)   = mkrecfun x (interp t)

interp (Var x)    = signalV (AppEnv x)

interp (Con n)    = return (Num n)

interp (Bit b)    = return (Bol b)


--                                       --
-- Characteristic Interpreter Morphisms: --
--                                       --

signalV :: Req -> Re V_Err
signalV q = P (q, \(Val v) -> return (return v))


xEnv :: Env -> Name -> V_Err -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
lkp :: Name -> Env -> R V_Err
lkp x ((y,b):bs) = if x == y then return b else lkp x bs
lkp x [] = Err


--
-- form an application:
--
apply :: V_Err -> V_Err -> Re V_Err
apply f v = signalV (Ap f v)


--
-- create a function from an abstraction:
--
mkfun :: Name -> Re V_Err -> Re V_Err
mkfun x f = signalV (MkCl x f)

--
-- create a recursive closure:
--
mkrecfun :: Name -> Re V_Err -> Re V_Err
mkrecfun x f = signalV (MkRecCl x f)



-- THIS IS THE END OF THE FILE --
