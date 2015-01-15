--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Compiler/Interp.hs
--
-- an interpreter for ETIC
--
-- put here 2010.06.01
--
-- Schulz
--

module Deprecated.Compiler.Interp where

import CT.MonadicConstructions
import Deprecated.ETIC.Syntax

type Reg = String

--
-- thread control block maintains:
-- 
-- + signal from current thread
-- + retval of current thread
-- + remainder of thread to execute
--
{-
data TCB = TCB Value Value [Stmt] deriving Show

sigof :: TCB -> Value
sigof (TCB sig _ _) = sig

retvalof :: TCB -> Value
retvalof (TCB _ v _) = v

ttailof :: TCB -> [Stmt]
ttailof (TCB _ _ ss) = ss
-}

data Value = IntVal Int
           | BoolVal Bool
           | StringVal String
           | ArrayVal [Value]                    -- static-length array
           | Pair Value Value                    -- cartesian product
           | TCB [Stmt]                          -- thread control block
           | StructVal String [(String, Value)]  -- data structure, named fields
           | StackVal [Value]                    -- a first-class (?) stack
           | EnvVal [(String, Value)]            -- I hate this
           | EnvStackVal [[(String, Value)]]     -- I hate this
           | Void                                -- initial var contents
           deriving Show

type Param = String

data SymLkp = F ([Param], ([VarDecl], [Stmt]))   -- function dec
            | S [(String, Type)]                 -- struct dec
            | L [Stmt]                           -- jump label
            | V Value                            -- value
            | GLOBAL                             -- reference to a global var
            deriving Show


type GVarDec = VarDecl

type FunDec = ((String, [Param]), ([VarDecl], [Stmt]))

type SDec = TopDecl

--
-- environment of currently in-scope symbols,
-- including constants, declared functions,
-- declared structs, variables;
--
-- the environment is here being used as an imperative
-- state with the usual notions of scoping;
--
--
type IEnv = String -> SymLkp

--
-- globally declared variables:
--
type Globals = [(String, Value)]

--
-- a stack of environments, used by the handler:
--
type Env    = [(String, Value)]
type EStack = [Env]


--
-- the interpreter monad:
--
-- this consists of environments of locally
-- scoped variables, and persistent state holding
-- the values of all globally declared variables
--
type IE a = EnvT IEnv (StateT (Globals, EStack) Id) a


--
-- accessors for the various parts of the environment:
--
appEnvFun :: String -> IE ([Param], ([VarDecl], [Stmt]))
appEnvFun s = rdEnv >>= \rho ->
              case (rho s) of
                (F f) -> return f
                _     -> error $ "couldn't locate function declaration: " ++ s

appEnvStruct :: String -> IE [(String, Type)]
appEnvStruct s = rdEnv >>= \rho ->
              case (rho s) of
                (S t) -> return t

appEnvVar :: String -> IE Value
appEnvVar x = rdEnv >>= \rho ->
              case (rho x) of
                (V v)  -> return v
                GLOBAL -> get_global x

appEnvJmp :: String -> IE [Stmt]
appEnvJmp s = rdEnv >>= \rho ->
              case (rho s) of
                (L p) -> return p

--
-- extend the current variable environment:
--
xVEnv :: String -> Value -> IE IEnv
xVEnv x v = rdEnv >>= \rho -> return (tweek rho x (V v))

xVEnv_fold :: [(String, Value)] -> IE IEnv
xVEnv_fold = foldr (\(x, v) -> \m -> xVEnv x v >>= \rho -> inEnv rho m) (rdEnv)

--
-- extend the current jump label environment:
--
xLEnv :: String -> [Stmt] -> IE IEnv
xLEnv x ss = rdEnv >>= \rho -> return (tweek rho x (L ss))


--
-- extend the declared function environment
--
-- (in general, should only happen at initialization)
--
xFEnv :: String -> ([Param], ([VarDecl], [Stmt])) -> IE IEnv
xFEnv x v = rdEnv >>= \rho -> return (tweek rho x (F v))

--
-- variable to which functions always return their values:
--
retval :: String
retval = "__ret"


--
-- read from a global variable:
--
get_global :: String -> IE Value
get_global x =

  liftEnv $
    get >>= \(vs, _) ->
    case (lookup x vs) of
      (Just v) -> return v
      Nothing  -> error $ "couldn't locate global variable " ++ x

--
-- write to a global variable:
--
put_global :: String -> Value -> IE ()
put_global x v =

  liftEnv $
    upd
      (\(y, z) ->
        ((map (\(x', v') -> if x' /= x then (x', v') else (x', v)) y), z))

--
-- pop the current environment from the stack:
--
pop_estack :: IE Env
pop_estack =

  liftEnv $
    get >>= \(vs, (p:ps)) ->
    upd (const (vs, ps)) >>
    return p

--
-- push an environment onto the global stack:
--
push_estack :: Env -> IE () 
push_estack p =

  liftEnv $
    upd
      (\(y, z) -> (y, p:z))


--
-- read the contents of the current stack:
--
get_estack :: IE EStack
get_estack = liftEnv $ get >>= \(_, stk) -> return stk

--
-- project out of the monad:
--
prj :: IE a -> a
prj (ENV x) = fst $ deId ((deST (x (initenv))) (initst))

initst :: (Globals, EStack)
initst = ([], [[]])

initenv :: IEnv
initenv = \x -> if x /= envstk then (V Void) else GLOBAL

--
-- TOP-LEVEL INTERPRETER FUNCTION
-- 

etic_interp :: Prog -> Value
etic_interp = prj . prog_interp

prog_interp :: Prog -> IE Value
prog_interp (Prog ds) =

  let (vs, fs, ss) = siftdecs ds
      envs         = VarDecl [] (TyStack TyInt) envstk (Just EmptyStack)
  in

    mkfenv fs >>= \rho ->                           -- make function environment
    inEnv rho (mksenv ss) >>= \rho' ->              -- add data structures 
    inEnv rho' (mkglobals (envs:vs)) >>= \rho'' ->  -- set up imperative globals

    -- start at main (presently assuming main takes no arguments):
    inEnv rho'' (interp_stmt (ExprStmt $ FunCall "main0" [])) >>= \rho''' ->

    -- kick back the return value produced by executing 'main':
    inEnv rho''' (appEnvVar retval)



--
-- INITIALIZATION
-- 

--
-- put the declared global variables, some of which may
-- be initialized, into the state:
--
mkglobals :: [VarDecl] -> IE IEnv
mkglobals vs =

  let inits = map
                (\(VarDecl _ t x _) ->
                  case t of
                    (TyArray _ _) -> (x, ArrayVal [])
                    _             -> (x, Void)

                ) vs
  in

    liftEnv (upd (\(_, ys) -> (inits, ys))) >>

    foldr
    (\(VarDecl _ _ x e) -> \m ->

      case e of
        (Just e) -> eval e >>= \v ->
                    put_global x v >>
                    rdEnv >>= \rho ->
                    inEnv (tweek rho x GLOBAL)  m

        _        -> rdEnv >>= \rho ->
                    inEnv (tweek rho x GLOBAL)  m

    ) (rdEnv) vs

--
-- form the initial environment of function declarations:
--
mkfenv :: [((String, [Param]), ([VarDecl], [Stmt]))] -> IE IEnv
mkfenv =

{-
  (foldr
  (\((f, xs), (ds, ss)) -> \m ->

    xFEnv f (xs, (ds, ss)) >>= \rho ->
    inEnv rho m

  ) (rdEnv) fs) >>= \rho' ->
-}

  foldl
  (\m -> \((f, xs), (ds, ss)) ->

    m >>= \rho ->
    return (tweek rho f (F (xs, (ds, ss)))) >>= \rho' ->
    return rho'

  ) (rdEnv)


--
-- form the (static) environment of declared constants, data structures
--
mksenv :: [TopDecl] -> IE IEnv
mksenv =

  foldl
  (\m -> \d ->

    case d of

      -- bind enumerated constants:
      (EnumDec xs)     -> let cs = map (\(x, y) -> (x, IntVal y)) (zip xs ints)
                          in
                            m >>= \rho ->
                            inEnv rho (xVEnv_fold cs)

      -- associate a structure with its fields:
      (StructDec s xs) -> m >>= \rho ->
                          return $ tweek rho s (S xs)

      (UnionDec s xs)  -> m >>= \rho ->
                          return $ tweek rho s (S xs)

  ) (rdEnv)

--
-- INTERPRETER FUNCTIONS
-- 


--
-- execute a statement list:
--
exec :: [Stmt] -> IE IEnv
exec ((Return e):_) = eval e >>= \v ->
                      rdEnv >>= \rho ->
                      return (tweek rho retval (V v))

exec ((SysCall e):ss) = eval e >>= \v ->                   -- get the request
                        xVEnv r_signal v >>= \rho ->       -- set signal
                        inEnv rho (syscall ss) >>= \rho' -> -- make call
                        inEnv rho' (exec ss)
                        

exec (s:ss) = interp_stmt s >>= \rho ->
              inEnv rho (exec ss)

exec [] = rdEnv


syscall :: [Stmt] -> IE IEnv
syscall tcb = get_estack >>= \stk ->
              xVEnv envstk (EnvStackVal stk) >>= \rho ->
              let call = ExprStmt $ FunCall handler [Var envstk, MkThread tcb]
              in
                inEnv rho (interp_stmt call)

{-
  rdEnv >>= \rho ->

  foldr
  (\s -> \m ->

    case s of

      -- if a return statement, stop execution of the current
      -- statement list and assign the return-value component:
      (Return e) -> eval e >>= \v ->
                    return (tweek rho retval (V v))


      -- otherwise, execute statement and propagate its effects:
      --
      _          -> interp_stmt s >>= \rho ->
                    inEnv rho m >>= \rho' ->
                    return rho'

  ) (rdEnv) ss
-}


--
-- interpret a single statement:
--
interp_stmt :: Stmt -> IE IEnv

--
-- assign a variable:
--
interp_stmt (Assign (LHSVar x) e)      = eval e >>= \v ->
                                         rdEnv >>= \rho ->
                                         case (rho x) of
                                           (V _)  -> xVEnv x v
                                           GLOBAL -> put_global x v >>
                                                     return rho
--
-- assign a single element of an array:
--
interp_stmt (Assign (LHSVarIX x e) e') = eval e >>= \(IntVal i) ->
                                         eval e' >>= \v ->
                                         rdEnv >>= \rho ->

                                         case (rho x) of

                                           (V a)  -> let a' = array_put a i v
                                                     in
                                                       xVEnv x a'

                                           GLOBAL -> get_global x >>= \a ->
                                                     let a' = array_put a i v
                                                     in
                                                       xVEnv x a'
--
-- declare and assign a variable:
--
interp_stmt (DeclStmt (VarDecl _ _ x (Just e))) = interp_stmt $
                                                    Assign (LHSVar x) e

--
-- declaring without an assignment has no effect in the interpreter;
--
interp_stmt (DeclStmt (VarDecl _ _ _ Nothing)) = rdEnv

--
-- execute a conditional branch:
--
interp_stmt (IfThenElse e ss (Just ss')) = eval e >>= \(BoolVal b) ->
                                           if b then (exec ss) else (exec ss')

interp_stmt (IfThenElse e ss Nothing)    = eval e >>= \(BoolVal b) ->
                                           if b then (exec ss) else rdEnv

--
-- run a loop:
--
interp_stmt (Loop l ss) = xLEnv l ss >>= \rho ->
                          inEnv rho (exec ss)

--
-- jump to the head of a loop:
--
interp_stmt (Jump l)    = appEnvJmp l >>= \ss ->
                          exec ss

--
-- run an expression that may have imperative side-effects;
--
-- these happen through an indirect call-back in the evaluator.
--
interp_stmt (ExprStmt e) = eval e >> rdEnv

--
-- 'Return' is handled as a special case inside of 'exec', above;
--

--
-- nop:
--
interp_stmt Skip = rdEnv



--
-- expression evaluator:
--
eval :: Expr -> IE Value

--
-- arithmetic primitives:
--
eval (Add e e')    = eval e >>= \(IntVal v) ->
                     eval e' >>= \(IntVal v') ->
                     return (IntVal $ v + v')

eval (Sub e e')    = eval e >>= \(IntVal v) ->
                     eval e' >>= \(IntVal v') ->
                     return (IntVal $ v - v')

eval (Mul e e')    = eval e >>= \(IntVal v) ->
                     eval e' >>= \(IntVal v') ->
                     return (IntVal $ v * v')

eval (Div e e')    = eval e >>= \(IntVal v) ->
                     eval e' >>= \(IntVal v') ->
                     return (IntVal $ div v v')

eval (Modulus e e') = eval e >>= \(IntVal v) ->
                      eval e' >>= \(IntVal v') ->
                      return (IntVal $ mod v v')

--
-- logic primitives:
--
eval (Neg e)        = eval e >>= \(IntVal v) ->
                      return (IntVal $ negate v)

eval (AndLogic e e') = eval e >>= \(BoolVal b) ->
                       eval e' >>= \(BoolVal b') ->
                       return (BoolVal $ b && b')

eval (OrLogic e e')  = eval e >>= \(BoolVal b) ->
                       eval e' >>= \(BoolVal b') ->
                       return (BoolVal $ b || b')

eval (Not e)         = eval e >>= \(BoolVal b) ->
                       return (BoolVal $ not b)

eval (IsLT e e')     = eval e >>= \(IntVal v) -> 
                       eval e' >>= \(IntVal v') ->
                       return (BoolVal $ v < v')

eval (IsGT e e')     = eval e >>= \(IntVal v) -> 
                       eval e' >>= \(IntVal v') ->
                       return (BoolVal $ v > v')

eval (IsLTE e e')    = eval e >>= \(IntVal v) -> 
                       eval e' >>= \(IntVal v') ->
                       return (BoolVal $ v <= v')

eval (IsGTE e e')    = eval e >>= \(IntVal v) -> 
                       eval e' >>= \(IntVal v') ->
                       return (BoolVal $ v >= v')

eval (IsEq e e')    =  eval e >>= \v -> 
                       eval e' >>= \v' ->
                       return $ BoolVal $
                       case (v, v') of
                         (IntVal n, IntVal n')       -> n == n'
                         (BoolVal b, BoolVal b')     -> b == b'
                         (StringVal s, StringVal s') -> s == s'

eval (NotEq e e')   =  eval (IsEq e e') >>= \(BoolVal b) ->
                       return (BoolVal $ not b)

--
-- aggregate data structure operations:
--
eval (MkPair e e') = eval e >>= \v ->
                     eval e' >>= \v' -> 
                     return (Pair v v')


--
-- procedure call, with possible side-effects:
--

eval (FunCall f es) = mapM eval es >>= \vs ->            -- evaluate args
                      appEnvFun f >>= \(ps, (ds, ss)) -> -- get declaration
                      dec_vars ds >>= \rho ->            -- declare vars

                      -- bind parameters:
                      inEnv rho (xVEnv_fold (zip ps vs)) >>= \rho' ->

                      inEnv rho' (exec ss) >>= \rho'' ->  -- run body statements
                      inEnv rho'' (appEnvVar retval)      -- kick back return

--
-- whoa!  Hack city!
--
-- (2010.06.07) Schulz
--
eval (CtorApp "Empty" _ ) = return Void

--
-- form a struct-value from a constructor application:
--

eval (CtorApp c es) = mapM eval es >>= \vs ->        -- evaluate the args
                      appEnvStruct c >>= \as ->      -- get constructor fields
                      return $
                        StructVal c $ zipWith (\(x, _) -> \y -> (x, y)) as vs
                        


--
-- unions are trivial here, since the interpreter doesn't
-- have to deal with the vicissitudes of encoding or space allocation
--
{-
eval (UnionMember e _)  = eval e >>= \(StructVal _ [(_, v)]) ->
                          return v
-}
eval (UnionMember e _)  = eval e

--
-- access the fields of a struct:
--
eval (StructMember e ("__ctor__")) = eval e >>= \(StructVal s _) ->
                                     eval (Var (s ++ "__enum"))

eval (StructMember e ("__instance__")) = eval e

eval (StructMember e f) = eval e >>= \(StructVal s vs) ->
                          case vs of
                            [] -> eval (Var (s ++ "__enum"))
                            _  -> case (lookup f vs) of
                                    (Just v) -> return v
                                    _        -> error $ "couldn't locate " ++
                                                  "struct member \'" ++ f ++
                                                  " in " ++ (show e) ++ "\n"

-- in above:
-- 
-- an empty struct should be treated as interchangeable with
-- an enumerated constant, expected to be declared elsewhere;
-- this is a consequence of the compilation of 'data' declarations;
--



--
-- primitive stack operations:
--
eval EmptyStack  = return $ StackVal []

eval (IsEmpty e) = eval e >>= \stk ->
                   case stk of
                     (StackVal [])    -> return $ BoolVal True
                     (EnvStackVal []) -> return $ BoolVal True
                     _                -> return $ BoolVal False

eval (Pop e)     = eval e >>= \(StackVal (v:_)) ->
                   return v

eval (Push e e') = eval e >>= \v ->
                   eval e' >>= \(StackVal vs) ->
                   return $ StackVal (v:vs)

--
-- again, this is a simplification that works
-- in this context but will not in general
--
{-
eval (Top e)     = eval e >>= \(StackVal (v:_)) ->
                   return v
-}
eval (Top e)     = eval e >>= \v ->
                   case v of
                     (StackVal (v:_))    -> return v
                     (EnvStackVal (v:_)) -> return $ EnvVal v
                     _                   -> appEnvVar envstk >>= \v ->
                                            error $ show v
                                            

eval (SRest e)   = eval e >>= \(StackVal (_:vs)) ->
                   return $ StackVal vs

--
-- get a thread for execution:
--
eval (MkThread ss) = return $ TCB ss

--
-- create a time-slice block;
--
-- here this simply has the effect of producing the TCB
-- referenced in the argument (this may indicate a problem in ETIC)
--
eval (Slice e) = eval e

--
-- run a thread specified in an expression:
--
-- (call-back to the interpreter)
--
eval (RunThread e) = eval e >>= \t ->
                     case t of
                       (TCB t) -> exec t >>= \rho ->
                                  inEnv rho (appEnvVar retval) 
                       v       -> return v
--                       _       -> error $ show (e, t)
{-
eval (RunThread e) = eval e >>= \(TCB t) ->       -- get the thread
                     exec t >>= \rho ->           -- execute the thread
                     inEnv rho (appEnvVar retval) -- kick back the return value
-}

eval (TTail e)     = eval e >>= \t ->
                     return t

--
-- accesses to the TCB:
--
eval (IsDone e)   = eval e >>= \(TCB ss) ->
                    case ss of
                      [] -> return $ BoolVal True
                      _  -> return $ BoolVal False

--
-- a quick kludge, where access to the 'signal' component
-- a TCB simply reads from the global signal reigster;
--
-- this probably needs to be replaced with a stack-like structure
-- in the future
--
-- (2010.06.05) Schulz
--
eval (SigOf _)    = eval (Var r_signal) 

--
-- variable lookups:
--
eval (Var x)       = appEnvVar x

eval (VarIX x e)   = appEnvVar x >>= \a ->
                     eval e >>= \(IntVal v) ->
                     return (array_get v a)

{-
                     eval e >>= \v ->
                     case v of
                       (IntVal v) ->  return (array_get v a)
                       v          -> error $ show ((x, a), (e, v))
-}

--
-- literals:
--
eval (LitInt n)    = return $ IntVal $ fromInteger n
eval (LitBool b)   = return $ BoolVal b
eval (LitString s) = return $ StringVal s

eval x = error $ show x


--
-- add a list of variable declarations, which may be initialized,
-- to the current environment:
--
dec_vars :: [VarDecl] -> IE IEnv
dec_vars =

  foldr
  (\(VarDecl _ _ x e) -> \m ->

    (
      case e of
        (Just e) -> eval e >>= \v ->  -- if initialized, bind
                    xVEnv x v

        Nothing  -> xVEnv x Void    -- else add to the environment with no value
    ) >>= \rho ->

    inEnv rho m

  ) (rdEnv)



--
-- HELPER FUNCTIONS
--

tweek :: IEnv -> String -> SymLkp -> IEnv
tweek rho x v = \x' -> if x /= x' then rho x' else v


ints :: [Int]
ints = iterate (+ 1) 0

--
-- sift declarations according to their various sorts:
--
siftdecs :: [TopDecl] -> ([GVarDec], [FunDec], [SDec])
siftdecs =

  foldr
  (\d -> \(gs, fs, ts) ->

    case d of
      (FunDecl _ f xs ds ss)      -> (gs,((f, map snd xs),(ds, ss)):fs,ts)
      (TopVarDecl v)              -> (v:gs, fs, ts)
      s@(StructDec _ _)           -> (gs, fs, s:ts)
      s@(UnionDec _ _)            -> (gs, fs, s:ts)
      s@(EnumDec _)               -> (gs, fs, s:ts)

  ) ([], [], [])

--
-- using zero as the starting index for arrays, as usual:
--
array_get :: Int -> Value -> Value
array_get n (ArrayVal vs) = head $ drop n vs

array_put :: Value -> Int -> Value -> Value
array_put (ArrayVal vs) n v = ArrayVal $ (take n vs) ++ v:(drop (n + 1) vs)


--
-- system-dependent constants of the abstract machine:
--

--
-- the environment stack, currently in place for
-- special use with the reification example:
--
-- (2010.06.06) Schulz
--
envstk :: String
envstk = "ENV_STK"

--
-- a distinguished register for holding the response
-- from the handler
--
r_signal :: Reg
r_signal = "r_SIGNAL"


--
-- expected label for the handler:
--
handler :: String
handler = "hand0"


-- THIS IS THE END OF THE FILE --
