--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/OESS/Compile.hs
--
-- the CT-to-OESS code generation module;
--
-- put here 2010.06.25
--
-- Schulz
--

module Deprecated.OESS.Compile where

import Deprecated.OESS.Syntax

import CT.Syntax
import CT.INAST
import CT.MonadicConstructions


--                --
-- TOP LEVEL CALL --
--                --

--
-- switching point for organizing type-directed compilation:
--
compile_any :: INAST -> SC (Block, BlockPile)
compile_any e =
  case (typeofinast e) of

    (CTMTy ResTy _)          -> compile_R e
    (CTMTy (ReactTy _ _) _)  -> compile_Re e
    (CTMTy StateTy _)        -> compile_K e
    _                        -> compile_I e



--
-- wrapper for making type-directed compilation work:
--
data Code = StrmCode Stream
          | ThrdCode TCode
          | ImprCode STBlock
          | ExprCode Expr


type Reg = String

--
-- any call to the compilation functions may return a
-- pile of code blocks that need to be added to the output:
--
type BlockPile = [Block]



--
-- environment separates function symbols from variable symbols:
--
data Binding = VBind | FBind Label [Reg]

--
--
-- code generation monad, and its operations:
--
--

type OEnv = String -> Binding

type SC a = EnvT OEnv (StateT Int Id) a

--
-- get the parameters bound to a declared function:
--
argsof :: String -> SC [String]
argsof f = rdEnv >>= \rho -> case (rho f) of
                               (FBind _ xs) -> return xs

--
-- get the label bound to a function:
--
localof :: String -> SC Label
localof f = rdEnv >>= \rho -> case (rho f) of
                                (FBind l _) -> return l


--
-- make a new variable name:
--
genvar :: SC String
genvar =

  liftEnv $

    get >>= \n ->
    upd (const (n + 1)) >>
    return (internal_var ++ (show n))

--
-- make a new code label:
--
genlabel :: SC String
genlabel =

  liftEnv $

    get >>= \n ->
    upd (const (n + 1)) >>
    return (internal_label ++ (show n))



--
-- COMPILATION TRANSFORMATIONS
--

--
-- compilation of the resumption monad:
--
compile_R :: INAST -> SC (Block, BlockPile)

--
-- resumptive sequencing:
--
compile_R (CTBindIN e (CTLamIN x e' _) _) = compile_R e >>= \(b, c) ->
                                            compile_R e' >>= \(b', c') ->
                                            genlabel >>= \l ->
                                            let (StrmBlock _ s)   = b
                                                (StrmBlock _ s'') = b'
                                            in
                                              let a  = Assign R_Ret 
                                                         (DeRef (Var x))
                                                  s' = FBy (Atom (Stmt a)) s''
                                                  r  = streamcat s s'
                                              in
                                               return ((StrmBlock l r), c ++ c')
                                                


compile_R (CTNullBindIN e e' _)           = compile_R e >>= \(b, c) ->
                                            compile_R e' >>= \(b', c') ->
                                            genlabel >>= \l ->
                                            let (StrmBlock _ s)  = b
                                                (StrmBlock _ s') = b'
                                            in
                                              let r = streamcat s s'
                                              in
                                               return ((StrmBlock l r), c ++ c')

compile_R app@(CTAppIN _ _ _) = let (f, as) = dconapp app
                                in

                                  -- compile argument code:
                                  (
                                    foldr
                                    (\a -> \m ->
                                      compile_any a >>= \(p, c) ->
                                      m >>= \(ps, c') ->
                                      (return ((p:ps), (c ++ c')))
                                    )
                                      (return ([], [])) as

                                  ) >>= \(ps, cs) -> 

                                  -- situate argument code within the stream:
                                  (
                                    foldr
                                    (\p -> \m ->

                                      (

                                      case p of


                                        (StrmBlock l _) -> genvar >>= \v ->
                                                           let t = DeRef R_TCT
                                                               s = xassign v t
                                                           in
                                                           return $

                                                             (v, 

                                                             -- create thread:
                                                             FBy 
                                                               (KCreate 
                                                                 (KThread t l))

                                                               (FBy
                                                                 (Atom
                                                                  (Seq s inctid)
                                                                 )
                                                                 Halt)
                                                              )

                                        (ThrdBlock l _) -> genvar >>= \v ->
                                                           let t = DeRef R_TCT
                                                               s = xassign v t
                                                           in
                                                           return $

                                                             (v, 

                                                             -- create thread:
                                                             FBy 
                                                               (TCreate 
                                                                 (UThread t l))

                                                               (FBy
                                                                 (Atom
                                                                  (Seq s inctid)
                                                                 )
                                                                 Halt)
                                                              )


                                        (ImprBlock l _) -> genvar >>= \v ->
                                                           let e' = LabelRef l
                                                           in
                                                           return 
                                                             (v, 
                                                               FBy
                                                                 (Atom $ Stmt $
                                                                   xassign v e')
                                                                 Halt
                                                             )

                                        (ExprBlock _ e) -> genvar >>= \v ->
                                                           return
                                                             (v, 
                                                               FBy
                                                                 (Atom $ Stmt $
                                                                   xassign v e)
                                                                 Halt
                                                             )

                                      ) >>= \p' ->

                                      m >>= \ps ->
                                      return (p':ps)

                                    )
                                      (return []) ps

                                  ) >>= \s ->
                                  
                                  -- make the assignments in the prologue:
                                  argsof f >>= \xs ->
                                  localof f >>= \f' ->
                                  let as = foldr
                                           (\(r, x) -> \as -> (rassign r x):as)
                                             [] (zip (map fst s) xs)

                                      -- put together the stream code:
                                      s' = SJSR f' Halt
                                      ss = foldr
                                           (\s -> \s' -> streamcat s s')
                                             s' (map snd s)
                                  in
                                    genlabel >>= \l ->
                                    return (StrmBlock l ss, (ps ++ cs))

--
-- control flow:
--

compile_R (CTBranchIN g e e' _)          = compile_I g >>= \(g', cs'') ->
                                           compile_R e >>= \(b, cs) ->
                                           compile_R e' >>= \(b', cs') ->
                                           genlabel >>= \l ->
                                           let (StrmBlock _ r)  = b
                                               (StrmBlock _ r') = b'
                                               (ExprBlock _ x)  = g'
                                           in
                                             let s   = Atom (Stmt (TestZ x))
                                                 s'  = FBy s (SBZ r r' Halt)
                                                 s'' = FBy s s'
                                             in
                                               return
                                                 (StrmBlock l s'',
                                                   (cs ++ cs' ++ cs'')) 

compile_R (CTLoopIN (CTLamIN x r _) _)   = compile_R r >>= \(p, c) ->
                                           let (StrmBlock _ r') = p
                                           in
                                             let ret  = xassign x (DeRef R_Ret)
                                                 s    = Atom (Stmt ret)
                                                 strm = FBy s r'
                                                 loop = Loop strm Halt
                                             in
                                               genlabel >>= \l ->
                                               return (StrmBlock l loop, c)

--
-- resumptive primitives:
--

compile_R (CTStepIN k _)                 = compile_K k >>= \(p, c) ->
                                           genlabel >>= \l ->
                                           let (ImprBlock _ k') = p
                                           in
                                             return
                                               (StrmBlock l
                                                 (FBy (Atom k') Halt),
                                                   c)


compile_R (CTReturnIN e _)               = compile_I e >>= \(a, c) ->
                                           genlabel >>= \l ->
                                           let (ExprBlock _ e) = a
                                           in
                                             let s = Stmt (Assign R_Ret e)
                                             in
                                               return
                                                 (StrmBlock l
                                                   (FBy (Atom s) Halt), c)

--
-- compilation of the reactive resumption monad:
--
compile_Re :: INAST -> SC (Block, BlockPile)

--
-- reactive sequencing:
--

compile_Re (CTBindIN e (CTLamIN x e' _) _) = compile_Re e >>= \(b, c) ->
                                             compile_Re e' >>= \(b', c') ->
                                             genlabel >>= \l ->
                                             let (ThrdBlock _ t)   = b
                                                 (ThrdBlock _ t'') = b'
                                             in
                                               let a  = Assign R_Ret 
                                                          (DeRef (Var x))
                                                   t' = TSeq (Cont (Stmt a)) t''
                                                   r  = threadcat t t'
                                               in
                                                return ((ThrdBlock l r),c ++ c')


compile_Re (CTNullBindIN e e' _)           = compile_Re e >>= \(b, c) ->
                                             compile_Re e' >>= \(b', c') ->
                                             genlabel >>= \l ->
                                             let (ThrdBlock _ t)  = b
                                                 (ThrdBlock _ t') = b'
                                             in
                                               let r = threadcat t t'
                                               in
                                                return ((ThrdBlock l r),c ++ c')

--
-- control flow:
--

compile_Re (CTBranchIN g e e' _)         = compile_I g >>= \(g', cs'') ->
                                           compile_Re e >>= \(b, cs) ->
                                           compile_Re e' >>= \(b', cs') ->
                                           genlabel >>= \l ->
                                           let (ThrdBlock _ r)  = b
                                               (ThrdBlock _ r') = b'
                                               (ExprBlock _ x)  = g'
                                           in
                                             let t   = Cont (Stmt (TestZ x))
                                                 t'  = TSeq t (TBZ r r' TDone)
                                                 t'' = TSeq t t'
                                             in
                                               return
                                                 (ThrdBlock l t'',
                                                   (cs ++ cs' ++ cs'')) 


compile_Re (CTLoopIN (CTLamIN x r _) _)  = compile_Re r >>= \(p, c) ->
                                           let (ThrdBlock _ r') = p
                                           in
                                             let ret  = xassign x (DeRef R_Ret)
                                                 s    = Cont (Stmt ret)
                                                 term = TSeq s r'
                                                 loop = TLoop term TDone
                                             in
                                               genlabel >>= \l ->
                                               return (ThrdBlock l loop, c)

--
-- reactive primitives:
--

compile_Re (CTStepIN k _)                = compile_K k >>= \(p, c) ->
                                           genlabel >>= \l ->
                                           let (ImprBlock _ k') = p
                                           in
                                             return
                                               (ThrdBlock l
                                                 (TSeq (Cont k') TDone), c)

compile_Re (CTReturnIN e _)              = compile_I e >>= \(a, c) ->
                                           genlabel >>= \l ->
                                           let (ExprBlock _ e) = a
                                           in
                                             let s = Stmt (Assign R_Ret e)
                                             in
                                               return
                                                 (ThrdBlock l
                                                   (TSeq (Cont s) TDone), c)


--
-- compilation of the state monad:
--
compile_K :: INAST -> SC (Block, BlockPile)

--
-- sequencing:
--
compile_K (CTBindIN e (CTLamIN x e' _) _) = compile_K e >>= \(b, c) ->
                                            compile_K e' >>= \(b', c') ->
                                            genlabel >>= \l ->
                                            let (ImprBlock _ a)  = b
                                                (ImprBlock _ a') = b'
                                            in
                                              let s  = Assign (Var x)
                                                         (DeRef R_Ret)
                                                  s' = codecat a (Seq s a')
                                              in
                                                return (ImprBlock l s', c ++ c')


compile_K (CTNullBindIN e e' _)           = compile_K e >>= \(b, c) ->
                                            compile_K e' >>= \(b', c') ->
                                            genlabel >>= \l ->
                                            let (ImprBlock _ a)  = b
                                                (ImprBlock _ a') = b'
                                            in
                                              let s' = codecat a a'
                                              in
                                                return (ImprBlock l s', c ++ c')

--
-- local branching:
--
compile_K (CTBranchIN g e e' _) = compile_I g >>= \(b, c) ->
                                  compile_K e >>= \(b', c') ->
                                  compile_K e' >>= \(b'', c'') ->
                                  genlabel >>= \l ->
                                  let (ExprBlock _ g')  = b
                                      (ImprBlock _ k')  = b'
                                      (ImprBlock _ k'') = b''
                                  in
                                    let tst = TestZ g'
                                        br  = Seq tst (BZ k' k'' (Stmt NOP))
                                    in
                                      return (ImprBlock l br, c ++ c' ++ c'')

--
-- state primitives:
--
compile_K (CTPutIN x e _)   = compile_I e >>= \(b, c) ->
                              genlabel >>= \l ->
                              let (ExprBlock _ a) = b
                              in
                                let s   = Assign (Var x) a    -- make assignment
                                    s'  = Assign R_Ret Clear  -- clear retval
                                    s'' = Seq s (Stmt s')
                                in
                                  return (ImprBlock l s'', c)

compile_K (CTGetIN x _)     = let s = Stmt $ Assign R_Ret (DeRef (Var x))
                              in
                                genlabel >>= \l ->
                                return (ImprBlock l s, [])


compile_K (CTReturnIN e _)  = compile_I e >>= \(a, c) ->
                              genlabel >>= \l ->
                              let (ExprBlock _ e) = a
                              in
                                let s = Stmt (Assign R_Ret e)
                                in
                                  return
                                    (ImprBlock l s, c)



--
-- compilation of non-monadic (or Identity) expressions:
--
compile_I :: INAST -> SC (Block, BlockPile)

-- STUB (2010.07.08)
compile_I _ = return (ExprBlock "" Clear, [])

{-

--
-- primitive expressions:
--
compile_I (CTPrim1aryIN op e _) = compile_I e >>= \i ->
                                  case op of
                                    (Un CTNeg) -> return (Neg i)
                                    (Un CTNot) -> return (Not i)


compile_I (CTPrim2aryIN op e e' _) = compile_I e >>= \i ->
                                     compile_I e' >>= \i' ->
                                     case op of
                                       (Bin CTPlus)  -> return (Add i i')
                                       (Bin CTMinus) -> return (Sub i i')
                                       (Bin CTMult)  -> return (Mul i i')
                                       (Bin CTIDiv)  -> return (Div i i')
                                       (Bin CTAnd)   -> return (And i i')
                                       (Bin CTOr)    -> return (Or i i')

--
-- tuples:
--
compile_I (CTPair e e' _) = compile_any e >>= \c ->
                            setup_code c >>= \(r, p) ->
                            compile_any e' >>= \c' ->
                            setup_code c' >>= \(r', p') ->

--
-- references:
--
compile_I (CTVarIN x _)           = return (DeRef (Var x))

--
-- literals:
--
compile_I (CTLitIN (LitInt n) _)  = return (SInt n)
compile_I (CTLitIN (LitBool b) _) = return (SBool b)
compile_I (CTLitIN UnitEl _)      = return Clear
compile_I (CTUnitIN _)            = return Clear
-}


--
-- HELPER FUNCTIONS
--

--
-- make temporary assignments for generalized 'code'
-- in the sum-type produced by 'compile_any'
--
setup_code :: Code -> SC (String, STCode)

--
-- for case of stream code, thread must actually be created
-- before the assignment is run, which is done elsewhere NOT HERE;
--
-- note, however, the TID counter is incremented in anticipation
-- of a new thread creation
--
-- 2010.07.07 Schulz
--
setup_code (StrmCode s) = genvar >>= \x ->
                          return
                            (x,
                               Seq
                                 -- set 'x' to the anticipated TID:
                                 (xassign x (DeRef R_TCT))

                                 -- increment the TID counter:
                                 (Stmt
                                   (Assign R_TCT
                                     (Add (DeRef R_TCT) (SInt 1))
                                   )
                                 )
                            )

setup_code (ThrdCode t) = genvar >>= \x ->
                          return
                            (x,
                               Seq
                                 -- set 'x' to the anticipated TID:
                                 (xassign x (DeRef R_TCT))

                                 -- increment the TID counter:
                                 (Stmt
                                   (Assign R_TCT
                                     (Add (DeRef R_TCT) (SInt 1))
                                   )
                                 )
                            )

--
-- code produced by 'compile_any' comes as a block; assignment
-- is made to the start of this block
--
setup_code (ImprCode k) = genvar >>= \x ->
                          return
                            (x,
                              (Stmt (xassign x (LabelRef (labelof k)))))

--
-- simple assignment should suffice for non-monadic expressions
--
setup_code (ExprCode e) = genvar >>= \x ->
                          return
                             (x, 
                               (Stmt (xassign x e)))

--
-- deconstruct an application:
--
dconapp :: INAST -> (String, [INAST])
dconapp (CTAppIN (CTVarIN f _) a' _) = (f, [a'])
dconapp (CTAppIN a a' _)             = case (dconapp a) of
                                         (f, as) -> (f, as ++ [a'])

--
-- short-hand for the imperative code that increments the TID counter:
--
inctid :: STCode
inctid = Stmt $ Assign R_TCT (Add (DeRef (R_TCT)) (SInt 1))

--
-- short-hand for passing the value of one variable to another:
--
rassign :: String -> String -> Stmt
rassign x y = Assign (Var x) (DeRef (Var y))

--
-- short-hand for assigning an expression to a variable:
--
xassign :: String -> Expr -> Stmt
xassign x e = Assign (Var x) e


--
-- essentially list concatenation;
--
-- this preserves right-associativity of the data structure
--
codecat :: STCode -> STCode -> STCode
codecat (Seq k s) s'  = Seq k (codecat s s')
codecat (BZ t f s) s' = BZ t f (codecat s s')
codecat (JSR l s) s'  = JSR l (codecat s s')
codecat (Stmt s) s'   = Seq s s'

--
-- same as above, for streams:
--
streamcat :: Stream -> Stream -> Stream
streamcat (FBy a s) s'    = FBy a (streamcat s s')
streamcat (Loop s s'') s' = Loop s (streamcat s' s'')
streamcat (SJSR l s) s'   = SJSR l (streamcat s s')
streamcat (SBZ t f s) s'  = SBZ t f (streamcat s s')
streamcat Halt s'         = s'

--
-- for threads:
--
-- note that 'pthread_exit' on the LHS is discarded
-- only because it is used as a place-holder by the compiler;
-- the R-most occurence should remain intact
--
threadcat :: TCode -> TCode -> TCode
threadcat (TSeq a t) t'    = TSeq a (threadcat t t')
threadcat (TLoop t t'') t' = TLoop t (threadcat t' t'')
threadcat (TBZ z n t) t'   = TBZ z n (threadcat t t')
threadcat (TJSR l t) t'    = TJSR l (threadcat t t')
threadcat (TDone) t'       = t'


--
-- the standard compiler-generated variable prefix:
--
internal_var :: String
internal_var = "__compiler_var__"

--
-- standard compiler-generated label prefix:
--
internal_label :: String
internal_label = "__LABEL__"



-- THIS IS THE END OF THE FILE --
