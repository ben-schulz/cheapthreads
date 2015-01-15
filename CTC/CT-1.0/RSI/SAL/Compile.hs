--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/SAL/Compile.hs
--
-- generation of three-address code from RSI
--
-- put here (2010.10.14)
--
-- Schulz
--

module RSI.SAL.Compile where

import RSI.Syntax
import RSI.SAL.Syntax
import RSI.SAL.FlowAnalysis

import CT.MonadicConstructions


--                 --
-- TOP LEVEL CALLS --
--                 --

--
-- generate the next program representation:
--
gen_sal :: RSI_B -> SAL
gen_sal (RSI_B (ds, (l, ps))) =

  let ps' = foldr
            (\p -> \m ->

              compile_code p >>= \j -> 
              m >>= \js ->
              return (j:js)

            ) (return []) ps
  in

    SAL (ds, (l, prj_GS ps'))


--
-- compute the annotated control flow graph:
--
gen_flow :: SAL -> SAL_AN
gen_flow (SAL (ds, (l, as))) = SAL_AN (ds, (l, map flanalyze as))


--
-- generate and apply the register allocation map:
--



--                   --
-- COMPILATION MONAD --
--                   --


--
-- just your generic state monad, for generating fresh virtual registers,
-- plus an environment for scoping loops::
--
type GS a = EnvT LEnv (StateT (Int, Int) Id) a

type LEnv = Label

initlenv = ""

genreg :: GS VReg
genreg = liftEnv $
           get >>= \(n, _) ->
           upd (\(x, y) -> (x + 1, y)) >>
           return (VReg n)

genlabel :: GS Label
genlabel = liftEnv $
             get >>= \(_, n) ->
             upd (\(x, y) -> (x, y + 1)) >>
             return (asl ++ (show n))

initct = (1, 0)

asl = "__ASM_LABEL"

-- i.e. run StateT for final return value
prj_GS m = fst $ deId $ (deST ((deENV m) initlenv)) initct


--                    --
-- COMPILER CONSTANTS --
--                    --

--
-- common numeric constants:
--
zero  = Num 0
one   = Num 1
ffff  = Num (-1)

--
-- Boolean constants:
--
false = Num 0
true = Num 1

-- use the convention that r0 is a constant zero value, as in MB
rzero = VReg 0


-- the monadic return register:
rret = SReg R_Ret
rrti = SReg R_Rti



compile_code :: Code_B -> GS InsSeq

compile_code (R_B l c) = compile_chain c >>= \j ->
                         return (Labeled l j)

compile_code (K_B l c) = compile_block c >>= \j ->
                         return (Labeled l j)



--
-- compilation of chains, i.e. control-structured code;
--
-- note that, as written, every chain should compile to
-- an instruction sequence beginning with a corresponding label
--
compile_chain :: Chain_B -> GS InsSeq

compile_chain (Seq_B b c)     = compile_block b >>= \j ->
                                compile_chain c >>= \j' ->
                                return (inscat j j')

compile_chain (BZ_B l e c c' c'') = compile_expr e >>= \(v, j) -> 
                                    compile_chain c >>= \j' ->
                                    compile_chain c' >>= \j'' ->
                                    compile_chain c'' >>= \j''' ->

                                    let br = startof c'    -- branch label
                                        rs = startof c''   -- join label

                                        -- form the branch code
                                        bz = MBZ v (Adr br)
                                        hd = inscat j (Semi bz Nil)

                                        -- append a jump to control-join
                                        -- to the fall-through (true) code:
                                        jp = MJmpI (Adr rs)
                                        tr = inscat j' (Semi jp Nil)

                                        -- label the branch target:
                                        fl = Labeled br j''

                                        -- label the rejoin:
                                        rj = Labeled rs j'''

                                        -- put it all together:
                                        as = inscat hd
                                               (inscat tr (inscat fl rj))
                                    in
                                      return (Labeled l as)

compile_chain (Loop_B l c c') = inEnv l (compile_chain c) >>= \j ->
                                compile_chain c' >>= \j' ->

                                -- unconditional jump to head of loop:
                                let br = MJmpI (Adr l)

                                -- append unconditional jump to end of body:
                                    bd = inscat j (Semi br Nil)
                                in
                                  return (Labeled l (inscat bd j'))

compile_chain (Break_B l e)   = rdEnv >>= \l' ->
                                compile_expr e >>= \(v, j) ->

                                let br = MJmpI (Adr l') -- jump out of loop
                                    rt = Mov rret v    -- put expr value in ret

                                    -- code for the break:
                                    bk = inscat j (Semi rt (Semi br Nil))
                                in
                                  return (Labeled l bk)
                                
--
-- this compilation case makes several important simplifying assumptions;
-- see log (2010.11.02) for details
--
-- Schulz
--
compile_chain (Swr_B l r c)   = compile_chain c >>= \j ->
                                compile_ref r >>= \(r', j') ->

                                let sw  = MJmp r'    -- the jump, 
                                    rt  = Semi sw j  -- plus the code following,
                                    rt' = inscat j' rt
                                in
                                  return (Labeled l rt')

--
-- note the similarity to the case above; does this bother you?
--
-- (2010.11.02) Schulz
--
compile_chain (Jmp_B l r c)   = compile_chain c >>= \j ->
                                compile_ref r >>= \(r', j') ->

                                let sw  = MJmp r'    -- the jump, 
                                    rt  = Semi sw j  -- plus the code following,
                                    rt' = inscat j' rt
                                in
                                  return (Labeled l rt')


compile_chain (LabelPt_B l c) = compile_chain c >>= \j ->
                                return (Labeled l j)

compile_chain (Halt_B l)      = return (Labeled l Nil)



compile_block :: Block -> GS InsSeq
compile_block (Block l k) = compile_asm k >>= \j ->
                            return (Labeled l j)


compile_asm :: ASM -> GS InsSeq

compile_asm (FBy s k)         = compile_stmt s >>= \j ->
                                compile_asm k >>= \j' ->
                                return (inscat j j')

compile_asm (BZ_K e b b' b'') = compile_expr e >>= \(v, j) ->
                                compile_block b >>= \j' ->
                                compile_block b' >>= \(Labeled l j'') ->
                                compile_block b'' >>= \(Labeled l' j''') ->

                                let bz = MBZ v (Adr l)    -- branch point
                                    jp = MJmpI (Adr l')   -- rejoin point

                                    -- form the branch header:
                                    br = inscat j (Semi bz Nil)

                                    fl = Labeled l j''            -- zero br
                                    tr = inscat j' (Semi jp Nil)  -- nonzero br
                                    rs = Labeled l' j'''          -- rejoin

                                in
                                  return
                                    (inscat br (inscat tr (inscat fl rs)))
                                  
compile_asm End = return Nil




compile_stmt :: Stmt -> GS InsSeq

-- 'assignments' to IMR are actually distinguished instructions:
compile_stmt (Assign IMR e) = compile_expr e >>= \(v, j) -> -- get a one/zero
                              genlabel >>= \l ->
                              genlabel >>= \fl ->

                              -- make a small branch to set/clear interrupt bit
                              -- according to value of the expression:
                              let br = MBZ v (Adr fl)

                                  -- if non-zero expr arg, set:
                                  t  = Semi IMR_Set (Semi (MJmpI (Adr l)) Nil)

                                  -- otherwise clear:
                                  f  = IMR_Clr

                                  -- otherwise clear:
                                  cn = Labeled l (Semi Nop Nil)
                              in
                                return
                                  (inscat j (Semi br (inscat t (Semi f cn))))

-- all other assignments:
compile_stmt (Assign r e) = compile_expr e >>= \(v, j) ->   -- get the value
                            compile_ref r >>= \(v', j') ->  -- get the location
                            let a0 = Store v' v rzero
                            in
                              return (inscat (inscat j j') (Semi a0 Nil))

-- see note on assignments to IMR above;
compile_stmt (Set IMR)    = return (Semi IMR_Set Nil)

compile_stmt (Set r)      = compile_ref r >>= \(v, j) ->
                            let a0 = MovI v one
                            in
                              return (inscat j (Semi a0 Nil))

compile_stmt (Clr IMR)    = return (Semi IMR_Clr Nil)

compile_stmt (Clr r)      = compile_ref r >>= \(v, j) ->
                            let a0 = Mov v rzero
                            in
                              return (inscat j (Semi a0 Nil))

compile_stmt (Tst e)      = compile_expr e >>= \(v, j) ->
                            let a0 = MTst (SReg R_Z) v -- weird idiom for set_z
                            in
                              return (inscat j (Semi a0 Nil))

compile_stmt NOP          = return (Semi Nop Nil)

--
--
-- compilation of primitive expressions:
--
--
compile_expr :: Expr -> GS (VReg, InsSeq)

--
-- folding of high-level references into registers:
--
compile_expr (DeRef r) =

  case r of

    (Var x)          -> genreg >>= \v ->
                        let ld = LoadI v rzero (Adr x)
                        in
                          return (v, Semi ld Nil)

    (LabelRef l)     -> genreg >>= \v ->
                        let mv = MovI v (Adr l)
                        in
                          return (v, Semi mv Nil)

    (StructFld r' f) -> compile_expr (DeRef r') >>= \(v, j) ->
                        genreg >>= \v' ->
                        let ld = LoadI v' v (SOffSet f)
                        in
                          return (v', inscat j (Semi ld Nil))

    (UnionFld r' f)  -> compile_expr (DeRef r') >>= \(v, j) ->
                        genreg >>= \v' ->
                        let ld = LoadI v' v (SOffSet f)
                        in
                          return (v', inscat j (Semi ld Nil))

    -- distinguished registers from RSI map onto themselvers, for now:
    R_Ret            -> return (SReg R_Ret, Nil)
    R_Rti            -> return (SReg R_Rti, Nil)
    R_Pro            -> return (SReg R_Pro, Nil)
    R_Nxt            -> return (SReg R_Nxt, Nil)
    R_Req            -> return (SReg R_Req, Nil)
    R_Z              -> return (SReg R_Z, Nil)
    IMR              -> return (SReg IMR, Nil)
    INR              -> return (SReg INR, Nil)


    -- declared constants are resolved by the assembler:
    (DecConstant c)  -> genreg >>= \v ->
                        let mv = MovI v (Symbol c)
                        in
                          return (v, Semi mv Nil)

    (SysConstant c)  -> genreg >>= \v ->
                        let mv = MovI v (Symbol c)
                        in
                          return (v, Semi mv Nil)

--
-- register arithmetic:
--
compile_expr (Add e e') = compile_expr e >>= \(v, j) ->
                          compile_expr e' >>= \(v', j') ->
                          genreg >>= \v'' ->
                          let ad = MAdd v'' v v'
                          in
                            return (v'', inscat j (inscat j' (Semi ad Nil)))

compile_expr (Sub e e') = compile_expr e >>= \(v, j) ->
                          compile_expr e' >>= \(v', j') ->
                          genreg >>= \v'' ->
                          let sb = MSub v'' v v'
                          in
                            return (v'', inscat j (inscat j' (Semi sb Nil)))

compile_expr (Mul e e') = compile_expr e >>= \(v, j) ->
                          compile_expr e' >>= \(v', j') ->
                          genreg >>= \v'' ->
                          let ml = MMul v'' v v'
                          in
                            return (v'', inscat j (inscat j' (Semi ml Nil)))

compile_expr (Div e e') = compile_expr e >>= \(v, j) ->
                          compile_expr e' >>= \(v', j') ->
                          genreg >>= \v'' ->
                          let dv = MDiv v'' v v'
                          in
                            return (v'', inscat j (inscat j' (Semi dv Nil)))


--
-- logical expressions
--
compile_expr (Not e)    = compile_expr e >>= \(v, j) ->
                          genreg >>= \v' ->
                          let ts  = MTst v' v
                          in
                            return (v', Semi ts Nil)

compile_expr (And e e') = compile_expr e >>= \(v, j) ->
                          compile_expr e' >>= \(v', j') ->
                          genreg >>= \v'' -> 
                          let an = MAnd v'' v v'
                          in
                            return (v'', inscat j (inscat j' (Semi an Nil)))


compile_expr (Or e e') = compile_expr e >>= \(v, j) ->
                         compile_expr e' >>= \(v', j') ->
                         genreg >>= \v'' -> 
                         let an = MOr v'' v v'
                         in
                           return (v'', inscat j (inscat j' (Semi an Nil)))

--
-- comparisons:
--
compile_expr (EqTest e e') = compile_expr e >>= \(v, j) ->
                             compile_expr e' >>= \(v', j') ->
                             genreg >>= \v'' ->
                             genreg >>= \v''' ->
                             let a1 = MCmp v'' v v'   -- compare v, v'
                                 a2 = MTst v''' v''   -- test diff for zero
                             in
                               return (v''', Semi a1 (Semi a2 Nil))

compile_expr (IneqTest e e') = compile_expr e >>= \(v, j) ->
                               compile_expr e' >>= \(v', j') ->
                               genreg >>= \v'' ->
                               let a1 = MCmp v'' v v'         -- cmp v'' v v'
                                   a2 = MTst v'' v''          -- tst v'' v''
                                   a3 = a2                    -- repeat tst
                               in
                                 return (v'',
                                   Semi a1 (Semi a2 (Semi a3 Nil)))

compile_expr (LTTest e e') = compile_expr e >>= \(v, j) ->
                             compile_expr e' >>= \(v', j') ->
                             genreg >>= \v'' ->
                             let a1 = MCmp v'' v v'         -- v'' := sgn(e-e')
                                 a2 = MCmpI v'' v'' ffff    -- cmp v'' (-1)
                                 a3 = MTst v'' v''          -- tst v''
                             in
                               return (v'', Semi a1 (Semi a2 (Semi a3 Nil)))

compile_expr (GTTest e e') = compile_expr e >>= \(v, j) ->
                             compile_expr e' >>= \(v', j') ->
                             genreg >>= \v'' ->
                             let a1 = MCmp v'' v v'         -- v'' := sgn(e-e')
                                 a2 = MCmpI v'' v'' one     -- cmp v'' 1
                                 a3 = MTst v'' v''          -- tst v''
                             in
                               return (v'', Semi a1 (Semi a2 (Semi a3 Nil)))

compile_expr (LTETest e e') = compile_expr (LTTest e e') >>= \(v, j) ->
                              compile_expr (EqTest e e') >>= \(v', j') ->
                              genreg >>= \v'' ->
                              let a1 = MOr v'' v v'         -- or v'' v v '
                              in
                                return (v'', Semi a1 Nil)

compile_expr (GTETest e e') = compile_expr e >>= \(v, j) ->
                              compile_expr e' >>= \(v', j') ->
                              genreg >>= \v'' ->
                              let a1 = MCmp v'' v v'         -- v'' := sgn(e-e')
                                  a2 = MCmpI v'' v'' one     -- cmp v'' 1
                              in
                                return (v'', Semi a1 (Semi a2 Nil))

compile_expr (SInt n)       = genreg >>= \v ->
                              let a0 = MovI v (Num n)
                              in
                                return (v, Semi a0 Nil)

compile_expr (SBool b)      = genreg >>= \v ->
                              case b of
                                False -> return (v, Semi (MovI v false) Nil)
                                True  -> return (v, Semi (MovI v true) Nil)

compile_expr Clear          = genreg >>= \v ->
                              return (v, Semi (MovI v zero) Nil)

--
-- compilation of compound references, e.g. multi-member structures
--
-- note that these correspond into references to LOCATIONS, as opposed
-- to references to the CONTENTS of a location
--
compile_ref :: Ref -> GS (VReg, InsSeq)

compile_ref (Var x) = genreg >>= \v ->
                      let a0 = MovI v (Adr x)
                      in
                        return (v, Semi a0 Nil)

compile_ref (LabelRef l) = genreg >>= \v ->
                           let a0 = MovI v (Adr l)
                           in
                             return (v, Semi a0 Nil)

compile_ref (Array x e)  = compile_expr e >>= \(v, j) ->
                           genreg >>= \v' ->
                           let a0 = MovI v (Adr x)
                               a1 = MAdd v' v' v     -- add the offset
                               j' = inscat j (Semi a0 (Semi a1 Nil))
                           in
                             return (v', j')

compile_ref (StructFld r f) = compile_ref r >>= \(v, j) ->
                              genreg >>= \v' ->
                              let a0 = MAddI v' v (SOffSet f)
                                  j' = inscat j (Semi a0 Nil)
                              in
                                return (v', j')

--
-- since we only need to an address, it is sufficient
-- just to give the starting address here; the details
-- of the footprint should be dealt with through the assignment.
--
-- implicit, of course, is the convention that all union references
-- are written beginning at the same starting address
--
-- (2010.11.01) Schulz
--
compile_ref (UnionFld r _) = compile_ref r

--
-- all of the following remain distinguished references:
--
compile_ref R_Ret = return (SReg R_Ret, Nil)
compile_ref R_Rti = return (SReg R_Rti, Nil)
compile_ref R_Nxt = return (SReg R_Nxt, Nil)
compile_ref R_Pro = return (SReg R_Pro, Nil)
compile_ref R_Req = return (SReg R_Req, Nil)
compile_ref R_Z   = return (SReg R_Z, Nil)
compile_ref IMR   = return (SReg IMR, Nil)
compile_ref INR   = return (SReg INR, Nil)


-- THIS IS THE END OF THE FILE --
