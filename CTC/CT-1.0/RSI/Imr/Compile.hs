--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/RSI_Inr/Compile.hs
--
-- Implementation of RSI using an abstracted interrupt mask register;
--
-- put here 2010.10.08
--
-- Schulz
--

module RSI.Imr.Compile where

import RSI.Syntax

import CT.Syntax
import CT.INAST

import CT.MonadicConstructions

import CT.PPT


--                --
-- TOP-LEVEL CALL --
--                --

imr_pass :: RSI -> RSI_B
imr_pass (RSI (d, (l, cs))) = (RSI_B (d, (l, map compile_imr cs)))


--                     --
-- MAIN TRANSFORMATION --
--                     --
compile_imr :: Code -> Code_B

--
-- all imperative code is invariant under this transformation:
--
compile_imr (K l b) = K_B l b

--
-- reifications to the control flow primitives:
--
compile_imr (R l r) = R_B l (compile_imr' r)


compile_imr' :: Chain -> Chain_B
compile_imr' r =

  case r of

    (Seq (Atom l k) c) ->  let k' = asmcat (FBy (Clr IMR) k) (FBy (Set IMR) End)
                               a' = Block l k'
                           in
                             Seq_B a' (compile_imr' c)


    (Seq (Throw l k) c) -> let l0 = l ++ thrmsk_label
                               l1 = l
                               l2 = l ++ brterm_label

                               k' = asmcat (FBy (Clr IMR) k) (FBy (Set IMR) End)

                               b2 = Seq_B (Block l2 (FBy NOP End))
                                      (Halt_B (l2 ++ halt_label))

                               b1 = Seq_B (Block l1 k')
                                      (Halt_B (l1 ++ halt_label))
                           in
                             BZ_B l0 (DeRef INR) b1 b2  (compile_imr' c)
                             
                           

    (BZ_R l v c c' t)   -> let l0 = l ++ brinit_label
                               l1 = l ++ brtrue_label
                               l2 = l ++ brflse_label
                               l3 = l ++ brterm_label

                               b1 = Block l1
                                      (FBy
                                        (Assign R_Nxt
                                          (DeRef (LabelRef (startof c))))
                                        End)

                               b2 = Block l2
                                      (FBy
                                        (Assign R_Nxt
                                          (DeRef (LabelRef (startof c'))))
                                        End)

                               b3 = Block l3 (FBy (Set IMR) End)

                               b0 = Block l0
                                      (FBy
                                        (Clr IMR)
                                      (FBy
                                        (Tst v)

                                      (BZ_K (DeRef R_Z) b1 b2 b3)))

                           in
                             LabelPt_B l (Seq_B b0
                              (Jmp_B (l ++ nxt_label) R_Nxt (compile_imr' t)))


    (Loop l c c')       -> Loop_B l (compile_imr' c) (compile_imr' c')

    (Break l v)         -> Break_B l v

    (Swr l x c)         -> let ent = FBy (Clr IMR) (FBy (Set INR) End)

                               ret = FBy (Clr INR)
                                       (FBy (Assign R_Ret (DeRef R_Nxt))
                                         (FBy (Assign R_Nxt
                                           (DeRef (LabelRef (startof c)))) End))
                               
                               b   = Block (l ++ swrent_label) ent
                               b'  = Block (l ++ swrret_label) ret

                           in
                             Seq_B b
                               (Swr_B l x (Seq_B b' (compile_imr' c)))


    (Swt l x c)         -> compile_imr' (Swr l x c)  -- 'swt', 'swr' identical 


    (Catch l x c)       -> let xbn = Assign x (DeRef R_Ret)
                               b   = Block l (FBy (Clr IMR) (FBy xbn End))
                           in
                             Seq_B b (compile_imr' c)

    (Jmp l x c)         -> Jmp_B l x (compile_imr' c)

    (LabelPt l c)       -> LabelPt_B l (compile_imr' c)

    (Halt l)            -> Halt_B l



--
-- labeling conventions:
--
thrmsk_label :: String
thrmsk_label = "__MASK"

brterm_label :: String
brterm_label = "__TERM"

brinit_label :: String
brinit_label = "__GUARD"

brtrue_label :: String
brtrue_label = "__NOTZERO"

brflse_label :: String
brflse_label = "__ZERO"

swrent_label :: String
swrent_label = "__SWITCH_ENT"

swrret_label :: String
swrret_label = "__SWITCH_RET"

halt_label :: String
halt_label = "__HALT"

nxt_label :: String
nxt_label = "__NXT"

-- THIS IS THE END OF THE FILE --
