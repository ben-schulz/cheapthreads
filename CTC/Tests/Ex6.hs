monad R = ResT K
monad K = StateT(Int) Reg1 + StateT(Int) Reg2 + StateT(Int) Reg3

foo :: R ()
foo = stepR (getReg1K >>= \ x -> putReg1K (x+1))
