module SimpleKernel where

type System = ([(R ())])

sched :: System -> R ()
sched (p:ps) = case p of
                (Done _ )   -> sched ps
                (Pause x)  -> sched $ ps ++ [(step x)]