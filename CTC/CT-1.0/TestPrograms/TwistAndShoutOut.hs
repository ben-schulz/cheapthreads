ast__foo_txt = 

CTFixIN
   (CTLamIN "tw"
      (CTLamIN "phi"
         (CTLamIN "gamma"
            (CTCaseIN
               (CTPairIN
                  (CTVarIN "phi" (CTMTy ResTy CTUnitTy))
                  (CTVarIN "gamma" (CTMTy ResTy CTUnitTy))
                  (CTPairTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))
               )
               [(PTuple (PPause (PVar "x")) Wildcard,
                 CTBindIN
                   (CTStepIN
                      (CTVarIN "x" (CTMTy StateTy (CTMTy ResTy CTUnitTy)))
                      (CTMTy ResTy (CTMTy ResTy CTUnitTy))
                   )
                   (CTLamIN "k"
                      (CTAppIN
                         (CTAppIN
                            (CTVarIN "tw"
                               (CTAbsTy
                                  (CTMTy ResTy CTUnitTy)
                                  (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))
                               )
                            )
                            (CTVarIN "gamma" (CTMTy ResTy CTUnitTy))
                            (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))
                         )
                         (CTVarIN "k" (CTMTy ResTy CTUnitTy))
                         (CTMTy ResTy CTUnitTy)
                      )
                      (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))
                   )
                   (CTMTy ResTy CTUnitTy)
                ),
                (PTuple (PDone Wildcard) (PVar "y"),CTVarIN "y" (CTMTy ResTy CTUnitTy)),
                (PTuple (PVar "x") (PDone Wildcard),CTVarIN "x" (CTMTy ResTy CTUnitTy))
               ]
               (CTMTy ResTy CTUnitTy)
            )
            (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))
         )(CTAbsTy (CTMTy ResTy CTUnitTy) (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy)))) (CTAbsTy (CTAbsTy (CTMTy ResTy CTUnitTy) (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))) (CTAbsTy (CTMTy ResTy CTUnitTy) (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy))))) [] (CTAbsTy (CTMTy ResTy CTUnitTy) (CTAbsTy (CTMTy ResTy CTUnitTy) (CTMTy ResTy CTUnitTy)))

