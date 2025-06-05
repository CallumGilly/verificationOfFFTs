open import src.Real using (Real)
open import src.Complex.Base using (CplxBase)
open import src.Complex.Properties using (CplxProperties)

module src.Complex (r : Real) (c : CplxBase r) (cProperties : CplxProperties r c) where
  open CplxBase c public
  open CplxProperties cProperties public
