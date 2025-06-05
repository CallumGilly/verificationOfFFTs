open import src.Real.Base using (RealBase)
open import src.Real.Properties using (RealProperties)

module src.Real (realBase : RealBase) (realProperties : RealProperties realBase) where
  open RealBase realBase public
  open RealProperties realProperties public
