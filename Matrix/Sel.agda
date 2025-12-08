module Matrix.Sel where

open import Matrix
open import Matrix.Reshape

data Sel : Shape → Shape → Set where
  idh   : Sel s s
  view  : Sel s p → Reshape q s → Sel q p
  chain : Sel s p → Sel p q → Sel s q
  left  : Position p → Sel q s → Sel q (s ⊗ p)
  right : Position s → Sel q p → Sel q (s ⊗ p)

