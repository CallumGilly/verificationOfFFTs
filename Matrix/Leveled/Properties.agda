open import Matrix.Mon
module Matrix.Leveled.Properties (M : Mon) where
open Mon M

open import Matrix.Leveled.Base M 
open import Matrix.Leveled.Reshape M

open import Relation.Binary.PropositionalEquality

private variable
  n : U
  ℓ : L

--iota : ∀ {n : U} → Ar (ι (ν n)) U
--iota (ι (ν x)) = toU x

iota-resh : ∀ {n : U} 
          → ∀ (r : Reshape (ι (ν n)) (ι (ν n)))
          → ∀ (i : P (ι (ν n)))
          → iota i ≡ iota (i ⟨ r ⟩)
iota-resh eq i = refl
iota-resh (_∙_ {p = p} r r₁) i = ?
iota-resh (up r) i = ?
iota-resh (down r) i = ?
