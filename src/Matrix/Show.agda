module src.Matrix.Show where

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; foldr; nest; map; head₁; tail₁)
open import Agda.Builtin.String using (String; primStringAppend; primShowString)
open import Data.Nat using (ℕ) 
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (opposite)
open import Agda.Builtin.Nat using (suc; zero)

-- Makes shit less ugly
_++_ : String → String → String
_++_ = primStringAppend

id : String → String
id x = x

flipArr : ∀ {n : ℕ} {X : Set} → Ar (ι n) X → Ar (ι n) X
flipArr arr (ι x) = arr (ι (opposite x))

show : ∀ {s : Shape} {X : Set} → (X → String) →  Ar s X → String
-- This does the classic thing of ending with a comma, but like......
show {ι zero} showElem arr = "[" ++ "]"
show {ι (suc x)} showElem arr = "[" ++ ((foldr (λ elem → (", " ++ (("(" ++ (showElem elem)) ++ ")")) ++_) "" (flipArr arr)) ++ "]")
show {s ⊗ s₁} showElem arr = show id (map (show showElem) (nest arr))

showShape : ∀ {s : Shape} → String
showShape {ι x} = "ι " ++ (showNat x) 
showShape {s ⊗ s₁} = "[" ++ ((showShape {s}) ++ ("] ⊗ [" ++ ((showShape {s₁}) ++ "]")))
