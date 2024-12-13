module src.MatrixShow where

open import src.Matrix using (Ar; Shape; ι; _⊗_; foldr; nest; map; head₁; tail₁)
open import Agda.Builtin.String using (String; primStringAppend; primShowString)
open import Agda.Builtin.Nat using (suc; zero)

-- Makes shit less ugly
_++_ : String → String → String
_++_ = primStringAppend

id : String → String
id x = x

show : ∀ {s : Shape} {X : Set} → (X → String) →  Ar s X → String
-- This does the classic thing of ending with a comma, but like......
show {ι zero} showElem arr = "[" ++ "]"
show {ι (suc x)} showElem arr = (("[" ++ ("(" ++ ((showElem (head₁ arr)) ++ ")")) ) ++ (foldr (λ elem → (", " ++ (("(" ++ (showElem elem)) ++ ")")) ++_) "" (tail₁ arr))) ++ "]"
show {s ⊗ s₁} showElem arr = show id (map (show showElem) (nest arr))
