module Matrix.Show where

open import Matrix using (Ar; Shape; Position; ι; _⊗_; foldr; nest; map; head₁; tail₁)
open import Matrix.Reshape
open import Agda.Builtin.String using (String; primStringAppend; primShowString)
open import Data.Nat using (ℕ) 
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (opposite)
open import Agda.Builtin.Nat using (suc; zero)

open import Function.Base using (_$_; _∘_)

private
  infixl 4 _++_
  _++_ : String → String → String
  _++_ = primStringAppend

id : String → String
id x = x

flipArr : ∀ {n : ℕ} {X : Set} → Ar (ι n) X → Ar (ι n) X
flipArr arr (ι x) = arr (ι (opposite x))

showShape : ∀ {s : Shape} → String
showShape {ι x} = "ι " ++ (showNat x) 
showShape {s ⊗ s₁} = "[" ++ ((showShape {s}) ++ ("] ⊗ [" ++ ((showShape {s₁}) ++ "]")))

show : ∀ {s : Shape} {X : Set} → (X → String) →  Ar s X → String
-- This does the classic thing of ending with a comma, but like......
show {ι zero   } showElem arr = "[" ++ "]"
show {ι (suc x)} showElem arr = 
    "[" 
  ++ (foldr 
        (λ elem → _++ (", " ++ "(" ++ (showElem elem) ++ ")"))
        ("(" ++ (showElem $ head₁ arr) ++ ")")
        (tail₁ arr)
     ) 
  ++ "]"
show {s ⊗ s₁} showElem arr = show id (map (show showElem) (nest arr))

private
  variable
    AR-Count n : ℕ
    X : Set

showRow : (X → String) → Ar (ι AR-Count) X → String
showRow {_} {zero} showX xs = ""
showRow {_} {suc AR-Count} showX xs = foldr (λ elem → _++ (", " ++ showX elem)) (showX $ head₁ xs) (tail₁ xs)

showCSV : (X → String) → Ar (ι AR-Count) String → Ar (ι AR-Count ⊗ ι n) X → String
showCSV showX header = foldr (λ row → _++ (showRow showX row ++ "\n")) ((showRow id header) ++ "\n") ∘ (nest ∘ reshape swap)

