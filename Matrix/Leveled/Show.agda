open import Matrix.Mon
open import Matrix.Mon.Show
open import Matrix.NatMon

open import Data.String
open import Data.Nat
open import Data.Fin hiding (fold)

--module Matrix.Leveled.Show (M : Mon) (MS : MonShow M) (C : Set) (ShowC : C → String) where
--open Mon M
--open MonShow MS

open import Matrix.Leveled.Base ℕ-Mon

module Matrix.Leveled.Show (C : Set) (ShowC : C → String) where
private variable  
  X Y : Set
  ℓ : L
  s : S ℓ
  u n : ℕ

head₁  : Ar (ν (suc n)) X → X
head₁ xs = xs (ν zero)

tail₁ : Ar (ν (suc n)) X → Ar (ν n) X
tail₁ xs (ν x) = xs (ν (suc x))

fold : (X → Y → Y) → Y → Ar (ν u) X → Y
fold {X} {Y} {zero} f acc xs = f (xs (ν zero)) acc
fold {X} {Y} {suc u} f acc xs = f (head₁ xs) (fold f acc (tail₁ xs))

showAr : Ar (ν (suc u)) C → String
showAr xs = fold (λ x acc → acc ++ "," <+> ShowC x) (ShowC (head₁ xs)) (tail₁ xs)

