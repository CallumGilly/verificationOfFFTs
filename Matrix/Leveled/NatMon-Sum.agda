open import ComplexNew

module Matrix.Leveled.NatMon-Sum (cplx : Cplx) where
open Cplx cplx
open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon

open import Data.Nat hiding (_+_)
open import Data.Fin hiding (_+_)

private variable
  n : ℕ
  X : Set

{- 
I could define sum via foldr
I should defined sum via foldr
I have previously had issues defining sum via foldr
So I will use this for now, but may have to make an ↔ relation with foldr sum
-}
head₁  : Ar (ν (suc n)) X → X
head₁ xs = xs (ν zero)

tail₁ : Ar (ν (suc n)) X → Ar (ν n) X
tail₁ xs (ν x) = xs (ν (suc x))

sum : ∀ {n : ℕ} → Ar (ν n) ℂ → ℂ
sum {zero} xs = xs (ν zero)
sum {suc n} xs = head₁ xs + (sum (tail₁ xs))
