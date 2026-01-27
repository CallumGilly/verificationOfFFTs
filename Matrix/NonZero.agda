module Matrix.NonZero where
open import Data.Fin using (Fin)
open import Data.Nat.Base using (ℕ; NonZero; nonZero; suc; zero)
open import Data.Nat.Properties using (m*n≢0; m*n≢0⇒n≢0; m*n≢0⇒m≢0)
open import Matrix
open import Matrix.Reshape using (recursive-transpose)
open import Relation.Nullary
open import Data.Empty
open import Function.Base using (_$_)
open import Agda.Builtin.Unit using (tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)

--- Shorthands for length and recursive transpose, and variables, for use in this file only
private
  variable
    N : ℕ
    s p : Shape

  infix 10 #_
  #_ : Shape → ℕ
  #_ = length 

  infix 11 _ᵗ
  _ᵗ : Shape → Shape
  _ᵗ = recursive-transpose

---------------------------------------
--- NonZero properties of matricies ---
---------------------------------------

data NonZeroₛ : Shape → Set where
  ι   : NonZero  N →              NonZeroₛ (ι N)
  _⊗_ : NonZeroₛ s → NonZeroₛ p → NonZeroₛ (s ⊗ p)

-------------------------------------
--- Decidable funciton on NonZero ---
-------------------------------------

nonZeroDec : ∀ s → Dec (NonZeroₛ s)
nonZeroDec (ι zero) = no λ { (ι ()) }
nonZeroDec (ι (suc x)) = yes (ι _)
nonZeroDec (s ⊗ p) with nonZeroDec s | nonZeroDec p 
... | yes  ds | yes  dp = yes ( ds ⊗ dp )
... | yes _   | no  ¬dp = no (λ { (_  ⊗ dp) → ¬dp dp })
... | no  ¬ds | _       = no (λ { (ds ⊗ _ ) → ¬ds ds })

--------------------------
--- Basic Length Rules ---
--------------------------

nonZeroₛ-s⇒nonZero-s : NonZeroₛ s → NonZero (# s)
nonZeroₛ-s⇒nonZero-s (ι nonZero-|s|) = nonZero-|s|
nonZeroₛ-s⇒nonZero-s {s ⊗ p} (nonZeroₛ-s ⊗ nonZeroₛ-p) with nonZeroₛ-s⇒nonZero-s nonZeroₛ-s | nonZeroₛ-s⇒nonZero-s nonZeroₛ-p 
... | nonZeroₛ-#s | nonZeroₛ-#p = m*n≢0 (# s) (# p) ⦃ nonZeroₛ-#s ⦄ ⦃ nonZeroₛ-#p ⦄

nonZero-s⇒nonZeroₛ-s : NonZero (# s) → NonZeroₛ s
nonZero-s⇒nonZeroₛ-s {ι N  } nz-#s   = ι nz-#s
nonZero-s⇒nonZeroₛ-s {s ⊗ p} nz-#s⊗p = 
    (nonZero-s⇒nonZeroₛ-s (m*n≢0⇒m≢0 (# s) ⦃ nz-#s⊗p ⦄ )) 
  ⊗ 
    (nonZero-s⇒nonZeroₛ-s (m*n≢0⇒n≢0 (# s) ⦃ nz-#s⊗p ⦄ ))

---------------------------------
--- Basic Transposition Rules ---
---------------------------------

nonZeroₛ-s⇒nonZeroₛ-sᵗ : NonZeroₛ s → NonZeroₛ (s ᵗ)
nonZeroₛ-s⇒nonZeroₛ-sᵗ {s} (ι nz-N) = ι nz-N
nonZeroₛ-s⇒nonZeroₛ-sᵗ {s} (nz-s ⊗ nz-p) = 
    ( nonZeroₛ-s⇒nonZeroₛ-sᵗ nz-p ) 
  ⊗ 
    ( nonZeroₛ-s⇒nonZeroₛ-sᵗ nz-s )

nonZeroₛ-sᵗ⇒nonZeroₛ-s : NonZeroₛ (s ᵗ) → NonZeroₛ s
nonZeroₛ-sᵗ⇒nonZeroₛ-s {ι N} (ι nz-N) = ι nz-N
nonZeroₛ-sᵗ⇒nonZeroₛ-s {s ⊗ p} (nz-sᵗ ⊗ nz-pᵗ) = 
    (nonZeroₛ-sᵗ⇒nonZeroₛ-s nz-pᵗ) 
  ⊗ 
    (nonZeroₛ-sᵗ⇒nonZeroₛ-s nz-sᵗ)

-----------------------------------
--- Transpositon × Length Rules ---
-----------------------------------

nonZeroₛ-s⇒nonZero-sᵗ : NonZeroₛ s → NonZero (# s ᵗ)
nonZeroₛ-s⇒nonZero-sᵗ (ι nz-N) = nz-N
nonZeroₛ-s⇒nonZero-sᵗ {s ⊗ p} (nz-s ⊗ nz-p) 
  = m*n≢0 
      (# p ᵗ) 
      (# s ᵗ) 
      ⦃ nonZeroₛ-s⇒nonZero-sᵗ nz-p ⦄ 
      ⦃ nonZeroₛ-s⇒nonZero-sᵗ nz-s ⦄

¬nonZeroₛ-s⇒¬nonZero-sᵗ : ¬ NonZeroₛ s → ¬ NonZero (# s ᵗ)
¬nonZeroₛ-s⇒¬nonZero-sᵗ ¬nz-s nz-#sᵗ = ¬nz-s (nonZeroₛ-sᵗ⇒nonZeroₛ-s (nonZero-s⇒nonZeroₛ-s nz-#sᵗ))


nonZero-s⇒nonZero-sᵗ : NonZero (# s) → NonZero (# s ᵗ)
nonZero-s⇒nonZero-sᵗ {ι N} nz-#sᵗ = nz-#sᵗ
nonZero-s⇒nonZero-sᵗ {s ⊗ p} nz-#sᵗ 
  = m*n≢0 
      (# p ᵗ)
      (# s ᵗ)
      ⦃ nonZero-s⇒nonZero-sᵗ {p} (m*n≢0⇒n≢0 (length s) ⦃ nz-#sᵗ ⦄) ⦄ 
      ⦃ nonZero-s⇒nonZero-sᵗ {s} (m*n≢0⇒m≢0 (length s) ⦃ nz-#sᵗ ⦄) ⦄ 

¬nonZero-sᵗ⇒¬nonZero-s : ¬ NonZero (# s ᵗ) → ¬ NonZero (# s)
¬nonZero-sᵗ⇒¬nonZero-s {ι N} ¬nz-#sᵗ nz-#s = ¬nz-#sᵗ nz-#s
¬nonZero-sᵗ⇒¬nonZero-s {s ⊗ p} ¬nz-#sᵗ nz-#s = ¬nz-#sᵗ 
  $ m*n≢0 
      (# p ᵗ) 
      (# s ᵗ) 
      ⦃ nonZero-s⇒nonZero-sᵗ { p } (m*n≢0⇒n≢0 (length s) ⦃ nz-#s ⦄) ⦄ 
      ⦃ nonZero-s⇒nonZero-sᵗ { s } (m*n≢0⇒m≢0 (length s) ⦃ nz-#s ⦄) ⦄ 


¬nonZero-N⇒N≡0 : ∀ N → ¬ NonZero N → N ≡ 0
¬nonZero-N⇒N≡0 zero    ¬nz-N = refl
¬nonZero-N⇒N≡0 (suc N) ¬nz-N = ⊥-elim (¬nz-N (nonZero {N}))

Fin0⇒⊥ : Fin 0 → ⊥
Fin0⇒⊥ ()

¬nonZero-N⇒FinN-irrelevant : ¬ NonZero N → (i j : Fin N) → i ≡ j
¬nonZero-N⇒FinN-irrelevant {N} nz-N i j rewrite ¬nonZero-N⇒N≡0 N nz-N = ⊥-elim (Fin0⇒⊥ i)

¬nonZero-N⇒PosN-irrelevant : ¬ NonZero N → ∀ (i j : Position (ι N)) → i ≡ j
¬nonZero-N⇒PosN-irrelevant ¬nz-N (ι i) (ι j) = cong ι (¬nonZero-N⇒FinN-irrelevant ¬nz-N i j)

nz≡nzₛ : ∀ {n : ℕ} → ∀ (nz-n : NonZero n) → ∀ (nzₛ-n : NonZeroₛ (ι n)) → (ι nz-n) ≡ nzₛ-n
nz≡nzₛ {suc n} nz-n (ι x) = refl

nz≡nz : ∀ {n : ℕ} → ∀ (nz-a nz-b : NonZero n) → nz-a ≡ nz-b
nz≡nz {suc n} record { nonZero = tt } record { nonZero = tt } = refl

nzₛ≡nzₛ : ∀ {s : Shape} → ∀ (nz-a nz-b : NonZeroₛ s) → nz-a ≡ nz-b
nzₛ≡nzₛ (ι a) (ι b) = cong ι (nz≡nz a b)
nzₛ≡nzₛ (nz-a₁ ⊗ nz-a₂) (nz-b₁ ⊗ nz-b₂) = cong₂ _⊗_ (nzₛ≡nzₛ nz-a₁ nz-b₁) (nzₛ≡nzₛ nz-a₂ nz-b₂)

  
