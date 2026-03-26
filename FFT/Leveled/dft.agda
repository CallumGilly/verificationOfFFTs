open import ComplexNew

module FFT.Leveled.dft (cplx : Cplx) where


open Cplx cplx
open import Matrix.Mon
open import Matrix.NatMon
open import Matrix.Leveled ℕ-Mon
open Mon ℕ-Mon
open import FFT.Leveled.Specification cplx ℕ-Mon Leveled-CM
open import FFT.Leveled.FFT cplx ℕ-Mon
--open CM Leveled-CM
open import Data.Fin hiding (_+_; pred)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
{-

  iota : Ar (ι N) ℕ
  iota (ι i) = toℕ i

  offset-prod : Position (s ⊗ p) → ℕ
  offset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  twiddles′ : ℕ → Position s → Position p → ℂ
  twiddles′ n i j = -ω (suc n) ⦃ record { nonZero = tt } ⦄ (offset-prod (i ⊗ j))

  twiddles : Ar (s ⊗ p) ℂ
  twiddles {s} {p} i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (¬nz (pos⇒nz i))
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (offset-prod i)

  -------------------
  --- DFT and FFT ---
  -------------------

  DFT′ : ∀ {N} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT′ {N} xs with nonZero? N
  ... | no ¬nz = λ { (ι j) → ⊥-elim (¬nz (fin-nz _ j)) }
  DFT′ {suc N} xs | yes nz = λ j → sum (λ k → xs k * twiddles′ N j k)

  DFT : ∀ {N} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} xs with nonZero? N
  ... | no ¬nz = λ { (ι j) → ⊥-elim (¬nz (fin-nz _ j)) }
  ... | yes nz = λ j → sum (λ k → xs k * -ω N ⦃ nz ⦄ (iota k *ₙ iota j))
-}
open import Data.Nat renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties

{-
head₁ : Ar (ι (suc n)) X → X
head₁ ar = ar (ι fzero)

tail₁ : Ar (ι (suc n)) X → Ar (ι n) X
tail₁ ar (ι x) = ar (ι (fsuc x))
-}
private
  variable
    l : L
    n : U
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

sum : ∀ {n : U} → Ar (ν n) ℂ → ℂ
sum {zero} xs = xs (ν zero)
sum {suc n} xs = head₁ xs + (sum (tail₁ xs))

-- Be careful here, given i : Fin ∘ suc
iota : ∀ {n : U} → Ar (ι (ν n)) ℕ
iota (ι (ν x)) = toℕ x

twiddles : ∀ {l : L} → ∀ {s p : S (ss l)} → ℕ → P s → P p → ℂ
twiddles {l} {s} {p} n i j = -ω n ((iota (i ⟨ rev u-flattenᵣ ⟩)) *ₙ (iota (j ⟨ rev u-flattenᵣ ⟩)))

size : ∀ {l : L} → S l → ℕ
size (ν x) = x
size (ι x) = size x
size (x₁ ⊗ x₂) = size x₁ *ₙ size x₂

std-twiddles : ∀ {l : L} → ∀ {s p : S (ss l)} → P s → P p → ℂ
std-twiddles {_} {s} {p} i j = twiddles (size s *ₙ size p) i j

dft : {n : U} →
      Ar (ι (ν n)) ℂ →
      Ar (ι (ν n)) ℂ
dft {n} xs (ι j) = sum (λ k → xs (ι k) * twiddles n (ι k) (ι j))

dftffttmp : {s
             : S (ss zz)}
            (xs : Ar s ℂ) (i : P s) →
            dft (reshape u-flattenᵣ xs) (i ⟨ rev u-flattenᵣ ⟩)
            ≡
            reshape (change-majorᵣ )
            (fft
             (dft) (std-twiddles) xs)
            i
dftffttmp {ι (ν x)} xs (ι (ν i)) = refl
dftffttmp {s ⊗ s₁} xs (i ⊗ i₁) = ?

ℕ-dft : FFT-Specification
ℕ-dft = record 
      { dft = dft
      ; dft-cong = ?
      ; twiddles = std-twiddles
      ; dft≡fft = dftffttmp
      }
