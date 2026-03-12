open import Complex

module FFT.Leveled.dft (cplx : Cplx) where


open Cplx cplx
open import Matrix.Mon
open import Matrix.NatMon
open import Matrix.Leveled ℕ-Mon
open Mon ℕ-Mon
open import FFT.Leveled.Specification cplx ℕ-Mon Leveled-CM

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
open import Data.Nat

dft : {n : U} →
      Ar (ν n) ℂ →
      Ar (ν n) ℂ

ℕ-dft : FFT-Specification
ℕ-dft = record 
      { dft = ?
      ; dft-cong = ?
      ; twiddles = ?
      ; dft≡fft = ?
      }
