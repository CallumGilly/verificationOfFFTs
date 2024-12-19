open import src.Real using (Real)

module src.FFT (r : Real) where

open import Function using (_$_)

open import Data.Fin.Base using (Fin; toℕ; opposite) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open Real r renaming (_*_ to _*ᵣ_)
open import src.Complex r using (ℂ; _*_; ω)

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap)
open import src.Reshape using (Reshape; transposeᵣ; recursive-transpose; reshape)

open import src.DFTMatrix r using (DFT)


twiddles : ∀ {s : Shape} → Ar s ℂ
twiddles {s} p = ω (base s) (position-sum p)
  where
    -- This has to do some weird stuff I dont like to get the correct value as Fin seems to be reversed :Puzzled_face:
    position-sum : ∀ {s : Shape} → Position s → ℕ
    position-sum {ι (suc n)} (ι fzero) = 0
    position-sum {ι (suc n)} (ι (fsuc pos)) = (toℕ (opposite (fsuc pos))) +ₙ 1
    position-sum {sₗ ⊗ sᵣ} (xₗ ⊗ xᵣ) = (position-sum {sₗ} xₗ) *ₙ (position-sum {sᵣ} xᵣ)

    -- Base of the omega value
    base : Shape → ℕ
    base (ι x) = x
    base (s ⊗ s₁) = base s *ₙ base s₁

    

FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT arr in
                     let twiddleFactorsApplied = zipWith _*_ innerDFTapplied twiddles in
                     nestedMap FFT $ reshape transposeᵣ twiddleFactorsApplied

