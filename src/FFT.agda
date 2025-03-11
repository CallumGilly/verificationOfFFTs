open import src.Real using (Real)

module src.FFT (r : Real) where

open import Function using (_$_)

open import Data.Fin.Base using (Fin; toℕ; opposite) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open Real r renaming (_*_ to _*ᵣ_)
open import src.Complex r using (ℂ; _*_; -ω; ℂfromℕ)

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length)
open import src.Reshape using (Reshape; transposeᵣ; recursive-transpose; reshape; flat; _∙_)

open import src.DFTMatrix r using (DFT)


-- This has to do some weird stuff I dont like to get the correct value as Fin seems to be reversed :Puzzled_face:
position-sum : ∀ {s : Shape} → Position s → ℕ
position-sum {ι (suc n)} (ι fzero) = 0
position-sum {ι (suc n)} (ι (fsuc pos)) = (position-sum {ι (n)} (ι pos)) +ₙ 1
-- position-sum {ι (suc n)} (ι (fsuc pos)) = (toℕ ((fsuc pos))) +ₙ 1 -- THIS BROKE THE ENTIRE PROGRAM AGGGGG
position-sum {sₗ ⊗ sᵣ} (xₗ ⊗ xᵣ) = (position-sum {sₗ} xₗ) *ₙ (position-sum {sᵣ} xᵣ)

twiddles : ∀ {s : Shape} → Ar s ℂ
twiddles {s} p = -ω (length s) (position-sum p)

tmp : Shape → Shape
tmp (ι x) = ι x
tmp (x ⊗ x₁) = x ⊗ tmp x₁
    
FFT₁ : ∀ {s : Shape} → Ar s ℂ → Ar (ι (length s)) ℂ
FFT₁ {ι x} arr = DFT arr
FFT₁ {s ⊗ s₁} arr = let innerDFTapplied       = nestedMap FFT₁ arr in
                    let twiddleFactorsApplied = zipWith _*_ innerDFTapplied twiddles in
                    let outerDFTapplied = nestedMap FFT₁ $ reshape transposeᵣ twiddleFactorsApplied in
                    reshape (flat ∙ transposeᵣ) outerDFTapplied

----------------------------------
-- THIS BELOW IS WRONG!!: :( :( --
----------------------------------
FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT arr in
                     let twiddleFactorsApplied = zipWith _*_ innerDFTapplied twiddles in
                     let outerDFTapplied = nestedMap FFT $ reshape transposeᵣ twiddleFactorsApplied in
                     outerDFTapplied
