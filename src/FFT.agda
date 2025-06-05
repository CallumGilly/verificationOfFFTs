open import src.Real.Base using (RealBase)
open import src.Complex.Base using (CplxBase)

module src.FFT (realBase : RealBase) (cplxBase : CplxBase realBase) where
open CplxBase cplxBase using (ℂ; _*_; -ω; ℂfromℕ; e^i_)
open import src.DFTMatrix realBase cplxBase using (DFT)

open import Function using (_$_; _∘_)

open import Data.Fin.Base using (Fin; toℕ; opposite) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open RealBase realBase renaming (_*_ to _*ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_)

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length)
open import src.Reshape using (Reshape; transpose; transposeᵣ; rev; recursive-transposeᵣ; recursive-transpose; reshape; flat; _∙_; swap; _⟨_⟩; _♯; _⊕_; eq)



offset : ∀ {s : Shape} → Position s → Position (ι (length s))
offset i = i ⟨ _♯ ⟩

offset-n : ∀ {s : Shape} → Position s → ℕ
offset-n i with offset i
... | ι x = toℕ x

-- This has to do some weird stuff I dont like to get the correct value as Fin seems to be reversed :Puzzled_face:
position-sum : ∀ {s r : Shape} → Position (s ⊗ r) → ℕ
position-sum {s} {r} (i ⊗ j) = offset-n i *ₙ offset-n j
-- position-sum {ι (suc n)} (ι fzero) = 0
-- position-sum {ι (suc n)} (ι (fsuc pos)) = (position-sum {ι (n)} (ι pos)) +ₙ 1
-- position-sum {ι (suc n)} (ι (fsuc pos)) = (toℕ ((fsuc pos))) +ₙ 1 -- THIS BROKE THE ENTIRE PROGRAM AGGGGG
-- position-sum {ι (suc n)} (ι pos) = toℕ pos
-- position-sum {sₗ ⊗ sᵣ} (xₗ ⊗ xᵣ) = (position-sum {sₗ} xₗ) *ₙ (position-sum {sᵣ} xᵣ)

twiddles : ∀ {s r : Shape} → Ar (s ⊗ r) ℂ
twiddles {s} {r} p = -ω (length (s ⊗ r)) (position-sum p)


--Wv-gen {s} {p} (i ⊗ j) = W^ (S-prod s ℕ.* S-prod p) (R.fromℕ $ offset-n i ℕ.* offset-n j)

FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT (reshape swap arr) in
                     let twiddleFactorsApplied = zipWith _*_   (reshape swap innerDFTapplied) twiddles in
                     let outerDFTapplied       = nestedMap FFT $ twiddleFactorsApplied in
                     reshape swap outerDFTapplied


-- Working
-- FFT : ∀ {s : Shape} → Ar s ℂ → Ar s ℂ
-- FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
-- FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT arr in
--                      let twiddleFactorsApplied = zipWith _*_  innerDFTapplied twiddles in
--                      let outerDFTapplied       = nestedMap FFT $ reshape swap twiddleFactorsApplied in
--                      reshape swap outerDFTapplied
                     
-- FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
-- FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
-- FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT (reshape swap arr) in
--                      let twiddleFactorsApplied = zipWith _*_   (reshape swap innerDFTapplied) twiddles in
--                      let outerDFTapplied       = nestedMap FFT $ twiddleFactorsApplied in
--                      reshape swap outerDFTapplied
