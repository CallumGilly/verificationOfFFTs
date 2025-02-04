open import src.Real using (Real)
open import src.Matrix using (Ar; ι; foldr; zip; iterate)
open import Data.Nat.Base using (ℕ; suc) renaming (_*_ to _*ₙ_)
open import Data.Fin.Base using (toℕ)
open import Data.Product.Base using (_×_) renaming ( _,_ to ⟨_,_⟩)

-- Definition of DFT using retricted matrices instead of Vectors
module src.DFTMatrix (r : Real) where
  open import src.Complex r using (ℂ; ℂfromℕ; _+_; _*_; -ω)
  
  -- May need checks on division exluding zero
  DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} xs (ι k) = foldr (step (toℕ k)) (ℂfromℕ 0) (zip xs posVec)
    where
      step : ℕ → (ℂ × ℕ) → ℂ → ℂ
      step k ⟨ xₙ , n ⟩ acc = acc + (xₙ * (-ω N (n *ₙ k)))

      posVec : Ar (ι N) ℕ
      posVec = iterate N suc 0

  -- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
