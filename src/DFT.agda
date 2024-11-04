open import src.Vector using (Vec; foldr; zip; iterate)
open import src.Real using (Real)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

module src.DFT (r : Real) where
  open Real r using (ℝ; -ᵣ_; _/ᵣ_; _*ᵣ_; π; _ᵣ)
  open import src.Complex r using (ℂ; ℂfromℕ; _+_; _*_;e^i_)
  
  -- Todo: move this syntax sugar to somewhere that isn't here
  _ₙ/ᵣ_ : ℕ → ℕ → ℝ
  _ₙ/ᵣ_ num den = (num ᵣ) /ᵣ (den ᵣ)

  -- May need checks on division exluding zero

  DFT : ∀ {N : ℕ} → Vec ℂ N → Vec ℂ N
  DFT {N} xs k = foldr (step (toℕ k)) (ℂfromℕ 0) (zip xs posVec)
    where
      step : ℕ → (ℂ × ℕ) → ℂ → ℂ
      step k ⟨ xₙ , n ⟩ acc = acc + (xₙ * e^i (-ᵣ 2 ᵣ *ᵣ π *ᵣ n ᵣ *ᵣ (k ₙ/ᵣ N)))

      posVec : Vec ℕ N
      posVec = iterate N suc 0
  
  -- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
