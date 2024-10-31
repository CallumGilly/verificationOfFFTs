open import src.vector using (Vec; foldr; zip; iterate)
open import src.reals using (Real)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

module src.DFT (r : Real) where
  open Real r using (ℝ; _-ᵣ_; _*ᵣ_; _ₙ/ᵣ_; π; fromℕ)
  open import src.complex r using (ℂ; ℂfromℕ; _+_; _*_;e^i_)

  DFT : ∀ {N : ℕ} → Vec ℂ N → Vec ℂ N
  DFT {N} xs k = foldr (step (toℕ k)) (ℂfromℕ 0) (zip xs posVec)
    where
      0-2 : ℝ
      0-2 = (fromℕ 0) -ᵣ (fromℕ 2) 

      step : ℕ → (ℂ × ℕ) → ℂ → ℂ
      step k ⟨ xₙ , n ⟩ acc = acc + (xₙ * e^i (0-2 *ᵣ π *ᵣ fromℕ n *ᵣ (k ₙ/ᵣ N)))

      posVec : Vec ℕ N
      posVec = iterate N suc 0
