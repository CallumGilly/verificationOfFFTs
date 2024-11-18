open import src.Vector using (Vec; foldr; zip; iterate)
open import src.Real using (Real)
open import Data.Nat.Base using (ℕ; suc) renaming (_*_ to _*ₙ_)
open import Data.Fin.Base using (toℕ)
open import Data.Product.Base using (_×_) renaming ( _,_ to ⟨_,_⟩)

module src.DFT (r : Real) where
  open import src.Complex r using (ℂ; ℂfromℕ; _+_; _*_; ω)
  
  -- May need checks on division exluding zero

  DFT : ∀ {N : ℕ} → Vec ℂ N → Vec ℂ N
  DFT {N} xs k = foldr (step (toℕ k)) (ℂfromℕ 0) (zip xs posVec)
    where
      step : ℕ → (ℂ × ℕ) → ℂ → ℂ
      step k ⟨ xₙ , n ⟩ acc = acc + (xₙ * (ω N (n *ₙ k)))

      posVec : Vec ℕ N
      posVec = iterate N suc 0

  -- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
