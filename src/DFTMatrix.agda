open import src.Real using (Real)
open import src.Matrix using (Ar; ι; foldr; zipWith; iterate)
open import Data.Nat.Base using (ℕ; suc) renaming (_*_ to _*ₙ_)
open import Data.Fin.Base using (toℕ; Fin)


-- Definition of DFT using retricted matrices instead of Vectors
module src.DFTMatrix (r : Real) where
  open import src.Complex r using (ℂ; ℂfromℕ; _+_; _*_; -ω)
  
  posVec : ∀ {N : ℕ} → Ar (ι N) ℕ
  posVec (ι x) = toℕ x

  step : {N : ℕ} → {Fin N} → ℂ → ℕ → ℂ
  step {N} {k} xₙ n = xₙ * (-ω N (n *ₙ (toℕ k)))

  -- May need checks on division exluding zero
  DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} xs (ι k) = foldr (_+_) (ℂfromℕ 0) (zipWith (step {N} {k}) xs posVec)

  -- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
