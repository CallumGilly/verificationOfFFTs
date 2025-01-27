module src.FFTSpliter where


open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length)
open import src.Reshape using (Reshape; transposeᵣ; recursive-transpose; reshape; split; swap; _∙_; eq; _⊕_; flat)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open import Data.Nat.Properties using (*-comm)
open import Data.Fin.Base using (Fin)

---- - LEGACY
splitAndSwap : ∀ {n m : ℕ} → Reshape (ι (n *ₙ m)) (ι m ⊗ ι n)
splitAndSwap {n} {m} = swap ∙ (split {n} {m})

splitOnce : ∀ {n m : ℕ} {X : Set} → Ar (ι (n *ₙ m)) X → Ar (ι m ⊗ ι n) X
splitOnce {n} {m} arr = reshape (splitAndSwap {n} {m}) arr


FFT-flattern : ∀ {s : Shape} → Reshape s (ι (length s))
FFT-flattern {ι x   } = eq
FFT-flattern {s ⊗ s₁} = flat ∙ (FFT-flattern ⊕ FFT-flattern)
--FFT-flattern {s ⊗ s₁} rewrite *-comm (length s) (length s₁) = flat ∙ swap ∙ (FFT-flattern ⊕ FFT-flattern)
