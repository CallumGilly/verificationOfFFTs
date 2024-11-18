open import src.Real using (Real)
module src.FFT (r : Real) where

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; nest; map; unnest; ι-cons; nil; _==_)
open import Data.Nat.Base using (ℕ; zero) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin.Base using (Fin; toℕ; splitAt) renaming (zero to fzero; suc to fsuc)
open import Data.Sum.Base using (inj₁; inj₂)

open import src.Complex r using (ℂ; ℂfromℕ; _+_; _-_; _*_; ω; *-identityʳ; ω-N-0)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

conged+-identityʳ : ∀ (n : ℕ) → n +ₙ (n +ₙ zero) ≡ n +ₙ n
conged+-identityʳ n =
  begin
    n +ₙ (n +ₙ zero)
  ≡⟨ cong (n +ₙ_) (+-identityʳ n) ⟩
    n +ₙ n
  ∎

-- Taken from Wikipedia
-- for k = 0 to N/2−1 do                        combine DFTs of two halves into full DFT:
--     p ← Xk
--     q ← exp(−2πi/N k) Xk+N/2
--     Xk ← p + q 
--     Xk+N/2 ← p − q
-- end for

fft₂-butterfly-K     : ∀ (N/2 : ℕ) (k : Fin N/2) → Ar (ι 2 ⊗ ι N/2) ℂ → ℂ
fft₂-butterfly-K     N/2 k ar = p + q
  where
    p : ℂ
    p = ar (ι fzero ⊗ ι k) 
    q : ℂ
    q = (ar (ι (fsuc fzero) ⊗ ι k)) * ω (2 *ₙ N/2) (toℕ k)

fft₂-butterfly-K+N/2 : ∀ (N/2 : ℕ) (k : Fin N/2) → Ar (ι 2 ⊗ ι N/2) ℂ → ℂ
fft₂-butterfly-K+N/2 N/2 k ar = p - q
  where
    p : ℂ
    p = ar (ι fzero ⊗ ι k) 
    q : ℂ
    q = (ar (ι (fsuc fzero) ⊗ ι k)) * (ω (2 *ₙ N/2) (toℕ k))

fft₂-butterfly : ∀ {N/2 : ℕ} → Ar (ι 2 ⊗ ι N/2) ℂ → Ar (ι (2 *ₙ N/2)) ℂ
fft₂-butterfly {N/2} ar (ι n) with splitAt N/2 nReshaped
  where
    nReshaped : Fin (N/2 +ₙ N/2)
    nReshaped rewrite conged+-identityʳ N/2 = n
... | inj₁ k = fft₂-butterfly-K     N/2 k ar
... | inj₂ k = fft₂-butterfly-K+N/2 N/2 k ar


data splitWithRadix2 : Shape → Set where
  singleton : ∀ {s : Shape}
    → s ≡ ι 1
    ----------------------
    → splitWithRadix2 s

  splitAr : ∀ {s t : Shape}
    → splitWithRadix2 t
    → s ≡ ι 2 ⊗ t
    ----------------------
    → splitWithRadix2 s

newRad2ArLength : ∀ (s : Shape) 
  → splitWithRadix2 s
  → ℕ
newRad2ArLength (ι 1) (singleton x) = 1
newRad2ArLength (ι 2 ⊗ subAr) (splitAr prf refl) = 2 *ₙ newRad2ArLength subAr prf

FFT₂ : ∀ {s : Shape} {n : ℕ}
    → (prf : splitWithRadix2 s)
    → n ≡ newRad2ArLength s prf
    → Ar s ℂ 
    --------------
    → Ar (ι n) ℂ
FFT₂ {ι 1    } (singleton     refl) refl xs = xs
FFT₂ {ι 2 ⊗ s} (splitAr   prf refl) refl xs = fft₂-butterfly (unnest (map (FFT₂ {s} {newRad2ArLength s prf} prf refl) (nest xs)))

-- data generalRadixSplit : Shape → Set where
--   singleton : ∀ {s : Shape}
--     → s ≡ ι 1
--     ----------------------
--     → generalRadixSplit s
-- 
-- newGeneralArLength : ∀ (s : Shape)
--   → generalRadixSplit s
--   → ℕ
-- newGeneralArLength s splt = ?
-- 
-- general-FFT : ∀ {s : Shape} {N₁ N₂ : ℕ} 
--   → Ar s ℂ
--   → Ar (ι ?) ℂ
-- general-FFT = ?

evidence-one : ∀ {x₀ : ℂ} → FFT₂
  {ι 1}
  {1}
  (singleton refl)
  refl
  (ι-cons x₀ nil)
  == (ι-cons x₀ nil)
evidence-one = λ p → refl

evidence-two : ∀ {x₀ x₂ : ℂ} → FFT₂
  {ι 2 ⊗ ι 1}
  {2}
  (splitAr (singleton refl) refl)
  refl
  (unnest (
       ι-cons (ι-cons x₀ nil) 
      (ι-cons (ι-cons x₂ nil) nil)
    ))
  == ι-cons (x₀ + x₂) (ι-cons (x₀ - x₂) nil) 
evidence-two {x₀} {x₂} (ι fzero) =
  begin
    fft₂-butterfly-K 1 fzero
            (unnest
             (map (λ xs → xs)
              (nest
               (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))))))
  ≡⟨⟩
    fft₂-butterfly-K 1 fzero (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil)))
  ≡⟨⟩
    (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι fzero ⊗ ι fzero) +
    (((unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι (fsuc fzero) ⊗ ι fzero)) * ω (2 *ₙ 1) (0))
  ≡⟨⟩
    x₀ + (x₂ * ω 2 0)
  ≡⟨ cong (x₀ +_) (cong (x₂ *_) ω-N-0) ⟩
    x₀ + (x₂ * ℂfromℕ 1)
  ≡⟨ cong (x₀ +_) (*-identityʳ) ⟩
    x₀ + x₂
  ∎
evidence-two {x₀} {x₂} (ι (fsuc fzero)) =
  begin
    fft₂-butterfly-K+N/2 1 fzero
            (unnest
             (map (λ xs → xs)
              (nest
               (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))))))
  ≡⟨⟩
    fft₂-butterfly-K+N/2 1 fzero (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil)))
  ≡⟨⟩
    (  unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι       fzero  ⊗ ι fzero) -
    (((unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι (fsuc fzero) ⊗ ι fzero)) * (ω (2 *ₙ 1) (0)))
  ≡⟨⟩
    x₀ - (x₂ * (ω 2 0))
  ≡⟨ cong (x₀ -_) (cong (x₂ *_) ω-N-0) ⟩
    x₀ - x₂ * ℂfromℕ 1
  ≡⟨ cong (x₀ -_) *-identityʳ ⟩
    x₀ - x₂
  ∎

-- evidence-four : ∀ {x₀ x₁ x₂ x₃ : ℂ} → 
--   FFT₂ 
--     {ι 2 ⊗ (ι 2 ⊗ ι 1)} 
--     {4}
--     (splitAr {ι 2 ⊗ (ι 2 ⊗ ι 1)} {ι 2 ⊗ ι 1} (splitAr (singleton refl) refl) refl)
--     refl
--     (unnest 
--     (ι-cons (unnest (
--        ι-cons (ι-cons x₀ nil) 
--       (ι-cons (ι-cons x₁ nil) nil)
--     )) 
--     (ι-cons (unnest (
--        ι-cons (ι-cons x₂ nil) 
--       (ι-cons (ι-cons x₃ nil) nil))
--     ) nil))
--   ) == 
--        ι-cons (x₀ +  x₁                      + x₂ +  x₃                     )
--       (ι-cons (x₀ - (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ + (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
--       (ι-cons (x₀ -  x₁                      + x₂ -  x₃                     )
--       (ι-cons (x₀ + (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ - (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
--        nil)))
-- evidence-four = ?

-- FFT₂ {ι 1    } xs (singleton   x) = ?
-- FFT₂ {ι 2 ⊗ s} xs (splitAr prf x) = ?
-- FFT₂ {ι 0} ar = ? --(ι ()) -- Length of 0 is absurd
-- FFT₂ {ι 1} ar = ?
-- FFT₂ {ι (suc (suc x))} ar = ?
-- FFT₂ {ι 2 ⊗ t₁} ar = ? -- fft₂-butterfly (unnest (map FFT₂ (nest ar)))
-- FFT₂ {ι x ⊗ t₁} ar = ?
-- FFT₂ {(t ⊗ t₂) ⊗ t₁} ar = ?

-- FFT₁ {x} ar = ?
-- 
-- FFT₂ {s} ar = ?
-- 
-- FFT {ι x             } ar = FFT₁ ar
-- FFT {s ⊗ t} ar = FFT₂ ar -- unnest (map (FFT) (nest Ar))




-- FFT {ι x      } ar = vecToArr (DFT (arrToVec ar)) -- This is but a vector
-- Assume this is row major order (i.e. (nest ar) i gives this ith row of the matrix)
-- FFT {} ar = vecToArr (DFT (arrToVec ar)) -- This is but a vector
-- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
