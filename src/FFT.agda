open import src.Real using (Real)
module src.FFT (r : Real) where

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; nest; map; foldr; unnest; ι-cons; nil; _==_; zip; iterate)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin.Base using (Fin; toℕ; splitAt) renaming (zero to fzero; suc to fsuc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import src.VecMat using (arrToVec; vecToArr)

open import src.DFT r using (DFT)
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


data FFT₂-shaped : Shape → Set where
  singleton : ∀ {s : Shape}
    → s ≡ ι 1
    ----------------------
    → FFT₂-shaped s

  splitAr : ∀ {s t : Shape}
    → FFT₂-shaped t
    → s ≡ ι 2 ⊗ t
    ----------------------
    → FFT₂-shaped s

newRad2ArLength : ∀ (s : Shape) 
  → FFT₂-shaped s
  → ℕ
newRad2ArLength (ι 1) (singleton x) = 1
newRad2ArLength (ι 2 ⊗ subAr) (splitAr prf refl) = 2 *ₙ newRad2ArLength subAr prf

FFT₂ : ∀ {s : Shape} {N : ℕ}
    → (prf : FFT₂-shaped s)
    → N ≡ newRad2ArLength s prf
    → Ar s ℂ 
    --------------
    → Ar (ι N) ℂ
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

data valid-shape : Shape → Set where
  singleton : ∀ {s : Shape}
    → s ≡ ι 1
    -------------
    → valid-shape s

  dft-shaped : ∀ {s : Shape} {n : ℕ}
    → s ≡ ι n
    ---------------
    → valid-shape s

  cooley-tukey-split : ∀ {s t : Shape} {radix : ℕ}
    → valid-shape t
    → s ≡ ι radix ⊗ t
    -------------------
    → valid-shape s

final-shape-length : ∀ (s : Shape)
  → valid-shape s
  → ℕ
final-shape-length (ι n) (singleton  refl) = n
final-shape-length (ι n) (dft-shaped refl) = n
final-shape-length (ι radix ⊗ subShape) (cooley-tukey-split subShapeIsValid refl) = radix *ₙ (final-shape-length subShape subShapeIsValid)

general-case-butterfly : ∀ {r N/r : ℕ} → Ar (ι r ⊗ ι N/r) ℂ → Ar (ι (r *ₙ N/r)) ℂ
--general-case-butterfly {radix} {N/r} xs (ι n) = let tmp = foldr ? (ℂfromℕ 0) (zip (iterate radix suc 0) (nest xs)) in ?
--general-case-butterfly {radix} {N/r} xs (ι n) = let tmp = (zip (iterate radix suc 0) (nest xs)) in ?
  where
    submissive-twiddler : Ar (ι N/r) (ℕ × ℂ) → ℂ → ℂ
    submissive-twiddler = ?

FFT : ∀ {s : Shape} {N : ℕ}
  → (shape-description : valid-shape s)
  → N ≡ final-shape-length s shape-description 
  → Ar s ℂ
  --------------------------------------------
  → Ar (ι N) ℂ
FFT (singleton  refl) refl ar = ar
FFT (dft-shaped refl) refl ar = vecToArr (DFT (arrToVec ar)) 
FFT (cooley-tukey-split {t = t} {radix = radix} shape-description refl) refl ar = general-case-butterfly 
                                                                                    {radix} 
                                                                                    {final-shape-length t shape-description }
                                                                                    (unnest (map (FFT shape-description refl) (nest ar)))
--FFT₂ {ι 2 ⊗ s} (splitAr   prf refl) refl xs = fft₂-butterfly (unnest (map (FFT₂ {s} {newRad2ArLength s prf} prf refl) (nest xs)))
-- FFT {ι x             } ar 
-- FFT {s ⊗ t} ar = FFT₂ ar -- unnest (map (FFT) (nest Ar))

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





-- FFT {ι x      } ar = vecToArr (DFT (arrToVec ar)) -- This is but a vector
-- Assume this is row major order (i.e. (nest ar) i gives this ith row of the matrix)
-- FFT {} ar = vecToArr (DFT (arrToVec ar)) -- This is but a vector
-- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
