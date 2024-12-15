open import src.Real using (Real)
module legacy.FFT (r : Real) where

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; nest; map; foldr; unnest; ι-cons; nil; _==_; zip; iterate; transpose; zipWith)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin.Base using (Fin; toℕ; splitAt) renaming (zero to fzero; suc to fsuc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Function.Base using (_∘_)
open import src.VecMat using (arrToVec; vecToArr)

open import src.DFTMatrix r using (DFT)
open import src.Complex r using (ℂ; ℂfromℕ; _+_; _-_; _*_; ω; *-identityʳ; ω-N-0; _+_i; e^i_; e^0; e^i[-π])
open import src.ComplexMatrix r using (sigma)
open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ;
    /ᵣ-zeroₜ; +ᵣ-identityʳ; neg-distrib-*; *ᵣ-comm; *ᵣ-assoc; *-cancels-/)
  renaming (_*_ to _*ᵣ_; _/_ to _/ᵣ_; _+_ to _+ᵣ_; -_ to neg_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

private
  variable
    N r₁ r₂ : ℕ

FFT₁ : Ar (ι N) ℂ → Ar (ι N) ℂ
FFT₁ arr = DFT arr

-- Taken from "Computational Frameworks for the Fast Fourier Transform"
-- ISBN 978-0-898712-85-8
-- 1.1.2
-- Fₙ : ∀ {N : ℕ} → Ar (ι N ⊗ ι N) ℂ
-- Fₙ {N} (ι p ⊗ ι q) = ω N ((toℕ p) *ₙ (toℕ q))--e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (toℕ p) ᵣ *ᵣ (toℕ q) ᵣ ) /ᵣ (n ᵣ))

--twiddles : Ar (ι r₁ ⊗ ι r₂) ℂ
--twiddles {r₁} {r₂} (ι k₁ ⊗ ι k₀) = ω (r₁ *ₙ r₂) (k₁ )
-- ω N k = e^i (((2 ᵣ) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

transposeₛ : Shape → Shape
transposeₛ (ι x) = ι x
transposeₛ (s ⊗ p) = (transposeₛ p) ⊗ (transposeₛ s) 

_ₙ/ᵣ_ : ∀ {f : ℕ} → Fin f → ℕ → ℝ
_ₙ/ᵣ_ m n = ((toℕ m) ᵣ) /ᵣ (n ᵣ)

twiddle-sum : ∀ {s : Shape} → Position s → ℝ
twiddle-sum {ι n} (ι pos) = pos ₙ/ᵣ n
twiddle-sum {sₗ ⊗ sᵣ} (xₗ ⊗ xᵣ) = (twiddle-sum xₗ) +ᵣ (twiddle-sum xᵣ)

--Need to check the difference between neg and not neg, I belive thats the difference for DIT vs DIF
twiddles : ∀ {s : Shape} → Ar s ℂ
twiddles {s} p = e^i (((neg (2 ᵣ)) *ᵣ π *ᵣ (twiddle-sum p)) ) 

FFT₂ : Ar (ι r₁ ⊗ ι r₂) ℂ → Ar (ι r₂ ⊗ ι r₁) ℂ
FFT₂ {r₁} {r₂} arr = let t  = unnest (map FFT₁ (nest arr)) in -- map on arr goes over rows, map on arrᵗ goes over the columns, as we want deciation in time, we want to use map arr
                     let t′ = zipWith _*_ t twiddles in
                     unnest (map FFT₁ (nest (transpose t′)))

FFT : ∀ {s : Shape} → Ar s ℂ → Ar (transposeₛ s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = unnest (map FFT (nest arr)) in
                     let twiddleFactorsApplied = zipWith _*_ innerDFTapplied twiddles in
                     unnest (map FFT (nest (transpose twiddleFactorsApplied)))
-- FFT {ι x ⊗ ι x₁ } arr = FFT₂ arr -- I think this case is unnened as its covered by the next case
-- Could be worth deriving a trivial equivialant of complex and floats from agda floats
-- Proof that the first two twiddles are correct
tmp : twiddles {ι 2} == ι-cons (ℂfromℕ 1) (ι-cons ((neg (1 ᵣ)) + (0 ᵣ) i) nil)
tmp (ι fzero) =
  begin
   twiddles {ι 2} (ι fzero)
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ (twiddle-sum (ι fzero))) 
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ (_ₙ/ᵣ_ {2} fzero 2)) 
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ ((0 ᵣ) /ᵣ (2 ᵣ))) 
  ≡⟨ cong (e^i_) (cong (neg 2 ᵣ *ᵣ π *ᵣ_) (/ᵣ-zeroₜ (2 ᵣ))) ⟩
    e^i (((neg (2 ᵣ)) *ᵣ π) *ᵣ 0 ᵣ) 
  ≡⟨ cong (e^i_) (*ᵣ-zeroᵣ ((neg (2 ᵣ)) *ᵣ π)) ⟩
    e^i (0 ᵣ) 
  ≡⟨ e^0 ⟩
    ℂfromℕ 1
  ∎
tmp (ι (fsuc fzero)) =
  begin
    twiddles (ι (fsuc fzero))
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ (twiddle-sum (ι (fsuc fzero)))) 
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ (_ₙ/ᵣ_ {2} (fsuc fzero) 2)) 
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ))) 
  ≡⟨⟩
    e^i ((neg (2 ᵣ)) *ᵣ π *ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ))) 
  ≡⟨ cong e^i_ (cong (_*ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ))) (neg-distrib-* (2 ᵣ) π)) ⟩
    e^i (neg ((2 ᵣ) *ᵣ π) *ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ))) 
  ≡⟨ cong e^i_ (neg-distrib-* ((2 ᵣ) *ᵣ π) (_/ᵣ_ (1 ᵣ) (2 ᵣ))) ⟩
    e^i (neg (((2 ᵣ) *ᵣ π) *ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ)))) 
  ≡⟨ cong e^i_ (cong neg_ (cong (_*ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ))) (*ᵣ-comm (2 ᵣ) (π)))) ⟩
    e^i (neg ((π *ᵣ (2 ᵣ)) *ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ)))) 
  ≡⟨ cong e^i_ (cong neg_ (*ᵣ-assoc π (2 ᵣ) (_/ᵣ_ (1 ᵣ) (2 ᵣ)))) ⟩
    e^i (neg (π *ᵣ ((2 ᵣ) *ᵣ (_/ᵣ_ (1 ᵣ) (2 ᵣ))))) 
  ≡⟨ cong e^i_ (cong neg_ (cong (π *ᵣ_) (*-cancels-/ (2 ᵣ) (1 ᵣ)))) ⟩
    e^i (neg (π *ᵣ (1 ᵣ))) 
  ≡⟨ cong e^i_ (cong neg_ (*ᵣ-identityʳ π)) ⟩
    e^i (neg (π)) 
  ≡⟨ e^i[-π] ⟩
    ((neg 1 ᵣ) + 0 ᵣ i) 
  ∎
    -- e^i[-π] : e^i (-ᵣ π) ≡ (-ᵣ (1 ᵣ)) + (0 ᵣ) i
    --*ᵣ-identityʳ : ∀ (x : ℝ) → x * (1 ᵣ) ≡ x
-- neg-distrib-*

----------------------------------------------------------------------------------------------
-- Second Radix 2 attemmpt, following the notation given in the original Cooley Tukey Paper -- 
----------------------------------------------------------------------------------------------

-- private
--   variable
--     n r₁ r₂ : ℕ
--     -- This means that j₀ j₁ k₀ and k₁ will always be of the correct type, and gives a quick reference to what they should be
--     j₀ k₁ : Fin r₁
--     j₁ k₀ : Fin r₂
-- 
-- -- This should be definable as the DFT no?
-- A₁-step : (j₀ : Fin r₁) → (k₀ : Fin r₂) → Ar (ι r₁) (Ar (ι r₂) ℂ) → Position (ι r₁) → ℂ
-- A₁-step {r₁} {r₂} j₀ k₀ arr (ι k₁) = arr (ι k₁) (ι k₀) * ω (r₁ *ₙ r₂) ((toℕ j₀) *ₙ (toℕ k₁) *ₙ r₂)
-- 
-- A₁ : Ar (ι r₁) (Ar (ι r₂) ℂ) →  Ar (ι r₁ ⊗ ι r₂) ℂ
-- A₁ arr (ι j₀ ⊗ ι k₀) = sigma arr (A₁-step j₀ k₀)
-- 
-- FFT₂-step : (j₀ : Fin r₁) → (j₁ : Fin r₂) → Ar (ι r₂) (Ar (ι r₁) ℂ) → Position (ι r₂) → ℂ
-- FFT₂-step {r₁} {r₂} j₀ j₁ A₁-arr (ι k₀) = A₁-arr (ι k₀) (ι j₀) * ω (r₁ *ₙ r₂) (((toℕ j₁ *ₙ r₁) +ₙ toℕ j₀) *ₙ (toℕ k₀))
-- 
-- FFT₂ : Ar (ι r₁ ⊗ ι r₂) ℂ → Ar (ι r₂ ⊗ ι r₁) ℂ
-- FFT₂ arr (ι j₁ ⊗ ι j₀) = sigma (nest (transpose (A₁ (nest arr)))) (FFT₂-step j₀ j₁)

-- FFT₂-Evidence-Four : ∀ {x₀ x₁ x₂ x₃ : ℂ} → 
--     FFT₂ {2} {2} 
--       (unnest (ι-cons 
--         (ι-cons x₀ (ι-cons x₁ nil)) 
--       (ι-cons 
--         (ι-cons x₂ (ι-cons x₃ nil)) 
--       nil)))
--   == 
--       (unnest (ι-cons 
--         (ι-cons (x₀ +  x₁                      + x₂ +  x₃                     )  
--         (ι-cons (x₀ - (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ + (x₃ * ((0 ᵣ) + (1 ᵣ) i)))  
--         nil)) 
--       (ι-cons 
--         (ι-cons (x₀ -  x₁                      + x₂ -  x₃                     )
--         (ι-cons (x₀ + (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ - (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
--         nil)) 
--       nil)))
-- FFT₂-Evidence-Four {x₀} {x₁} {x₂} {x₃} (ι       fzero  ⊗ ι       fzero ) =
--   begin
--     sigma (nest (transpose (A₁ (nest (unnest (ι-cons (ι-cons x₀ (ι-cons x₁ nil)) (ι-cons (ι-cons x₂ (ι-cons x₃ nil)) nil))))))) (FFT₂-step fzero fzero)
--   ≡⟨⟩
--     sigma (nest (transpose (A₁ (ι-cons (ι-cons x₀ (ι-cons x₁ nil)) (ι-cons (ι-cons x₂ (ι-cons x₃ nil)) nil))))) (FFT₂-step fzero fzero)
--   ≡⟨⟩
--     ?
-- FFT₂-Evidence-Four {x₀} {x₁} {x₂} {x₃} (ι       fzero  ⊗ ι (fsuc fzero)) = ?
-- FFT₂-Evidence-Four {x₀} {x₁} {x₂} {x₃} (ι (fsuc fzero) ⊗ ι       fzero ) = ?
-- FFT₂-Evidence-Four {x₀} {x₁} {x₂} {x₃} (ι (fsuc fzero) ⊗ ι (fsuc fzero)) = ?


-- -- evidence-four : ∀ {x₀ x₁ x₂ x₃ : ℂ} → 
-- --   FFT₂ 
-- --     {ι 2 ⊗ (ι 2 ⊗ ι 1)} 
-- --     {4}
-- --     (splitAr {ι 2 ⊗ (ι 2 ⊗ ι 1)} {ι 2 ⊗ ι 1} (splitAr (singleton refl) refl) refl)
-- --     refl
-- --     (unnest 
-- --     (ι-cons (unnest (
-- --        ι-cons (ι-cons x₀ nil) 
-- --       (ι-cons (ι-cons x₁ nil) nil)
-- --     )) 
-- --     (ι-cons (unnest (
-- --        ι-cons (ι-cons x₂ nil) 
-- --       (ι-cons (ι-cons x₃ nil) nil))
-- --     ) nil))
-- --   ) == 
-- --        ι-cons (x₀ +  x₁                      + x₂ +  x₃                     )
-- --       (ι-cons (x₀ - (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ + (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
-- --       (ι-cons (x₀ -  x₁                      + x₂ -  x₃                     )
-- --       (ι-cons (x₀ + (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ - (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
-- --        nil)))
-- -- evidence-four = ?






-- conged+-identityʳ : ∀ (n : ℕ) → n +ₙ (n +ₙ zero) ≡ n +ₙ n
-- conged+-identityʳ n =
--   begin
--     n +ₙ (n +ₙ zero)
--   ≡⟨ cong (n +ₙ_) (+-identityʳ n) ⟩
--     n +ₙ n
--   ∎

-- F₁ : Fₙ {1} == unnest (ι-cons (ι-cons (ℂfromℕ 1) nil) nil) 
-- F₁ = 
--   λ{(ι fzero ⊗ ι fzero) → 
--     begin
--       ω 1 0
--     ≡⟨⟩
--       e^i (((-ᵣ 2 ᵣ *ᵣ π) *ᵣ (0 ᵣ)) /ᵣ (1 ᵣ))
--     ≡⟨ cong (e^i_) (cong (_/ᵣ (1 ᵣ)) *ᵣ-zeroᵣ) ⟩
--       e^i ((0 ᵣ) /ᵣ (1 ᵣ))
--     ≡⟨ cong (e^i_) /ᵣ-zeroₜ ⟩
--       e^i (0 ᵣ)
--     ≡⟨ e^0 ⟩
--       ℂfromℕ 1
--     ∎
--   }


---------------------------------------------------------------------------------------------
-- First Radix 2 attemmpt, with restrictions imposed on the shape, and flattening implicit --
---------------------------------------------------------------------------------------------

-- Taken from Wikipedia
-- for k = 0 to N/2−1 do                        combine DFTs of two halves into full DFT:
--     p ← Xk
--     q ← exp(−2πi/N k) Xk+N/2
--     Xk ← p + q 
--     Xk+N/2 ← p − q
-- end for


-- fft₂-butterfly-K     : ∀ (N/2 : ℕ) (k : Fin N/2) → Ar (ι 2 ⊗ ι N/2) ℂ → ℂ
-- fft₂-butterfly-K     N/2 k ar = p + q
--   where
--     p : ℂ
--     p = ar (ι fzero ⊗ ι k) 
--     q : ℂ
--     q = (ar (ι (fsuc fzero) ⊗ ι k)) * ω (2 *ₙ N/2) (toℕ k)
-- 
-- fft₂-butterfly-K+N/2 : ∀ (N/2 : ℕ) (k : Fin N/2) → Ar (ι 2 ⊗ ι N/2) ℂ → ℂ
-- fft₂-butterfly-K+N/2 N/2 k ar = p - q
--   where
--     p : ℂ
--     p = ar (ι fzero ⊗ ι k) 
--     q : ℂ
--     q = (ar (ι (fsuc fzero) ⊗ ι k)) * (ω (2 *ₙ N/2) (toℕ k))
-- 
-- fft₂-butterfly : ∀ {N/2 : ℕ} → Ar (ι 2 ⊗ ι N/2) ℂ → Ar (ι (2 *ₙ N/2)) ℂ
-- fft₂-butterfly {N/2} ar (ι n) with splitAt N/2 nReshaped
--   where
--     nReshaped : Fin (N/2 +ₙ N/2)
--     nReshaped rewrite conged+-identityʳ N/2 = n
-- ... | inj₁ k = fft₂-butterfly-K     N/2 k ar
-- ... | inj₂ k = fft₂-butterfly-K+N/2 N/2 k ar
-- 
-- 
-- data FFT₂-shaped : Shape → Set where
--   singleton : ∀ {s : Shape}
--     → s ≡ ι 1
--     ----------------------
--     → FFT₂-shaped s
-- 
--   splitAr : ∀ {s t : Shape}
--     → FFT₂-shaped t
--     → s ≡ ι 2 ⊗ t
--     ----------------------
--     → FFT₂-shaped s
-- 
-- newRad2ArLength : ∀ (s : Shape) 
--   → FFT₂-shaped s
--   → ℕ
-- newRad2ArLength (ι 1) (singleton x) = 1
-- newRad2ArLength (ι 2 ⊗ subAr) (splitAr prf refl) = 2 *ₙ newRad2ArLength subAr prf
-- 
-- FFT₂ : ∀ {s : Shape} {N : ℕ}
--     → (prf : FFT₂-shaped s)
--     → N ≡ newRad2ArLength s prf
--     → Ar s ℂ 
--     --------------
--     → Ar (ι N) ℂ
-- FFT₂ {ι 1    } (singleton     refl) refl xs = xs
-- FFT₂ {ι 2 ⊗ s} (splitAr   prf refl) refl xs = fft₂-butterfly (unnest (map (FFT₂ {s} {newRad2ArLength s prf} prf refl) (nest xs)))


---------------------------------------------------------------------------------------------------
-- First general case attemmpt, with restrictions imposed on the shape, and flattening implicit --
---------------------------------------------------------------------------------------------------

-- data valid-shape : Shape → Set where
--   singleton : ∀ {s : Shape}
--     → s ≡ ι 1
--     -------------
--     → valid-shape s
-- 
--   dft-shaped : ∀ {s : Shape} {n : ℕ}
--     → s ≡ ι n
--     ---------------
--     → valid-shape s
-- 
--   cooley-tukey-split : ∀ {s t : Shape} {radix : ℕ}
--     → valid-shape t
--     → s ≡ ι radix ⊗ t
--     -------------------
--     → valid-shape s
-- 
-- final-shape-length : ∀ (s : Shape)
--   → valid-shape s
--   → ℕ
-- final-shape-length (ι n) (singleton  refl) = n
-- final-shape-length (ι n) (dft-shaped refl) = n
-- final-shape-length (ι radix ⊗ subShape) (cooley-tukey-split subShapeIsValid refl) = radix *ₙ (final-shape-length subShape subShapeIsValid)
-- 
-- general-case-butterfly : ∀ {r N/r : ℕ} → Ar (ι r ⊗ ι N/r) ℂ → Ar (ι (r *ₙ N/r)) ℂ
-- general-case-butterfly {radix} {N/r} xs (ι n) = let tmp = foldr ? (ℂfromℕ 0) (zip (iterate radix suc 0) (nest xs)) in ?
-- --general-case-butterfly {radix} {N/r} xs (ι n) = let tmp = (zip (iterate radix suc 0) (nest xs)) in ?
--   where
--     helper : Ar (ι N/r) (ℕ × ℂ) → ℂ → ℂ
--     helper = ?
-- 
-- -- try implementing for ι n ⊗ ι m 
-- 
-- FFT : ∀ {s : Shape} {N : ℕ}
--   → (shape-description : valid-shape s)
--   → N ≡ final-shape-length s shape-description 
--   → Ar s ℂ
--   --------------------------------------------
--   → Ar (ι N) ℂ
-- FFT (singleton  refl) refl ar = ar
-- FFT (dft-shaped refl) refl ar = vecToArr (DFT (arrToVec ar)) 
-- FFT (cooley-tukey-split {t = t} {radix = radix} shape-description refl) refl ar = general-case-butterfly 
--                                                                                     {radix} 
--                                                                                     {final-shape-length t shape-description }
--                                                                                     (unnest (map (FFT shape-description refl) (nest ar)))
-- --FFT₂ {ι 2 ⊗ s} (splitAr   prf refl) refl xs = fft₂-butterfly (unnest (map (FFT₂ {s} {newRad2ArLength s prf} prf refl) (nest xs)))
-- -- FFT {ι x             } ar 
-- -- FFT {s ⊗ t} ar = FFT₂ ar -- unnest (map (FFT) (nest Ar))

---------------------------------------------------------------------------
-- Evidence for the radix 2 implementation to test it works as inteneded --
---------------------------------------------------------------------------

-- evidence-one : ∀ {x₀ : ℂ} → FFT₂
--   {ι 1}
--   {1}
--   (singleton refl)
--   refl
--   (ι-cons x₀ nil)
--   == (ι-cons x₀ nil)
-- evidence-one = λ p → refl
-- 
-- evidence-two : ∀ {x₀ x₂ : ℂ} → FFT₂
--   {ι 2 ⊗ ι 1}
--   {2}
--   (splitAr (singleton refl) refl)
--   refl
--   (unnest (
--        ι-cons (ι-cons x₀ nil) 
--       (ι-cons (ι-cons x₂ nil) nil)
--     ))
--   == ι-cons (x₀ + x₂) (ι-cons (x₀ - x₂) nil) 
-- evidence-two {x₀} {x₂} (ι fzero) =
--   begin
--     fft₂-butterfly-K 1 fzero
--             (unnest
--              (map (λ xs → xs)
--               (nest
--                (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))))))
--   ≡⟨⟩
--     fft₂-butterfly-K 1 fzero (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil)))
--   ≡⟨⟩
--     (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι fzero ⊗ ι fzero) +
--     (((unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι (fsuc fzero) ⊗ ι fzero)) * ω (2 *ₙ 1) (0))
--   ≡⟨⟩
--     x₀ + (x₂ * ω 2 0)
--   ≡⟨ cong (x₀ +_) (cong (x₂ *_) ω-N-0) ⟩
--     x₀ + (x₂ * ℂfromℕ 1)
--   ≡⟨ cong (x₀ +_) (*-identityʳ) ⟩
--     x₀ + x₂
--   ∎
-- evidence-two {x₀} {x₂} (ι (fsuc fzero)) =
--   begin
--     fft₂-butterfly-K+N/2 1 fzero
--             (unnest
--              (map (λ xs → xs)
--               (nest
--                (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))))))
--   ≡⟨⟩
--     fft₂-butterfly-K+N/2 1 fzero (unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil)))
--   ≡⟨⟩
--     (  unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι       fzero  ⊗ ι fzero) -
--     (((unnest (ι-cons (ι-cons x₀ nil) (ι-cons (ι-cons x₂ nil) nil))) (ι (fsuc fzero) ⊗ ι fzero)) * (ω (2 *ₙ 1) (0)))
--   ≡⟨⟩
--     x₀ - (x₂ * (ω 2 0))
--   ≡⟨ cong (x₀ -_) (cong (x₂ *_) ω-N-0) ⟩
--     x₀ - x₂ * ℂfromℕ 1
--   ≡⟨ cong (x₀ -_) *-identityʳ ⟩
--     x₀ - x₂
--   ∎
-- 
-- -- evidence-four : ∀ {x₀ x₁ x₂ x₃ : ℂ} → 
-- --   FFT₂ 
-- --     {ι 2 ⊗ (ι 2 ⊗ ι 1)} 
-- --     {4}
-- --     (splitAr {ι 2 ⊗ (ι 2 ⊗ ι 1)} {ι 2 ⊗ ι 1} (splitAr (singleton refl) refl) refl)
-- --     refl
-- --     (unnest 
-- --     (ι-cons (unnest (
-- --        ι-cons (ι-cons x₀ nil) 
-- --       (ι-cons (ι-cons x₁ nil) nil)
-- --     )) 
-- --     (ι-cons (unnest (
-- --        ι-cons (ι-cons x₂ nil) 
-- --       (ι-cons (ι-cons x₃ nil) nil))
-- --     ) nil))
-- --   ) == 
-- --        ι-cons (x₀ +  x₁                      + x₂ +  x₃                     )
-- --       (ι-cons (x₀ - (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ + (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
-- --       (ι-cons (x₀ -  x₁                      + x₂ -  x₃                     )
-- --       (ι-cons (x₀ + (x₁ * ((0 ᵣ) + (1 ᵣ) i)) - x₂ - (x₃ * ((0 ᵣ) + (1 ᵣ) i)))
-- --        nil)))
-- -- evidence-four = ?





-- FFT {ι x      } ar = vecToArr (DFT (arrToVec ar)) -- This is but a vector
-- Assume this is row major order (i.e. (nest ar) i gives this ith row of the matrix)
-- FFT {} ar = vecToArr (DFT (arrToVec ar)) -- This is but a vector
-- For the FFT, follow the wiki page on how they decompose it, idealy for the general case but can start with 2 if needed
