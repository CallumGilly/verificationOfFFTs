open import src.Real using (Real)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Function using (_∘_)

open import Data.Product using (∃; ∃-syntax)
 
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

module src.Complex (r : Real) where
  open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ; +ᵣ-identityʳ; *ᵣ-comm; *ᵣ-assoc; neg-distrib-*)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)

  infixl 7 _*_
  infixl 6 _+_ _-_

  record ℂ : Set where
    constructor _+_i
    field
      real      : ℝ
      imaginary : ℝ
  
  RealPart      : ℂ → ℝ
  RealPart      = ℂ.real
  ImaginaryPart : ℂ → ℝ
  ImaginaryPart = ℂ.imaginary

  fromℝ : ℝ → ℂ
  fromℝ x = x + (0 ᵣ) i

  ℂfromℕ : ℕ → ℂ
  ℂfromℕ = fromℝ ∘ _ᵣ

  _+_ : ℂ → ℂ → ℂ
  (xRe + xIm i) + (yRe + yIm i) = (xRe +ᵣ yRe) + (xIm +ᵣ yIm) i
  --x + y = (RealPart x +ᵣ RealPart y) + (ImaginaryPart x +ᵣ ImaginaryPart y) i

  _-_ : ℂ → ℂ → ℂ
  (xRe + xIm i) - (yRe + yIm i) = (xRe -ᵣ yRe) + (xIm -ᵣ yIm) i

  _*_ : ℂ → ℂ → ℂ
  (xRe + xIm i) * (yRe + yIm i) = ((xRe *ᵣ yRe) -ᵣ (xIm *ᵣ yIm)) + ((xRe *ᵣ yIm) +ᵣ (xIm *ᵣ yRe)) i

  *-identityʳ : ∀ {n : ℂ} → n * (ℂfromℕ 1) ≡ n
  *-identityʳ {real + imaginary i} =
    begin
      (real + imaginary i) * ℂfromℕ 1
    ≡⟨⟩
      (real + imaginary i) * ((1 ᵣ) + (0 ᵣ) i)
    ≡⟨⟩
      ((real *ᵣ 1 ᵣ) -ᵣ (imaginary *ᵣ 0 ᵣ)) + ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong (_+ ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i) (cong (λ x → (real *ᵣ 1 ᵣ) -ᵣ x) (*ᵣ-zeroᵣ (imaginary))) ⟩
      ((real *ᵣ 1 ᵣ) -ᵣ (0 ᵣ)) + ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong (_+ ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i) (-ᵣ-identityʳ (real *ᵣ 1 ᵣ)) ⟩
      (real *ᵣ 1 ᵣ) + ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong ((real *ᵣ 1 ᵣ) +_i) (cong (_+ᵣ (imaginary *ᵣ 1 ᵣ)) (*ᵣ-zeroᵣ (real))) ⟩
      (real *ᵣ 1 ᵣ) + ((0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong ((real *ᵣ 1 ᵣ) +_i) (+ᵣ-identityˡ (imaginary *ᵣ 1 ᵣ)) ⟩
      (real *ᵣ 1 ᵣ) + ((imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong ((real *ᵣ 1 ᵣ) +_i) (*ᵣ-identityʳ imaginary) ⟩
      (real *ᵣ 1 ᵣ) + imaginary i
    ≡⟨ cong (_+ imaginary i) (*ᵣ-identityʳ real) ⟩
      real + imaginary i
    ∎

  +-identityʳ : ∀ {n : ℂ} → n + (ℂfromℕ 0) ≡ n 
  +-identityʳ {real + imaginary i} rewrite +ᵣ-identityʳ real | +ᵣ-identityʳ imaginary = refl
    -- begin 
    --   (real + imaginary i) + ℂfromℕ 0
    -- ≡⟨⟩
    --   (real + imaginary i) + ((0 ᵣ) + (0 ᵣ) i)
    -- ≡⟨⟩
    --   ((real +ᵣ (0 ᵣ)) + (imaginary +ᵣ (0 ᵣ)) i)
    -- ≡⟨ cong ( (real +ᵣ (0 ᵣ)) +_i ) (+ᵣ-identityʳ imaginary) ⟩
    --   ?
  -- (xRe + xIm i) + (yRe + yIm i) = (xRe +ᵣ yRe) + (xIm +ᵣ yIm) i

  -- Eulers Formula
  e^i_ : ℝ → ℂ
  e^i_ x = (cos x) + (sin x) i


  postulate
    e^0 : e^i (0 ᵣ) ≡ ℂfromℕ 1 
    e^i[-π] : e^i (-ᵣ π) ≡ (-ᵣ (1 ᵣ)) + (0 ᵣ) i

  ℂ-conjugate : ℂ → ℂ
  ℂ-conjugate (real + imaginary i) = real + (-ᵣ imaginary) i

  -- Explicitly states which complex roots are positive and which are negative
  +ω : ∀ (N : ℕ) (k : ℕ) → ℂ
  +ω N k = e^i (((2 ᵣ) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

  -ω : ∀ (N : ℕ) (k : ℕ) → ℂ
  -ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

  ω-N-0 : ∀ {N : ℕ} → -ω N 0 ≡ ℂfromℕ 1
  ω-N-0 {N} =
    begin
      -ω N 0
    ≡⟨⟩
      e^i (((-ᵣ 2 ᵣ *ᵣ π) *ᵣ (0 ᵣ)) /ᵣ (N ᵣ))
    ≡⟨ cong (e^i_) (cong (_/ᵣ (N ᵣ)) (*ᵣ-zeroᵣ (-ᵣ 2 ᵣ *ᵣ π))) ⟩
      e^i ((0 ᵣ) /ᵣ (N ᵣ))
    ≡⟨ cong (e^i_) (/ᵣ-zeroₜ (N ᵣ)) ⟩
      e^i (0 ᵣ)
    ≡⟨ e^0 ⟩
      ℂfromℕ 1
    ∎

  postulate
    ᵣ-distributes-*ₙ : ∀ (n m : ℕ) → (n *ₙ m) ᵣ ≡ (n ᵣ) *ᵣ (m ᵣ)
    *ᵣ-distributes-/ᵣ : ∀ (m n o : ℝ) → (m *ᵣ n) /ᵣ o ≡ m *ᵣ (n /ᵣ o)
    N-/ᵣ-N : ∀ (n : ℝ) → n /ᵣ n ≡ 1 ᵣ
    sin-2nπ : ∀ (n : ℕ) → sin (π *ᵣ (-ᵣ (n ᵣ))) ≡ 0 ᵣ
    cos-2nπ : ∀ (n : ℕ) → ∃[ m ] ( 2 *ₙ m ≡ n ) → cos (π *ᵣ (-ᵣ (n ᵣ))) ≡ 1 ᵣ

  --*ᵣ-comm : ∀ (m n : ℝ) → (m *ᵣ n) ≡ (n *ᵣ m) 
  --*ᵣ-assoc : ∀ (m n o : ℝ) → (m *ᵣ n) *ᵣ o ≡ m *ᵣ (n *ᵣ o)
  ---ᵣ-distributes-*ᵣ : ∀ (n m : ℝ) → (-ᵣ n) *ᵣ m ≡ -ᵣ (n *ᵣ m)

  -- I feel like this is a questionable use or rewrite, I kind of wish I'd kept each stage in comments next to each step at least ... but it works
  ω-N-mN : ∀ {N m : ℕ} → -ω N (N *ₙ m) ≡ ℂfromℕ 1
  ω-N-mN {N} {m} rewrite 
      ᵣ-distributes-*ₙ N m 
    | *ᵣ-comm (N ᵣ) (m ᵣ) 
    | sym (*ᵣ-assoc ((-ᵣ (2 ᵣ)) *ᵣ π) (m ᵣ) (N ᵣ))
    | *ᵣ-distributes-/ᵣ (((-ᵣ (2 ᵣ)) *ᵣ π) *ᵣ (m ᵣ)) (N ᵣ) (N ᵣ)
    | N-/ᵣ-N (N ᵣ)
    | *ᵣ-identityʳ (((-ᵣ (2 ᵣ)) *ᵣ π) *ᵣ (m ᵣ))
    | *ᵣ-comm (-ᵣ 2 ᵣ) π
    | *ᵣ-assoc π (-ᵣ 2 ᵣ) (m ᵣ)
    | neg-distrib-* (2 ᵣ) (m ᵣ)
    | sym (ᵣ-distributes-*ₙ 2 m) 
    | cos-2nπ (2 *ₙ m) ⟨ m , refl ⟩
    | sin-2nπ (2 *ₙ m)   = refl
    --    | e^i2nπ (2 *ₙ m) ⟨ m , refl ⟩ = refl

--  ω-multi : ∀ {N₁ N₂ k₁ k₂ : ℕ} → (-ω (N₁ *ₙ N₂) (k₁ *ₙ k₂)) ≡ (-ω N₁ k₁) * (-ω N₂ k₂)
--  ω-multi {N₁} {N₂} {k₁} {k₂} =
--    begin
--      -ω (N₁ *ₙ N₂) (k₁ *ₙ k₂)
--    ≡⟨⟩
--      e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ ((k₁ *ₙ k₂) ᵣ)) /ᵣ ((N₁ *ₙ N₂) ᵣ))
--    ≡⟨⟩
--      ?















