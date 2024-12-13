open import src.Real using (Real)

module src.ComplexMatrix (r : Real) where

open import src.Complex r using (ℂ; ℂfromℕ; _+_; _-_; _*_; ω; *-identityʳ; ω-N-0; +-identityʳ)
open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; nest; map; foldr; unnest; ι-cons; nil; _==_; zip; iterate; head₁; tail₁)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open import Data.Fin.Base using (Fin; toℕ; splitAt) renaming (zero to fzero; suc to fsuc)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

-- pairWithIndex : ∀ {m : ℕ} {X : Set} → Ar (ι m) X → Ar (ι m) (ℕ × X)
-- pairWithIndex arr (ι p) = ⟨ (toℕ p) , arr (ι p) ⟩
-- 
-- 
-- sigma : ∀ {m : ℕ} {X : Set} → Ar (ι m) X → ((ℕ × X) → ℂ) → ℂ 
-- sigma {m} {X} arr f = foldr (_+_ ∘ f) (ℂfromℕ 0) (pairWithIndex arr)

toIndexArr : ∀ {m : ℕ} {X : Set} →  Ar (ι m) X → Ar (ι m) (Position (ι m))
toIndexArr arr (ι p) = ι p

sigma : ∀ {m : ℕ} {X : Set} → Ar (ι m) X → (Ar (ι m) X → Position (ι m) → ℂ ) → ℂ
sigma ar f = foldr (_+_ ∘ (f ar)) (ℂfromℕ 0) (toIndexArr ar)

--- If I'd implemented fold in a different way, I could use the below definition which is more general?
--sigma : ∀ {shape : Shape} {X : Set} → Ar shape X → (Ar shape X → Position shape → ℂ ) → ℂ
--sigma ar f = foldr (_+_ ∘ (f ar)) (ℂfromℕ 0) (toIndexArr ar)

-- foldr : ∀ {n : ℕ} {X Y : Set} → (X → Y → Y) → Y → Ar (ι n) X → Y
-- foldr {zero } f acc ar = acc
-- foldr {suc n} f acc ar = foldr f (f (head₁ ar) acc) (tail₁ ar)

tmp : ℕ × ℕ → ℂ
tmp ⟨ fst , snd ⟩ = ℂfromℕ (snd *ₙ fst)

tmp₂ : ∀ {m : ℕ} → Ar (ι m) ℕ → Position (ι m) → ℂ
tmp₂ arr (ι p) = ℂfromℕ (arr (ι p) *ₙ (toℕ p))

test₂ : sigma {2} {ℕ} (ι-cons 3 (ι-cons 3 nil)) tmp₂ ≡ ℂfromℕ 3
test₂ =
  begin
    sigma (ι-cons 3 (ι-cons 3 nil)) tmp₂
  ≡⟨⟩
    foldr (_+_ ∘ (tmp₂ (ι-cons 3 (ι-cons 3 nil)))) (ℂfromℕ 0) (toIndexArr (ι-cons 3 (ι-cons 3 nil)))
  ≡⟨⟩
       ℂfromℕ (3 *ₙ 1)
    + (ℂfromℕ 0 
    +  ℂfromℕ 0)
  ≡⟨ cong ((ℂfromℕ (3 *ₙ 1)) +_) +-identityʳ ⟩
       ℂfromℕ (3 *ₙ 1)
    + ℂfromℕ 0 
  ≡⟨ +-identityʳ ⟩
    ℂfromℕ (3 *ₙ 1)
  ≡⟨⟩
    ℂfromℕ 3
  ∎

-- test : sigma {2} {ℕ} (ι-cons 3 (ι-cons 3 nil)) tmp ≡ ℂfromℕ 3
-- test =
--   begin
--     sigma (ι-cons 3 (ι-cons 3 nil)) tmp
--   ≡⟨⟩
--     foldr (_+_ ∘ tmp) (ℂfromℕ 0) (pairWithIndex (ι-cons 3 (ι-cons 3 nil)))
--   ≡⟨⟩
--     foldr (_+_ ∘ tmp) (ℂfromℕ 0) ((ι-cons ⟨ 0 , 3 ⟩ (ι-cons ⟨ 1 , 3 ⟩ nil)))
--   ≡⟨⟩
--         tmp ⟨ 1 , 3 ⟩ 
--     + ((tmp ⟨ 0 , 3 ⟩)
--     + ℂfromℕ 0)
--   ≡⟨⟩
--        ℂfromℕ (3 *ₙ 1)
--     + (ℂfromℕ (3 *ₙ 0) 
--     +  ℂfromℕ 0)
--   ≡⟨⟩
--        ℂfromℕ (3 *ₙ 1)
--     + (ℂfromℕ 0 
--     +  ℂfromℕ 0)
--   ≡⟨⟩
--        ℂfromℕ (3 *ₙ 1)
--     + (ℂfromℕ 0 
--     +  ℂfromℕ 0)
--   ≡⟨ cong ((ℂfromℕ (3 *ₙ 1)) +_) +-identityʳ ⟩
--        ℂfromℕ (3 *ₙ 1)
--     + ℂfromℕ 0 
--   ≡⟨ +-identityʳ ⟩
--     ℂfromℕ (3 *ₙ 1)
--   ≡⟨⟩
--     ℂfromℕ 3
--   ∎
