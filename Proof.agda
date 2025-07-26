open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning

module Proof (real : Real) (cplx : Cplx real) where

open Real real using (_ᵣ; ℝ)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_; *-comm to *ᵣ-comm; *-identityʳ to *ᵣ-identityʳ)
open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

open AlgebraStructures  {A = ℂ} _≡_
open AlgebraDefinitions {A = ℂ} _≡_

open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid; distribˡ; *-comm; zeroʳ; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

open import Data.Nat.Base using (ℕ; zero; suc; NonZero; _≡ᵇ_) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (suc-injective; m*n≢0; m*n≢0⇒m≢0; m*n≢0⇒n≢0) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
  +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)
open import Data.Bool using (Bool; true; false; not)
open import Data.Bool using (T)

open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂ )
open import Data.Unit using (⊤; tt)

open import Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; length; splitAr; splitArₗ; splitArᵣ; NonZeroₛ; s⊗p-nonZeroₛ⇒p-nonZeroₛ; s⊗p-nonZeroₛ⇒s-nonZeroₛ; s⊗p-nonZeroₛ)
open import Matrix.Equality using (_≅_; reduce-≅; tail₁-cong)
open import Matrix.Properties using (splitArᵣ-zero; tail₁-const; zipWith-congˡ)

import Matrix.Sum as S
open S _+_ 0ℂ +-isCommutativeMonoid using (merge-sum; sum-reindex; sum-swap)
sum = S.sum _+_ 0ℂ +-isCommutativeMonoid
{-# DISPLAY S.sum _+_ 0ℂ +-isCommutativeMonoid = sum #-}
sum-cong = S.sum-cong _+_ 0ℂ +-isCommutativeMonoid

open import Matrix.Reshape using (reshape; Reshape; flat; ♭; ♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; reindex; rev-eq; flatten-reindex; |s|≡|sᵗ|; reindex-reindex; s-nonZeroₛ⇒sᵗ-nonZeroₛ)
open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

open import FFT real cplx using (DFT; FFT; offset-prod; iota; twiddles)

private
  variable
    s r₁ r₂ : Shape
    N M : ℕ

rev-eq-applied : (rshp : Reshape r₂ r₁) (arr : Ar r₁ ℂ) → reshape (rshp ∙ rev rshp) arr ≅ arr 
rev-eq-applied rshp arr i = cong arr (rev-eq rshp i)

--------------------------
--- Properties of iota ---
--------------------------

iota-reindex : ∀ {i : Position (ι N)} → (prf : M ≡ N) → iota (i ⟨ reindex prf ⟩) ≡ iota i
iota-reindex refl = refl

iota-split : ∀ 
   (k₀   : Position (ι (length r₂)))
   (k₁   : Position (ι (length r₁)))
   → iota ((k₁ ⊗ k₀) ⟨ split ⟩) ≡ (length r₂ *ₙ iota k₁) +ₙ iota k₀
iota-split (ι k₀) (ι k₁) rewrite toℕ-combine k₁ k₀ = refl

--⊤-true-irrelevant : ∀ {x y : ⊤ true} → x ≡ y

nonZero-eq : ∀ {n : ℕ} → (x y : NonZero n) → x ≡ y
nonZero-eq {n} record { nonZero = nonZero-x } record { nonZero = nonZero-y } 
  = cong (λ p → record { nonZero = p }) (?)


-ω-cong₂ : 
  ∀ {n m : ℕ} 
  → ⦃ nonZero-n : NonZero n ⦄
  → ⦃ nonZero-m : NonZero m ⦄
  → ∀ {k j : ℕ} 
  → (prfₗ : n ≡ m)
  → k ≡ j 
  → -ω n k ≡ -ω m j
-ω-cong₂ {n} {m} ⦃ nonZero-n ⦄ ⦃ nonZero-m ⦄ {k} {j} refl refl = 
  begin
    -ω n ⦃ nonZero-n ⦄ k
  ≡⟨ cong (λ f → -ω n ⦃ f ⦄ k) (nonZero-eq nonZero-n nonZero-m) ⟩
    -ω n ⦃ nonZero-m ⦄ k
  ∎

---------------------------------
--- Properties of DFT and FFT ---
---------------------------------

DFT-cong : ∀ {xs ys : Ar (ι N) ℂ} ⦃ nonZero-N : NonZero N ⦄ → xs ≅ ys → DFT xs ≅ DFT ys
DFT-cong {N} {xs} {ys} prf (ι j) = sum-cong {N} (λ i → cong₂ _*_ (prf i) refl)

FFT-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → ⦃ nonZeroₛ-s : NonZeroₛ s ⦄ → xs ≅ ys → FFT ⦃ nonZeroₛ-s ⦄ xs ≅ FFT ⦃ nonZeroₛ-s ⦄ ys
FFT-cong {ι N} {xs} {ys} ⦃ nonZero-s ⦄ prf j = 
  let instance
    _ : NonZero N
    _ = nonZero-s .NonZeroₛ.nonZeroₛ
  in DFT-cong prf j
FFT-cong {r₁ ⊗ r₂} {xs} {ys} ⦃ nonZero-r₁⊗r₂ ⦄ prf (j₁ ⊗ j₀) = 
  let instance
    nonZeroₛ-r₁ : NonZeroₛ r₁
    nonZeroₛ-r₁ = s⊗p-nonZeroₛ⇒s-nonZeroₛ ⦃ nonZero-r₁⊗r₂ ⦄
    nonZeroₛ-r₂ : NonZeroₛ r₂
    nonZeroₛ-r₂ = s⊗p-nonZeroₛ⇒p-nonZeroₛ ⦃ nonZero-r₁⊗r₂ ⦄
  in (FFT-cong {r₂} ⦃ nonZeroₛ-r₂ ⦄ λ{ k₀ → (cong₂ _*_ ((FFT-cong {r₁} ⦃ nonZeroₛ-r₁ ⦄ λ{k₁ → prf (k₁ ⊗ k₀) }) j₀ ) refl) }) j₁

-------------------------
--- Properties of Sum ---
-------------------------

-- Of note here is that I cannot put this in the sum module as it requires knowlage of _+_ as well as its relation with _+_

*-distribˡ-sum : {xs : Ar (ι N) ℂ} (x : ℂ) → x * (sum xs) ≡ sum (map (x *_) xs)
*-distribˡ-sum {zero} {xs} x = zeroʳ x
*-distribˡ-sum {suc N} {xs} x rewrite 
    distribˡ x (xs (ι fzero)) (sum (tail₁ xs)) 
  | *-distribˡ-sum {N} {tail₁ xs} x 
  = cong₂ _+_ refl (sum-cong {N} (λ{(ι i) → refl }))

*-distribʳ-sum : {xs : Ar (ι N) ℂ} (x : ℂ) → (sum xs) * x ≡ sum (map (_* x) xs)
*-distribʳ-sum {N} {xs} x rewrite
    *-comm (sum xs) x
  | *-distribˡ-sum {N} {xs} x
  = sum-cong {N} λ i → *-comm x (xs i)

------------------------------------
--- Rearanging of roots of unity ---
------------------------------------

-ω-rearanging : ∀
   (j₁   : Position (recursive-transpose r₂))
   (j₀   : Position (recursive-transpose r₁))
   (k₀   : Position (ι (length (recursive-transpose r₂))))
   (k₁   : Position (ι (length (recursive-transpose r₁))))
   → ⦃ nonZero-r₁ᵗ     : NonZero (                                   length (recursive-transpose r₁)) ⦄
   → ⦃ nonZero-r₂*r₁ᵗ  : NonZero (length                      r₂  *ₙ length (recursive-transpose r₁)) ⦄
   → ⦃ nonZero-r₂ᵗ     : NonZero (length (recursive-transpose r₂)                                   ) ⦄
   → ⦃ nonZero-r₂ᵗ*r₁ᵗ : NonZero (length (recursive-transpose r₂) *ₙ length (recursive-transpose r₁)) ⦄ 
   → ⦃ nonZero-r₁ᵗ*r₂ᵗ : NonZero (length (recursive-transpose r₁) *ₙ length (recursive-transpose r₂)) ⦄ -- This could be optimised down to two or even one, we'll see
   → 
        -ω 
          (length (recursive-transpose r₁)) 
          (iota k₁ *ₙ iota (j₀ ⟨ rev ♭ ⟩)) 
      * -ω 
          (length r₂ *ₙ length (recursive-transpose r₁))
          (iota (((k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) ⟨ ♭ ⟩) ⟨ rev (♭ {r₂}) ⟩) *ₙ iota (j₀ ⟨ rev ♭ ⟩)) 
      * -ω 
          (length (recursive-transpose r₂)) 
          (iota k₀ *ₙ iota (j₁ ⟨ rev ♭ ⟩))
      ≡
        -ω 
          (length (recursive-transpose r₂) *ₙ length (recursive-transpose r₁))
          (iota (((k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩) ⊗ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩)) ⟨ split ⟩) *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
-ω-rearanging {r₂} {r₁} j₁ j₀ k₀ k₁ =
  begin
  _ ≡⟨ cong₂ _*_ (cong₂ _*_ refl (-ω-cong₂ (cong₂ _*ₙ_ (|s|≡|sᵗ| {r₂}) refl) refl)) refl ⟩
  _ ≡⟨ cong₂ _*_ (cong₂ _*_ refl (-ω-cong₂ refl (cong₂ _*ₙ_ (cong iota (rev-eq {r₂} ♭ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩))) refl))) refl ⟩
  _ ≡⟨ cong₂ _*_ (cong₂ _*_ refl (-ω-cong₂ refl (cong₂ _*ₙ_ (iota-reindex (|s|≡|sᵗ| {r₂})) refl))) refl ⟩
  _ ≡⟨ -ω-rearanging′ (length (recursive-transpose r₁)) (length (recursive-transpose r₂)) (iota k₀) (iota k₁) (iota (j₀ ⟨ rev ♭ ⟩)) (iota (j₁ ⟨ rev ♭ ⟩)) ⟩
  _ ≡⟨ sym (-ω-cong₂ refl 
          (cong (_*ₙ (length (recursive-transpose r₁) *ₙ iota (j₁ ⟨ rev ♭ ⟩) +ₙ iota (j₀ ⟨ rev ♭ ⟩))) 
            (cong ((length (recursive-transpose r₂) *ₙ iota k₁ +ₙ_))
              (iota-reindex (|s|≡|sᵗ| {r₂}))
            )
          )
         ) 
   ⟩
  _ ≡⟨ sym (-ω-cong₂ refl 
          (cong (_*ₙ (length (recursive-transpose r₁) *ₙ iota (j₁ ⟨ rev ♭ ⟩) +ₙ iota (j₀ ⟨ rev ♭ ⟩))) 
            (cong (_+ₙ iota (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩)) 
              (cong (length (recursive-transpose r₂) *ₙ_) (iota-reindex {length (recursive-transpose r₁)} {length r₁} {k₁} (|s|≡|sᵗ| {r₁})))
            )
          )
         ) 
   ⟩
  _ ≡⟨ sym (-ω-cong₂ refl (cong₂ _*ₙ_ (cong₂ _+ₙ_ (cong₂ _*ₙ_ (|s|≡|sᵗ| {r₂}) refl) refl) refl)) ⟩
  _ ≡⟨ sym (-ω-cong₂ refl 
              (cong₂ _*ₙ_ 
                  (iota-split 
                    {r₂} 
                    {r₁} 
                    (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) 
                    (k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩)
                  ) 
                  (iota-split 
                    {ι (length (recursive-transpose r₁))} 
                    {ι (length (recursive-transpose r₂))} 
                    (j₀ ⟨ rev ♭ ⟩) 
                    (j₁ ⟨ rev ♭ ⟩)
                  )
              )
            ) 
      ⟩ 
  _ ∎
  where
    -ω-rearanging′ : 
      ∀ (r₁ r₂ k₀ k₁ j₀ j₁ : ℕ) 
      → ⦃ nonZero-r₁   : NonZero r₁         ⦄
      → ⦃ nonZero-r₂   : NonZero r₂         ⦄
      → ⦃ nonZero-r₂r₁ : NonZero (r₂ *ₙ r₁) ⦄
      → ⦃ nonZero-r₁r₂ : NonZero (r₁ *ₙ r₂) ⦄
      → 
                  -ω (r₁) (k₁ *ₙ j₀) 
                * -ω (r₂ *ₙ r₁) (k₀ *ₙ j₀) 
                * -ω (r₂) (k₀ *ₙ j₁)
                ≡
                -ω 
                  (r₂ *ₙ r₁) 
                  (
                    (r₂ *ₙ k₁ +ₙ k₀) 
                    *ₙ 
                    (r₁ *ₙ j₁ +ₙ j₀) 
                  )
    -ω-rearanging′ r₁ r₂ k₀ k₁ j₀ j₁ rewrite
        sym (ω-r₁x-r₁y r₂ r₁ (k₁ *ₙ j₀)) 
      | sym (ω-r₁x-r₁y r₁ r₂ (k₀ *ₙ j₁)) 
      | sym (*-identityʳ (-ω (r₂ *ₙ r₁) (r₂ *ₙ (k₁ *ₙ j₀)) * -ω (r₂ *ₙ r₁) (k₀ *ₙ j₀) * -ω (r₁ *ₙ r₂) (r₁ *ₙ (k₀ *ₙ j₁))))
      | sym (ω-N-mN {r₁} {j₁ *ₙ k₁}) 
      | sym (ω-r₁x-r₁y r₂ r₁ (r₁ *ₙ (j₁ *ₙ k₁))) 
      -- | *ₙ-comm r₂ r₁
      --| sym (ω-N-k₀+k₁ {r₁ *ₙ r₂} {r₂ *ₙ (k₁ *ₙ j₀)} {k₀ *ₙ j₀})
      --| sym (ω-N-k₀+k₁ {r₁ *ₙ r₂} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀} {r₁ *ₙ (k₀ *ₙ j₁)})
      --| sym (ω-N-k₀+k₁ {r₁ *ₙ r₂} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀ +ₙ r₁ *ₙ (k₀ *ₙ j₁)} {r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))})
      = ? -- cong₂ -ω refl (solve 6 (λ r₁ℕ r₂ℕ k₀ℕ k₁ℕ j₀ℕ j₁ℕ → r₂ℕ :* (k₁ℕ :* j₀ℕ) :+ k₀ℕ :* j₀ℕ :+ r₁ℕ :* (k₀ℕ :* j₁ℕ) :+ r₂ℕ :* (r₁ℕ :* (j₁ℕ :* k₁ℕ)) := (r₂ℕ :* k₁ℕ :+ k₀ℕ) :* (r₁ℕ :* j₁ℕ :+ j₀ℕ)) refl r₁ r₂ k₀ k₁ j₀ j₁)
  
-------------------------------------------
--- 4 way associativity helper function ---
-------------------------------------------

assoc₄ : (a b c d : ℂ) → a * b * c * d ≡ a * (b * c * d)
assoc₄ a b c d rewrite
    *-assoc a b c
  | *-assoc a (b * c) d
  = refl

-----------------
--- FFT ≡ DFT ---
-----------------

fft≅dft : 
    ⦃ nonZeroₛ-s  : NonZeroₛ s ⦄ 
  → ∀ (arr : Ar s ℂ) 
  → FFT ⦃ nonZeroₛ-s ⦄ arr 
    ≅ 
    ( (reshape ♯) 
    ∘ (DFT ⦃ s-nonZeroₛ⇒sᵗ-nonZeroₛ ⦃ nonZeroₛ-s ⦄ .NonZeroₛ.nonZeroₛ ⦄ )
    ∘ (reshape flatten-reindex)) arr
fft≅dft {ι N    } arr  i = refl
fft≅dft {r₁ ⊗ r₂} ⦃ record { nonZeroₛ = nonZero-|r₁⊗r₂| } ⦄ arr (j₁ ⊗ j₀) = 
  let instance
    nonZero-|r₁|  : NonZero (length r₁)
    nonZero-|r₁|  = m*n≢0⇒m≢0 (length r₁) ⦃ nonZero-|r₁⊗r₂| ⦄ 
    nonZero-|r₂|  : NonZero (length r₂)
    nonZero-|r₂|  = m*n≢0⇒n≢0 (length r₁) ⦃ nonZero-|r₁⊗r₂| ⦄
    nonZero-|r₁ᵗ| : NonZero (length (recursive-transpose r₁))
    nonZero-|r₁ᵗ| = s-nonZeroₛ⇒sᵗ-nonZeroₛ {r₁} .NonZeroₛ.nonZeroₛ
    nonZero-|r₂ᵗ| : NonZero (length (recursive-transpose r₂))
    nonZero-|r₂ᵗ| = s-nonZeroₛ⇒sᵗ-nonZeroₛ {r₂} .NonZeroₛ.nonZeroₛ
    nonZero-|r₁ᵗ⊗r₂ᵗ| : NonZero (length (recursive-transpose r₁) *ₙ length (recursive-transpose r₂))
    nonZero-|r₁ᵗ⊗r₂ᵗ| = (s⊗p-nonZeroₛ {ι (length (recursive-transpose r₁))} {ι (length (recursive-transpose r₂))}) .NonZeroₛ.nonZeroₛ
    nonZero-|r₂ᵗ⊗r₁ᵗ| : NonZero (length (recursive-transpose r₂) *ₙ length (recursive-transpose r₁))
    nonZero-|r₂ᵗ⊗r₁ᵗ| = (s⊗p-nonZeroₛ {ι (length (recursive-transpose r₂))} {ι (length (recursive-transpose r₁))}) .NonZeroₛ.nonZeroₛ
    nonZero-|r₂⊗r₁ᵗ| : NonZero (length r₂ *ₙ length (recursive-transpose r₁))
    nonZero-|r₂⊗r₁ᵗ| = m*n≢0 (length r₂) (length (recursive-transpose r₁))
  in
  begin
    _ ≡⟨ fft≅dft _ j₁ ⟩
    _ ≡⟨ DFT-cong (λ x → cong₂ _*_ (fft≅dft _ j₀) refl) (j₁ ⟨ rev ♭ ⟩ ) ⟩
    _ ≡⟨ sum-cong {length (recursive-transpose r₂)} (λ k₀ → cong₂ _*_ (*-distribʳ-sum {length (recursive-transpose r₁)} _) refl ) ⟩
    _ ≡⟨ sum-cong {length (recursive-transpose r₂)} (λ k₀ →            *-distribʳ-sum {length (recursive-transpose r₁)} _)        ⟩ 
    _ ≡⟨ sum-cong {  length (recursive-transpose r₂) } 
          (λ k₀ → 
            sum-cong {length (recursive-transpose r₁) }
              (λ k₁ → 
                assoc₄
                    (arr (((k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩) ⟨ ♭ ⟩) ⊗ ((k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) ⟨ ♭ ⟩)))
                    (-ω (length (recursive-transpose r₁)) (iota k₁ *ₙ iota (j₀ ⟨ rev ♭ ⟩)))
                    (-ω (length r₂ *ₙ length (recursive-transpose r₁)) (iota (((k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) ⟨ ♭ ⟩) ⟨ rev (♭ {r₂}) ⟩) *ₙ iota (j₀ ⟨ rev ♭ ⟩)))
                    (-ω (length (recursive-transpose r₂)) (iota k₀ *ₙ iota (j₁ ⟨ rev ♭ ⟩)))
              )
          )
      ⟩
    _ ≡⟨ sum-cong {  length (recursive-transpose r₂) } 
          (λ k₀ → 
            sum-cong {length (recursive-transpose r₁) }
              (λ k₁ →
                cong₂ _*_ refl (-ω-rearanging j₁ j₀ k₀ k₁)
              )
          )
      ⟩
    _ ≡⟨ sum-cong { length (recursive-transpose r₂) } 
          (λ k₀ → 
            sum-cong { length (recursive-transpose r₁) }
              (λ k₁ → 
                cong₂ _*_ (sym ((rev-eq-applied split (reshape (♭ ⊕ ♭) arr)) ((k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩) ⊗ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩))) ) refl
              )
          ) 
      ⟩
    _ ≡⟨ sum-cong {length (recursive-transpose r₂)} (λ k₀ → sym (sum-reindex (|s|≡|sᵗ| {r₁}))) ⟩
    _ ≡⟨ sym (sum-reindex (|s|≡|sᵗ| {r₂})) ⟩
    _ ≡⟨ sum-swap {length r₂} {length r₁} _ ⟩
    _ ≡⟨ merge-sum {length r₁} {length r₂} _ ⟩
          sum { length r₁ *ₙ length r₂ }
            (λ k →
                 arr (((k) ⟨ flat ⟩) ⟨ ♭ ⊕ ♭ ⟩)
               *
                 -ω
                   (length (recursive-transpose r₂) *ₙ length (recursive-transpose r₁))
                   (iota k *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
            )
      ≡⟨ sum-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂}) ⟩
    _ ≡⟨ sum-cong 
        {length (recursive-transpose (r₁ ⊗ r₂))} 
        (λ{(ι k) → 
            cong₂ _*_ 
              refl 
              (-ω-cong₂ 
                {length (recursive-transpose r₂) *ₙ length (recursive-transpose r₁)} 
                {length (recursive-transpose r₂) *ₙ length (recursive-transpose r₁) } 
                ⦃ m*n≢0 (length (recursive-transpose r₂)) (length (ι (length (recursive-transpose r₁)))) ⦄
                ⦃ ? ⦄
                {?} 
                {?} 
                refl 
                ?
                --refl 
                --(cong₂ _*ₙ_ (iota-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂})) refl)
              )
          }) 
      ⟩
    _ ∎
