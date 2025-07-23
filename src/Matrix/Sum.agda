open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions
open import Algebra.Core 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app; trans)
open Eq.≡-Reasoning

open AlgebraStructures  using (IsCommutativeMonoid)

module src.Matrix.Sum {A : Set} (_⋆_ : Op₂ A) (ε : A) (isCommutativeMonoid : IsCommutativeMonoid {A = A} _≡_ _⋆_ ε) where

  open AlgebraDefinitions {A = A} _≡_

  open IsCommutativeMonoid isCommutativeMonoid using (identity; assoc; comm)

  open import Data.Product.Base using (proj₁; proj₂)


  open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
  open import Data.Fin.Base using () renaming (zero to fzero; suc to fsuc)

  open import src.Matrix using (Ar; ι; head₁; tail₁; nil; foldr; splitArₗ; splitArᵣ)
  open import src.Matrix.Equality using (_≅_; foldr-cong; reduce-≅)
  open import src.Matrix.Properties using (tail₁-const)

  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

  identityˡ : LeftIdentity ε _⋆_
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε _⋆_
  identityʳ = proj₂ identity

  sum : ∀ {m : ℕ} → (arr : Ar (ι m) A) → A
  sum {zero} arr = ε
  sum {suc m} arr = (arr (ι fzero)) ⋆ (sum ∘ tail₁) arr

  sum-nil : ∀ {n : ℕ} (arr : Ar (ι n) A) (prf : n ≡ 0) → sum arr ≡ ε
  sum-nil {zero} arr prf = refl

  sum-cong : ∀ {n : ℕ} → {xs ys : Ar (ι n) A} → xs ≅ ys → sum xs ≡ sum ys
  sum-cong {zero } {xs} {ys} prf = refl
  sum-cong {suc n} {xs} {ys} prf = cong₂ _⋆_ (prf (ι fzero)) (sum-cong {n} {tail₁ xs} {tail₁ ys} (reduce-≅ prf))

  sum-zeros : ∀ {n : ℕ} → sum {n} (λ i → ε) ≡ ε 
  sum-zeros {zero} = refl
  sum-zeros {suc n} rewrite 
      sum-cong {n} (tail₁-const {A} {n} {ε}) 
    | sum-zeros {n}
    | identityʳ ε
    = refl

  foldr-pull-out : ∀ {r : ℕ} (n m : A) (arr : Ar (ι r) A) → foldr _⋆_ (n ⋆ m) arr ≡ n ⋆ (foldr _⋆_ m arr)
  foldr-pull-out {zero} n m arr = refl
  foldr-pull-out {suc r} n m arr rewrite
      foldr-pull-out (head₁ arr) (n ⋆ m) (tail₁ arr) 
    | foldr-pull-out (head₁ arr) (m) (tail₁ arr) 
    | foldr-pull-out n m (tail₁ arr)
    | sym (assoc (arr (ι fzero)) n (foldr _⋆_ m (tail₁ arr)))
    | comm (arr (ι fzero)) n
    | assoc n (arr (ι fzero)) (foldr _⋆_ m (tail₁ arr))
    = refl

  foldr≡sum : ∀ {m : ℕ} (arr : Ar (ι m) A) → foldr {m} _⋆_ ε arr ≡ sum {m} arr
  foldr≡sum {zero} arr = refl
  foldr≡sum {suc m} arr rewrite 
      foldr-pull-out {m} (arr (ι fzero)) ε (tail₁ arr) 
    | foldr≡sum {m} (tail₁ arr)
    = refl

  split-sum : ∀ {m n : ℕ} → (arr : Ar (ι (n +ₙ m)) A) → sum arr ≡ sum (splitArₗ {n} arr) ⋆ sum (splitArᵣ {n} arr)
  split-sum {m} {zero} arr rewrite
      identityˡ (sum (splitArᵣ {0} arr)) = sum-cong {m} (λ{(ι i) → refl })
  split-sum {m} {suc n} arr rewrite
      assoc (arr (ι fzero)) (sum (tail₁ (splitArₗ {suc n} arr))) (sum (splitArᵣ {suc n} arr))
    = cong₂ _⋆_ refl 
        ( trans 
            (split-sum {m} {n} (tail₁ arr)) 
            ( cong₂ _⋆_ 
              (sum-cong {n} λ{(ι i) → refl }) 
              (sum-cong {m} λ{(ι j) → refl }) 
            )
        )
