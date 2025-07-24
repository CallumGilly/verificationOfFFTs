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


  open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties using (suc-injective) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
  open import Data.Fin.Base using (combine; Fin) renaming (zero to fzero; suc to fsuc)

  open import src.Matrix using (Ar; ι; head₁; tail₁; nil; splitArₗ; splitArᵣ; _⊗_; Position)
  open import src.Matrix.Equality using (_≅_; reduce-≅)
  open import src.Matrix.Properties using (tail₁-const)

  open import src.Reshape using (reshape; reindex; |s|≡|sᵗ|; _⟨_⟩; split; _∙_; eq)

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

  sum-length : ∀ {n m : ℕ} → {xs : Ar (ι m) A} → (prf : m ≡ n) → sum {n} (reshape (reindex prf) xs) ≡ sum {m} xs
  sum-length refl = refl

  sum-zeros : ∀ {n : ℕ} → sum {n} (λ i → ε) ≡ ε 
  sum-zeros {zero} = refl
  sum-zeros {suc n} rewrite 
      sum-cong {n} (tail₁-const {A} {n} {ε}) 
    | sum-zeros {n}
    | identityʳ ε
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




  distrib-tail₁ : ∀ {n : ℕ} (xs ys : Ar (ι (suc n)) A) → sum (tail₁ (λ i → xs i ⋆ ys i)) ≡ sum (λ i → (tail₁ xs) i ⋆ (tail₁ ys) i)
  distrib-tail₁ {n} xs ys = sum-cong {n} λ{(ι i) → refl }

  expand-sum : ∀ {n : ℕ} (xs ys : Ar (ι (n)) A) → sum (λ i → xs i ⋆ ys i) ≡ sum (λ i → xs i) ⋆ sum (λ i → ys i)
  expand-sum {zero} xs ys rewrite identityʳ ε = refl
  expand-sum {suc n} xs ys rewrite
      assoc (xs (ι fzero)) (ys (ι fzero)) (sum (tail₁ (λ i → xs i ⋆ ys i)))
    | assoc (xs (ι fzero)) (sum (tail₁ xs)) (ys (ι fzero) ⋆ sum (tail₁ ys))
    | comm  (sum (tail₁ xs)) (ys (ι fzero) ⋆ sum (tail₁ ys))
    | assoc (ys (ι fzero)) (sum (tail₁ ys)) (sum (tail₁ xs))
    | distrib-tail₁ xs ys
    | expand-sum (tail₁ xs) (tail₁ ys)
    | comm (sum (tail₁ xs)) (sum (tail₁ ys))
    = refl


  sumSwap-helperˡ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → A) → (p : Position (ι (suc n))) → tail₁ (λ i → a i p ⋆ sum (tail₁ (a i))) ≅ (λ i → (tail₁ a) i p ⋆ sum (λ j → (tail₁ ((tail₁ a) i)) j))
  sumSwap-helperˡ {m} {n} a p (ι x) = cong₂ _⋆_ refl (sum-cong {n} (λ{(ι j) → refl }))

  sumSwap-helperʳ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → A) → (p : Position (ι (suc n))) → tail₁ (λ j → a (ι fzero) j ⋆ sum (tail₁ (λ i → a i j))) ≅ (λ j → (tail₁ (a (ι fzero))) j ⋆ sum (λ i → tail₁ ((tail₁ a) i) j))
  sumSwap-helperʳ {m} {n} a p (ι x) = cong₂ _⋆_ refl (sum-cong {m} (λ{(ι i) → refl }))

  sumSwap : ∀ {m n : ℕ} → (a : Position (ι m) → Position (ι n) → A) → sum {m} (λ i → sum {n} (λ j → a i j)) ≡ sum {n} (λ j → sum {m} (λ i → a i j))
  sumSwap {zero} {n} a rewrite sum-zeros {n} = refl
  sumSwap {suc m} {zero} a rewrite
      sum-cong {m} (tail₁-const {A} {m} {ε}) 
    | sum-zeros {m} 
    | identityʳ ε = refl
  sumSwap {suc m} {suc n} a rewrite
      assoc (a (ι fzero) (ι fzero)) (sum (tail₁ (a (ι fzero))))         (sum (tail₁ (λ i → a i (ι fzero) ⋆ sum (tail₁ (a i)))))
    | assoc (a (ι fzero) (ι fzero)) (sum (tail₁ (λ i → a i (ι fzero)))) (sum (tail₁ (λ j → a (ι fzero) j ⋆ sum (tail₁ (λ i → a i j)))))
    | sum-cong (sumSwap-helperˡ a (ι fzero))
    | sum-cong (sumSwap-helperʳ a (ι fzero))
    | expand-sum (λ z → tail₁ a z (ι fzero)) (λ z → sum (tail₁ (tail₁ a z)))        -- z here is a horrible varaible name but it was auto assigned and works
    | expand-sum (tail₁ (a (ι fzero)))  (λ z → sum (λ i → (tail₁ (tail₁ a i) z)))
    | sym (assoc (sum (tail₁ (a (ι fzero))))         (sum (λ z → tail₁ a z (ι fzero))) (sum (λ z → sum (tail₁ (tail₁ a z)))))
    | sym (assoc (sum (tail₁ (λ i → a i (ι fzero)))) (sum (tail₁ (a (ι fzero))))       (sum (λ z → sum (λ i → tail₁ (tail₁ a i) z))))
    | comm (sum (tail₁ (a (ι fzero)))) (sum (λ z → tail₁ a z (ι fzero)))
    = cong₂ _⋆_ refl (cong₂ _⋆_ (cong₂ _⋆_ (sum-cong {m} (λ{(ι z) → refl })) refl) (trans (sumSwap (λ z → (tail₁ (tail₁ a z)))) refl))


  sum-reindex : ∀ {m n : ℕ} → (arr : Ar (ι m) A) → (prf : m ≡ n) → sum arr ≡ sum (reshape (reindex prf) arr)
  sum-reindex arr refl = refl

  merge-sumₗ : ∀ {m n : ℕ} → (arr : Ar (ι (suc m *ₙ suc n)) A) → (tail₁ (λ j → arr ((ι (fzero {m}) ⊗ j) ⟨ split ⟩))) ≅ (splitArₗ {n} (tail₁ arr))
  merge-sumₗ {m} {n} arr (ι i) = cong (arr ∘ ι) refl

  merge-sum  : ∀ {m n : ℕ} → (arr : Ar (ι (m *ₙ n)) A) → sum {m} (λ i → sum {n} (λ j → arr ((i ⊗ j) ⟨ split ⟩ ))) ≡ sum arr
  merge-sum {zero} {n} arr = refl
  merge-sum {suc m} {zero} arr rewrite 
      sum-nil arr (*ₙ-zeroʳ m) 
    | identityˡ (sum {m} (tail₁ (λ i → ε)))
    | sum-cong (tail₁-const {A} {m} {ε})
    | sum-zeros {m}
    = refl
  merge-sum {suc m} {suc n} arr 
    rewrite split-sum {m *ₙ suc n} {n} (tail₁ arr) rewrite 
        sym (assoc (arr (ι fzero)) (sum (splitArₗ {n} (tail₁ arr))) (sum (splitArᵣ {n} (tail₁ arr))))
      | sum-cong (merge-sumₗ {m} {n} arr)
      = cong₂ _⋆_ refl 
        (trans 
          (sum-cong {m} (λ{ (ι i) → cong₂ _⋆_ refl (sum-cong {n} (λ{(ι j) → refl})) }))
          (merge-sum {m} {suc n} (splitArᵣ {n} (tail₁ arr)))
        )

















