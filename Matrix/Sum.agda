import Algebra.Structures as AlgebraStructures
open AlgebraStructures  using (IsCommutativeMonoid)
import Algebra.Definitions as AlgebraDefinitions
open import Algebra.Core 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app; trans)
open Eq.≡-Reasoning


module Matrix.Sum {A : Set} (_⋆_ : Op₂ A) (ε : A) (isCommutativeMonoid : IsCommutativeMonoid {A = A} _≡_ _⋆_ ε) where

  open import Data.Product.Base using (proj₁; proj₂)

  open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (*-zeroʳ)
  open import Data.Fin.Base using () renaming (zero to fzero; suc to fsuc)

  open import Matrix using (Ar; Position; ι; _⊗_; head₁; tail₁; splitArₗ; splitArᵣ)
  open import Matrix.Equality using (_≅_; reduce-≅)
  open import Matrix.Properties using (tail₁-const)

  open import Matrix.Reshape using (reshape; reindex; |s|≡|sᵗ|; _⟨_⟩; split; _∙_; eq)

  open import Function.Base using (_$_; _∘_)

  -----------------------------------------
  --- Pull out properties of the monoid ---
  -----------------------------------------

  open AlgebraDefinitions {A = A} _≡_

  open IsCommutativeMonoid isCommutativeMonoid using (identity; assoc; comm)


  private
    identityˡ : LeftIdentity ε _⋆_
    identityˡ = proj₁ identity

    identityʳ : RightIdentity ε _⋆_
    identityʳ = proj₂ identity

    variable
      n m : ℕ

  ----------------------
  --- Sum Definition ---
  ----------------------

  sum : (xs : Ar (ι n) A) → A
  sum {zero} xs = ε
  sum {suc n} xs = (xs (ι fzero)) ⋆ (sum ∘ tail₁) xs


  ----------------------------
  --- Basic Sum Properties ---
  ----------------------------

  sum-nil : 
    ∀ (xs : Ar (ι n) A) 
      (prf : n ≡ 0) 
      -----------------
      → sum xs ≡ ε
  sum-nil {zero} xs prf = refl

  sum-cong : 
    ∀ {xs ys : Ar (ι n) A} 
    → xs ≅ ys 
    -----------------
    → sum xs ≡ sum ys
  sum-cong {zero } {xs} {ys} prf = refl
  sum-cong {suc n} {xs} {ys} prf = cong₂ _⋆_ (prf (ι fzero)) $ sum-cong {n} (reduce-≅ prf)

  sum-reindex : 
    ∀ {m n : ℕ} 
      {xs : Ar (ι m) A} 
    → (prf : m ≡ n) 
    -----------------------------------------
    → sum xs ≡ sum (reshape (reindex prf) xs)
  sum-reindex refl = refl

  sum-zeros : sum {n} (λ i → ε) ≡ ε 
  sum-zeros {zero} = refl
  sum-zeros {suc n} rewrite 
      sum-cong {n} (tail₁-const {A} {n} {ε}) 
    | sum-zeros {n}
    | identityʳ ε
    = refl

  sum-distrib-tail₁ : 
    ∀ (xs ys : Ar (ι (suc n)) A) 
    ---------------------------------------------------------------------------
    → sum (tail₁ (λ i → xs i ⋆ ys i)) ≡ sum (λ i → (tail₁ xs) i ⋆ (tail₁ ys) i)
  sum-distrib-tail₁ {n} xs ys = sum-cong {n} λ{(ι i) → refl }

  --------------------------------------------------------
  --- Sumation can be split at any point into two sums ---
  --------------------------------------------------------

  split-sum : 
    ∀ {m n : ℕ} 
      (xs : Ar (ι (n + m)) A) 
    --------------------------------------------------------
    → sum xs ≡ sum (splitArₗ {n} xs) ⋆ sum (splitArᵣ {n} xs)
  split-sum {m} {zero} xs rewrite
      identityˡ (sum (splitArᵣ {0} xs)) = sum-cong {m} (λ{(ι i) → refl })
  split-sum {m} {suc n} xs rewrite
      assoc (xs (ι fzero)) (sum (tail₁ (splitArₗ {suc n} xs))) (sum (splitArᵣ {suc n} xs))
    = cong₂ _⋆_ refl 
        ( trans 
            (split-sum {m} {n} (tail₁ xs)) 
            ( cong₂ _⋆_ 
              (sum-cong {n} λ{(ι i) → refl }) 
              (sum-cong {m} λ{(ι j) → refl }) 
            )
        )

  --------------------------
  --- Σ(gᵢ⋆fᵢ) ≡ Σgᵢ⋆Σfᵢ ---
  --------------------------

  expand-sum : 
    ∀ (xs ys : Ar (ι (n)) A) 
    ---------------------------------------------------------------
    → sum (λ i → xs i ⋆ ys i) ≡ sum (λ i → xs i) ⋆ sum (λ i → ys i)
  expand-sum {zero} xs ys rewrite identityʳ ε = refl
  expand-sum {suc n} xs ys rewrite
      assoc (xs (ι fzero)) (ys (ι fzero)) (sum (tail₁ (λ i → xs i ⋆ ys i)))
    | assoc (xs (ι fzero)) (sum (tail₁ xs)) (ys (ι fzero) ⋆ sum (tail₁ ys))
    | comm  (sum (tail₁ xs)) (ys (ι fzero) ⋆ sum (tail₁ ys))
    | assoc (ys (ι fzero)) (sum (tail₁ ys)) (sum (tail₁ xs))
    | sum-distrib-tail₁ xs ys
    | expand-sum (tail₁ xs) (tail₁ ys)
    | comm (sum (tail₁ xs)) (sum (tail₁ ys))
    = refl

  --------------------------------------------
  --- Reordering of Summation of Summation ---
  --------------------------------------------

  sum-swap : 
    ∀ (a : Position (ι m) → Position (ι n) → A) 
    -------------------------------------------------------------------------------
    → sum {m} (λ i → sum {n} (λ j → a i j)) ≡ sum {n} (λ j → sum {m} (λ i → a i j))

  sum-swap-helperˡ : 
    ∀ (a : Position (ι (suc m)) → Position (ι (suc n)) → A) 
      (p : Position (ι (suc n))) 
    -------------------------------------------------------------------------------------------------------
    → tail₁ (λ i → a i p ⋆ sum (tail₁ (a i))) ≅ (λ i → (tail₁ a) i p ⋆ sum (λ j → (tail₁ ((tail₁ a) i)) j))
  sum-swap-helperˡ {m} {n} a p (ι x) = cong₂ _⋆_ refl (sum-cong {n} (λ{(ι j) → refl }))

  sum-swap-helperʳ : 
    ∀ (a : Position (ι (suc m)) → Position (ι (suc n)) → A) 
      (p : Position (ι (suc n))) 
    -------------------------------------------------------------------------------------------------------------------------------
    → tail₁ (λ j → a (ι fzero) j ⋆ sum (tail₁ (λ i → a i j))) ≅ (λ j → (tail₁ (a (ι fzero))) j ⋆ sum (λ i → tail₁ ((tail₁ a) i) j))
  sum-swap-helperʳ {m} {n} a p (ι x) = cong₂ _⋆_ refl (sum-cong {m} (λ{(ι i) → refl }))

  sum-swap {zero} {n} a rewrite sum-zeros {n} = refl
  sum-swap {suc m} {zero} a rewrite
      sum-cong {m} (tail₁-const {A} {m} {ε}) 
    | sum-zeros {m} 
    | identityʳ ε = refl
  sum-swap {suc m} {suc n} a rewrite
      assoc (a (ι fzero) (ι fzero)) (sum (tail₁ (a (ι fzero))))         (sum (tail₁ (λ i → a i (ι fzero) ⋆ sum (tail₁ (a i)))))
    | assoc (a (ι fzero) (ι fzero)) (sum (tail₁ (λ i → a i (ι fzero)))) (sum (tail₁ (λ j → a (ι fzero) j ⋆ sum (tail₁ (λ i → a i j)))))
    | sum-cong (sum-swap-helperˡ a (ι fzero))
    | sum-cong (sum-swap-helperʳ a (ι fzero))
    | expand-sum (λ z → tail₁ a z (ι fzero)) (λ z → sum (tail₁ (tail₁ a z)))        -- z here is a horrible varaible name but it was auto assigned and works
    | expand-sum (tail₁ (a (ι fzero)))  (λ z → sum (λ i → (tail₁ (tail₁ a i) z)))
    | sym (assoc (sum (tail₁ (a (ι fzero))))         (sum (λ z → tail₁ a z (ι fzero))) (sum (λ z → sum (tail₁ (tail₁ a z)))))
    | sym (assoc (sum (tail₁ (λ i → a i (ι fzero)))) (sum (tail₁ (a (ι fzero))))       (sum (λ z → sum (λ i → tail₁ (tail₁ a i) z))))
    | comm (sum (tail₁ (a (ι fzero)))) (sum (λ z → tail₁ a z (ι fzero)))
    = cong₂ _⋆_ refl (cong₂ _⋆_ (cong₂ _⋆_ (sum-cong {m} (λ{(ι z) → refl })) refl) (trans (sum-swap (λ z → (tail₁ (tail₁ a z)))) refl))

  ------------------------------------------------
  --- Sum of Sum can be represented as one sum ---
  ------------------------------------------------

  -- A Sum of Sums on an unflattened array, can be represented as one Sum on the same array

  merge-sum  : 
    ∀ (xs : Ar (ι (m * n)) A) 
    ------------------------------------------------------------------
    → sum {m} (λ i → sum {n} (λ j → xs ((i ⊗ j) ⟨ split ⟩ ))) ≡ sum xs

  merge-sumₗ : 
    ∀ (xs : Ar (ι (suc m * suc n)) A) 
    --------------------------------------------------------------------------------
    → (tail₁ (λ j → xs ((ι (fzero {m}) ⊗ j) ⟨ split ⟩))) ≅ (splitArₗ {n} (tail₁ xs))
  merge-sumₗ xs (ι i) = cong (xs ∘ ι) refl

  merge-sum {zero } {n   } xs = refl
  merge-sum {suc m} {zero} xs rewrite 
      sum-nil xs (*-zeroʳ m) 
    | identityˡ (sum {m} (tail₁ (λ i → ε)))
    | sum-cong (tail₁-const {A} {m} {ε})
    | sum-zeros {m}
    = refl
  merge-sum {suc m} {suc n} xs rewrite 
        split-sum {m * suc n} {n} (tail₁ xs)
      | sym (assoc (xs (ι fzero)) (sum (splitArₗ {n} (tail₁ xs))) (sum (splitArᵣ {n} (tail₁ xs))))
      | sum-cong (merge-sumₗ {m} {n} xs)
      = cong₂ _⋆_ refl 
        (trans 
          (sum-cong {m} (λ{ (ι i) → cong₂ _⋆_ refl (sum-cong {n} (λ{(ι j) → refl})) }))
          (merge-sum {m} {suc n} (splitArᵣ {n} (tail₁ xs)))
        )

