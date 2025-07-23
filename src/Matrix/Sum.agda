open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app; trans)
open Eq.≡-Reasoning

module src.Matrix.Sum (real : Real) (cplx : Cplx real) where
  open Real real using (_ᵣ; ℝ)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_; *-comm to *ᵣ-comm; *-identityʳ to *ᵣ-identityʳ)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing using (distribˡ; *-comm; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

  open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
  open import Data.Nat.Properties using (suc-injective) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)

  open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (inj₁; inj₂ )

  open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr; splitAr; splitArₗ; splitArᵣ)
  open import src.Matrix.Equality using (_≅_; foldr-cong; eq+eq≅arr; reduce-≅; tail₁-cong)
  open import src.Matrix.Properties using (tail₁-const)
  open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; eq+eq-position-wrapper; reindex; rev-eq)

  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)



  sum : ∀ {m : ℕ} → (arr : Ar (ι m) ℂ) → ℂ
  sum {zero} arr = 0ℂ
  sum {suc m} arr = (arr (ι fzero)) + (sum ∘ tail₁) arr

  sum-nil : ∀ {n : ℕ} (arr : Ar (ι n) ℂ) (prf : n ≡ 0) → sum arr ≡ 0ℂ
  sum-nil {zero} arr prf = refl

  sum-cong : ∀ {n : ℕ} → {xs ys : Ar (ι n) ℂ} → xs ≅ ys → sum xs ≡ sum ys
  sum-cong {zero } {xs} {ys} prf = refl
  sum-cong {suc n} {xs} {ys} prf = cong₂ _+_ (prf (ι fzero)) (sum-cong {n} {tail₁ xs} {tail₁ ys} (reduce-≅ prf))

  sum-zeros : ∀ {n : ℕ} → sum {n} (λ i → 0ℂ) ≡ 0ℂ 
  sum-zeros {zero} = refl
  sum-zeros {suc n} rewrite 
      sum-cong {n} (tail₁-const {ℂ} {n} {0ℂ}) 
    | sum-zeros {n}
    | +-identityʳ 0ℂ
    = refl

  foldr-pull-out : ∀ {r : ℕ} (n m : ℂ) (arr : Ar (ι r) ℂ) → foldr _+_ (n + m) arr ≡ n + (foldr _+_ m arr)
  foldr-pull-out {zero} n m arr = refl
  foldr-pull-out {suc r} n m arr rewrite
      foldr-pull-out (head₁ arr) (n + m) (tail₁ arr) 
    | foldr-pull-out (head₁ arr) (m) (tail₁ arr) 
    | foldr-pull-out n m (tail₁ arr)
    | sym (+-assoc (arr (ι fzero)) n (foldr _+_ m (tail₁ arr)))
    | +-comm (arr (ι fzero)) n
    | +-assoc n (arr (ι fzero)) (foldr _+_ m (tail₁ arr))
    = refl

  foldr≡sum : ∀ {m : ℕ} (arr : Ar (ι m) ℂ) → foldr {m} _+_ 0ℂ arr ≡ sum {m} arr
  foldr≡sum {zero} arr = refl
  foldr≡sum {suc m} arr rewrite 
      foldr-pull-out {m} (arr (ι fzero)) 0ℂ (tail₁ arr) 
    | foldr≡sum {m} (tail₁ arr)
    = refl

  split-sum : ∀ {m n : ℕ} → (arr : Ar (ι (n +ₙ m)) ℂ) → sum arr ≡ sum (splitArₗ {n} arr) + sum (splitArᵣ {n} arr)
  split-sum {m} {zero} arr rewrite
      +-identityˡ (sum (splitArᵣ {0} arr)) = sum-cong {m} (λ{(ι i) → refl })
  split-sum {m} {suc n} arr rewrite
      +-assoc (arr (ι fzero)) (sum (tail₁ (splitArₗ {suc n} arr))) (sum (splitArᵣ {suc n} arr))
    = cong₂ _+_ refl 
        ( trans 
            (split-sum {m} {n} (tail₁ arr)) 
            ( cong₂ _+_ 
              (sum-cong {n} λ{(ι i) → refl }) 
              (sum-cong {m} λ{(ι j) → refl }) 
            )
        )
