open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

module src.Proof (real : Real) (cplx : Cplx real) where

  open Real real
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_; *-comm to *ᵣ-comm)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing

  open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ₙ_)
  open import Data.Nat.Properties renaming (*-comm to *ₙ-comm)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id)

  open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

  open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr; sum)
  open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; _♭₂; comm-eq; eq+eq-position-wrapper)

  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

  open import src.FFT real cplx using (FFT; twiddles; position-sum; offset-n)
  open import src.DFTMatrix real cplx using (DFT; posVec; step)

  open import src.Extensionality using (extensionality)
  -- open import Algebra.Solver.Ring

  private 
    variable
      N r₁ r₂ : ℕ -- Such that N ≡ r₁ * r₂

  
  -- I really don't like having to use extensionality here
  double-nested-tail-equiv : ∀ {N : ℕ} (x : ℂ) (ys : Ar (ι (suc (suc N))) ℂ) → 
    (λ i → x * tail₁ (tail₁ ys) i) ≡ (tail₁ (λ i → x * tail₁ ys i))
  double-nested-tail-equiv {N} x ys = extensionality λ{(ι i) → Eq.refl }

  map-tail₁ : ∀ {N : ℕ} (f : ℂ → ℂ) (ys : Ar (ι (suc N)) ℂ) → (map f (tail₁ ys)) ≡ (tail₁ (map f ys))
  map-tail₁ {N} x ys = extensionality λ{(ι i) → Eq.refl }

  *-distribˡ-foldr-acc : ∀ {N : ℕ} (acc : ℂ) (x : ℂ) (ys : Ar (ι (suc N)) ℂ) → x * foldr _+_ (head₁ ys + acc) (tail₁ ys) ≡ foldr _+_ (x * (head₁ ys + acc)) (map (x *_) (tail₁ ys))
  *-distribˡ-foldr-acc {zero } acc x ys = Eq.refl
  *-distribˡ-foldr-acc {suc N} acc x ys rewrite 
      *-distribˡ-foldr-acc (head₁ ys + acc) x (tail₁ ys) 
    | distribˡ x (ys (ι (fsuc fzero))) (ys (ι fzero) + acc) 
    | double-nested-tail-equiv x ys
    = Eq.refl

  -- Attempt to implement https://agda.github.io/agda-stdlib/master/Algebra.Properties.Semiring.Sum.html 's *-distribˡ-sum
  *-distribˡ-sum : ∀ {N : ℕ} (acc : ℂ) (x : ℂ) (ys : Ar (ι N) ℂ) → x * (foldr _+_ acc ys) ≡ foldr _+_ (x * acc) (map (x *_) ys)
  *-distribˡ-sum {zero } acc x ys = Eq.refl
  *-distribˡ-sum {suc N} acc x ys =
    begin
      x * foldr _+_ (head₁ ys + acc) (tail₁ ys)                           ≡⟨ *-distribˡ-foldr-acc acc x ys ⟩
      foldr _+_ (x * (head₁ ys + acc))            (map (x *_) (tail₁ ys)) ≡⟨ cong (λ f → foldr _+_ f (map (x *_) (tail₁ ys))) (distribˡ x (head₁ ys) acc) ⟩
      foldr _+_ (head₁ (map (x *_) ys) + x * acc) (map (x *_) (tail₁ ys)) ≡⟨ cong (foldr _+_ (head₁ (map (x *_) ys) + x * acc)) (map-tail₁ (x *_) ys) ⟩
      foldr _+_ (head₁ (map (x *_) ys) + x * acc) (tail₁ (map (x *_) ys))
    ∎

  *-comm-on-ys : ∀ {N : ℕ} (ys : Ar (ι N) ℂ) (x : ℂ) → (λ i → x * ys i) ≡ (λ i → ys i * x)
  *-comm-on-ys ys x = extensionality (λ i → *-comm x (ys i))

  *-distribʳ-sum  : ∀ {N : ℕ} (acc : ℂ) (x : ℂ) (ys : Ar (ι N) ℂ) → (foldr _+_ acc ys) * x ≡ foldr _+_ (acc * x) (map (_* x) ys)
  *-distribʳ-sum acc x ys rewrite 
      *-comm (foldr _+_ acc ys) x
    | *-distribˡ-sum acc x ys 
    | *-comm x acc 
    | *-comm-on-ys ys x = Eq.refl
  
  *-distribʳ-sum-application : ∀ 
    {r₁ r₂ : ℕ}
    (arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ) 
    (j₀  : Fin r₁)
    (j₁  : Fin r₂)
    (k₀  : Position (ι r₂))
    → 
       foldr _+_ 0ℂ (λ k₁ → 
         arr (k₁ ⊗ k₀) * -ω r₁ (posVec k₁ *ₙ toℕ j₁)
       ) 
         * -ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀)) 
         * -ω r₂ (posVec k₀ *ₙ toℕ j₀)
       ≡ 
       foldr _+_ 0ℂ (λ k₁ → 
         arr (k₁ ⊗ k₀) * -ω r₁ (posVec k₁ *ₙ toℕ j₁)
         * -ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀)) 
         * -ω r₂ (posVec k₀ *ₙ toℕ j₀)
       ) 
  *-distribʳ-sum-application {r₁} {r₂} arr j₀ j₁ k₀ rewrite
      *-distribʳ-sum 0ℂ 
        (-ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀))) 
        (λ k₁ → arr (k₁ ⊗ k₀) * -ω r₁ (posVec k₁ *ₙ toℕ j₁)) 
    | zeroˡ 
       (-ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀))) 
    | *-distribʳ-sum 0ℂ 
        (-ω r₂ (posVec k₀ *ₙ toℕ j₀)) 
        (λ i → arr (i ⊗ k₀) * -ω r₁ (posVec i *ₙ toℕ j₁) * -ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀))) 
    | zeroˡ 
      (-ω r₂ (posVec k₀ *ₙ toℕ j₀)) 
    = Eq.refl

  theorm : ∀ {r₁ r₂ : ℕ}
    → FFT ≡ (reshape _♯) ∘ DFT ∘ (reshape {ι r₁ ⊗ ι r₂} _♭₂)
  theorm {r₁} {r₂} = -- I feel like half the point of the idea of using solvers was to remove these extensionalitys, todo: Ask AS
    extensionality (λ arr → 
      extensionality λ{ ((ι j₀) ⊗ (ι j₁)) →
        begin
          foldr _+_ 0ℂ
            (λ k₀ →
               foldr _+_ 0ℂ (λ k₁ → arr (k₁ ⊗ k₀) * -ω r₁ (posVec k₁ *ₙ toℕ j₁))
               * -ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀))
               * -ω r₂ (posVec k₀ *ₙ toℕ j₀))
        ≡⟨ ? ⟩
          foldr _+_ 0ℂ
            (λ k₀ →
               foldr _+_ 0ℂ (λ k₁ → 
                   arr (k₁ ⊗ k₀) 
                 * -ω r₁         (posVec k₁ *ₙ toℕ j₁)
                 * -ω (r₁ *ₙ r₂) (toℕ j₁ *ₙ (offset-n k₀)) 
                 * -ω r₂         (posVec k₀ *ₙ toℕ j₀)
               )
            ) 
        ≡⟨⟩
          ?
      }
    )


