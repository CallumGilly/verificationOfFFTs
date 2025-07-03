open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

module src.Proof (real : Real) (cplx : Cplx real) where

  open Real real using (_ᵣ)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_; *-comm to *ᵣ-comm; *-identityʳ to *ᵣ-identityʳ)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing using (distribˡ; *-comm; zeroˡ; *-identityʳ; *-assoc; +-identityʳ)

  open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
  open import Data.Nat.Properties using () renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ)
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine)

  open import Data.Product.Base using (_×_; proj₁; proj₂; map₁; map₂) renaming ( _,_ to ⟨_,_⟩)

  open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr)
  open import src.Matrix.Equality using (_≅_; foldr-cong; eq+eq≅arr)
  open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; _♭₂; comm-eq; eq+eq-position-wrapper)

  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

  open import src.FFT real cplx using (FFT; twiddles; position-sum; offset-n; offset)
  open import src.DFTMatrix real cplx using (DFT; posVec; step)

  -- open import Algebra.Solver.Ring

  private 
    variable
      N r₁ r₂ : ℕ -- Such that N ≡ r₁ * r₂

  
  double-nested-tail-equiv : ∀ {N : ℕ} (x : ℂ) (ys : Ar (ι (suc (suc N))) ℂ) → 
    (λ i → x * tail₁ (tail₁ ys) i) ≅ (tail₁ (λ i → x * tail₁ ys i))
  double-nested-tail-equiv {N} x ys (ι pos) = refl

  -- foldr-cong : ∀ {X Y : Set} {n : ℕ} → (f : X → Y → Y) → (acc : Y) → {xs ys : Ar (ι n) X} → xs ≅ ys → foldr f acc xs ≡ foldr f acc ys

  map-tail₁ : ∀ {N : ℕ} (f : ℂ → ℂ) (ys : Ar (ι (suc N)) ℂ) → (map f (tail₁ ys)) ≅ (tail₁ (map f ys))
  map-tail₁ {N} x ys (ι pos) = refl

  *-distribˡ-foldr-acc : ∀ {N : ℕ} (acc : ℂ) (x : ℂ) (ys : Ar (ι (suc N)) ℂ) → x * foldr _+_ (head₁ ys + acc) (tail₁ ys) ≡ foldr _+_ (x * (head₁ ys + acc)) (map (x *_) (tail₁ ys))
  *-distribˡ-foldr-acc {zero } acc x ys = Eq.refl
  *-distribˡ-foldr-acc {suc N} acc x ys rewrite 
      *-distribˡ-foldr-acc (head₁ ys + acc) x (tail₁ ys) 
    | distribˡ x (ys (ι (fsuc fzero))) (ys (ι fzero) + acc) 
    | foldr-cong _+_ (x * ys (ι (fsuc fzero)) + x * (ys (ι fzero) + acc)) (double-nested-tail-equiv x ys)
    = refl

  -- Attempt to implement https://agda.github.io/agda-stdlib/master/Algebra.Properties.Semiring.Sum.html 's *-distribˡ-sum
  *-distribˡ-sum : ∀ {N : ℕ} (acc : ℂ) (x : ℂ) (ys : Ar (ι N) ℂ) → x * (foldr _+_ acc ys) ≡ foldr _+_ (x * acc) (map (x *_) ys)
  *-distribˡ-sum {zero } acc x ys = Eq.refl
  *-distribˡ-sum {suc N} acc x ys =
    begin
      x * foldr _+_ (head₁ ys + acc) (tail₁ ys)                           ≡⟨ *-distribˡ-foldr-acc acc x ys ⟩
      foldr _+_ (x * (head₁ ys + acc))            (map (x *_) (tail₁ ys)) ≡⟨ cong (λ f → foldr _+_ f (map (x *_) (tail₁ ys))) (distribˡ x (head₁ ys) acc) ⟩
      foldr _+_ (head₁ (map (x *_) ys) + x * acc) (map (x *_) (tail₁ ys)) ≡⟨ foldr-cong _+_ (head₁ (map (x *_) ys) + x * acc) (map-tail₁ (x *_) ys) ⟩
      foldr _+_ (head₁ (map (x *_) ys) + x * acc) (tail₁ (map (x *_) ys))
    ∎

  *-comm-on-ys : ∀ {N : ℕ} (ys : Ar (ι N) ℂ) (x : ℂ) → (λ i → x * ys i) ≅ (λ i → ys i * x)
  *-comm-on-ys ys x (ι pos) = *-comm x (ys (ι pos))

  *-distribʳ-sum  : ∀ {N : ℕ} (acc : ℂ) (x : ℂ) (ys : Ar (ι N) ℂ) → (foldr _+_ acc ys) * x ≡ foldr _+_ (acc * x) (map (_* x) ys)
  *-distribʳ-sum acc x ys rewrite 
      *-comm (foldr _+_ acc ys) x
    | *-distribˡ-sum acc x ys 
    | *-comm x acc 
    | foldr-cong _+_ (acc * x) (*-comm-on-ys ys x)
    = refl

  
  offset-ιn≡posVec : ∀ {N : ℕ} (p : Position (ι N)) → offset-n p ≡ posVec p
  offset-ιn≡posVec (ι x) with offset (ι x) 
  ... | ι y = Eq.refl

  *-distribʳ-sum-application : ∀ 
    {r₁ r₂ : ℕ}
    (arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ) 
    (j₀  : Fin r₁)
    (j₁  : Fin r₂)
    (k₀  : Position (ι r₂))
    → 
       foldr _+_ 0ℂ 
         (λ k₁ → 
              arr (k₁ ⊗ k₀) 
            * -ω r₁ (posVec k₁ *ₙ toℕ j₀)
         )
       * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (offset-n k₀))
       * -ω r₂ (posVec k₀ *ₙ toℕ j₁)
       ≡
       foldr _+_ 0ℂ 
         (λ k₁ → 
              arr (k₁ ⊗ k₀) 
            * -ω r₁ (posVec k₁ *ₙ toℕ j₀)
            * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (posVec k₀))
            * -ω r₂ (posVec k₀ *ₙ toℕ j₁)
         )
  *-distribʳ-sum-application {r₁} {r₂} arr j₀ j₁ k₀ rewrite 
        offset-ιn≡posVec k₀
      | *-distribʳ-sum 0ℂ 
        (-ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (posVec k₀))) 
        (λ k₁ → arr (k₁ ⊗ k₀) * -ω r₁ (posVec k₁ *ₙ toℕ j₀)) 
      | zeroˡ 
         (-ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (posVec k₀))) 
      | *-distribʳ-sum 0ℂ 
          (-ω r₂ (posVec k₀ *ₙ toℕ j₁)) 
          (λ k₁ → arr (k₁ ⊗ k₀) * -ω r₁ (posVec k₁ *ₙ toℕ j₀) * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (posVec k₀))) 
      | zeroˡ 
        (-ω r₂ (posVec k₀ *ₙ toℕ j₁)) 
    = Eq.refl

  ω-power : ∀
    {r₁ r₂ : ℕ}
    (j₀  : Fin r₁)
    (j₁  : Fin r₂)
    (k₀  : Position (ι r₂))
    (k₁  : Position (ι r₁))
    → (r₂ *ₙ (posVec k₁ *ₙ toℕ j₀) +ₙ toℕ j₀ *ₙ posVec k₀ +ₙ r₁ *ₙ (posVec k₀ *ₙ toℕ j₁) +ₙ r₂ *ₙ (r₁ *ₙ (toℕ j₁ *ₙ posVec k₁)))
      ≡ 
      ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))
  ω-power {r₁} {r₂} j₀ j₁ k₀ k₁ = solvable-form r₁ r₂ (toℕ j₀) (toℕ j₁) (posVec k₀) (posVec k₁)
    where
      solvable-form : ∀ (r₁ℕ r₂ℕ j₀ℕ j₁ℕ k₀ℕ k₁ℕ : ℕ) → 
        (r₂ℕ *ₙ (k₁ℕ *ₙ j₀ℕ) +ₙ j₀ℕ *ₙ k₀ℕ +ₙ r₁ℕ *ₙ (k₀ℕ *ₙ j₁ℕ) +ₙ r₂ℕ *ₙ (r₁ℕ *ₙ (j₁ℕ *ₙ k₁ℕ)))
        ≡ 
        ((j₁ℕ *ₙ r₁ℕ +ₙ j₀ℕ) *ₙ (k₁ℕ *ₙ r₂ℕ +ₙ k₀ℕ))
      solvable-form = solve 6 (λ r₁ℕ r₂ℕ j₀ℕ j₁ℕ k₀ℕ k₁ℕ → 
        (r₂ℕ :* (k₁ℕ :* j₀ℕ) :+ j₀ℕ :* k₀ℕ :+ r₁ℕ :* (k₀ℕ :* j₁ℕ) :+ r₂ℕ :* (r₁ℕ :* (j₁ℕ :* k₁ℕ)))
        := 
        ((j₁ℕ :* r₁ℕ :+ j₀ℕ) :* (k₁ℕ :* r₂ℕ :+ k₀ℕ))
        ) refl


  inner-rearange : ∀
    {r₁ r₂ : ℕ}
    (arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ) 
    (j₀  : Fin r₁)
    (j₁  : Fin r₂)
    (k₀  : Position (ι r₂))
    (k₁  : Position (ι r₁))
    → 
         arr (k₁ ⊗ k₀) 
       * -ω r₁ (posVec k₁ *ₙ toℕ j₀)
       * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (posVec k₀))
       * -ω r₂ (posVec k₀ *ₙ toℕ j₁)
      ≡
       arr (k₁ ⊗ k₀) * 
        -ω (r₂ *ₙ r₁) 
           (((toℕ j₁ *ₙ r₁) +ₙ toℕ j₀) *ₙ ((posVec k₁ *ₙ r₂) +ₙ posVec k₀))
  inner-rearange {r₁} {r₂} arr j₀ j₁ k₀ k₁ rewrite
      Eq.sym (ω-r₁x-r₁y {r₂} {r₁} {posVec k₁ *ₙ toℕ j₀})
    | Eq.sym (ω-r₁x-r₁y {r₁} {r₂} {posVec k₀ *ₙ toℕ j₁})
    | Eq.sym (*-identityʳ (arr (k₁ ⊗ k₀) * -ω (r₂ *ₙ r₁) (r₂ *ₙ (posVec k₁ *ₙ toℕ j₀)) * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ posVec k₀) * -ω (r₁ *ₙ r₂) (r₁ *ₙ (posVec k₀ *ₙ toℕ j₁)))) 
    | Eq.sym (ω-N-mN {r₁} {toℕ j₁ *ₙ posVec k₁})
    | Eq.sym (ω-r₁x-r₁y {r₂} {r₁} {r₁ *ₙ (toℕ j₁ *ₙ posVec k₁)})
    | *ₙ-comm r₂ r₁
    | *-assoc (arr (k₁ ⊗ k₀)) (-ω (r₁ *ₙ r₂) (r₂ *ₙ (posVec k₁ *ₙ toℕ j₀))) (-ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ posVec k₀))
    | Eq.sym (ω-N-k₀+k₁ {r₁ *ₙ r₂} {r₂ *ₙ (posVec k₁ *ₙ toℕ j₀)} {toℕ j₀ *ₙ posVec k₀})
    | *-assoc (arr (k₁ ⊗ k₀)) (-ω (r₁ *ₙ r₂) (r₂ *ₙ (posVec k₁ *ₙ toℕ j₀) +ₙ toℕ j₀ *ₙ posVec k₀)) (-ω (r₁ *ₙ r₂) (r₁ *ₙ (posVec k₀ *ₙ toℕ j₁)))
    | Eq.sym (ω-N-k₀+k₁ {r₁ *ₙ r₂} {r₂ *ₙ (posVec k₁ *ₙ toℕ j₀) +ₙ toℕ j₀ *ₙ posVec k₀} {r₁ *ₙ (posVec k₀ *ₙ toℕ j₁)})
    | *-assoc (arr (k₁ ⊗ k₀)) (-ω (r₁ *ₙ r₂) (r₂ *ₙ (posVec k₁ *ₙ toℕ j₀) +ₙ toℕ j₀ *ₙ posVec k₀ +ₙ r₁ *ₙ (posVec k₀ *ₙ toℕ j₁))) (-ω (r₁ *ₙ r₂) (r₂ *ₙ (r₁ *ₙ (toℕ j₁ *ₙ posVec k₁))))
    | Eq.sym (ω-N-k₀+k₁ {r₁ *ₙ r₂} {r₂ *ₙ (posVec k₁ *ₙ toℕ j₀) +ₙ toℕ j₀ *ₙ posVec k₀ +ₙ r₁ *ₙ (posVec k₀ *ₙ toℕ j₁)} {r₂ *ₙ (r₁ *ₙ (toℕ j₁ *ₙ posVec k₁))})
    | ω-power j₀ j₁ k₀ k₁
    | *ₙ-comm r₁ r₂
    = refl

         --  foldr _+_ 0ℂ 
         --    (λ k₀ →
         --       foldr _+_ 0ℂ 
         --         (λ k₁ → 
         --             arr (k₁ ⊗ k₀) 
         --           * -ω (r₂ *ₙ r₁) (((toℕ j₁ *ₙ r₁) +ₙ toℕ j₀) *ₙ ((posVec k₁ *ₙ r₂) +ₙ posVec k₀))
         --         )
         --    )

         --  foldr _+_ 0ℂ
         --    (λ k →
         --         arr (k ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩)
         --       * -ω (r₂ *ₙ r₁) (posVec k *ₙ toℕ (combine j₁ j₀))
         --    )
         -- k₀   : Position (ι r₂)
         -- k₁   : Position (ι r₁)
  pos-combine : (k₀ : Position (ι r₂)) → (k₁ : Position (ι r₁)) → Position (ι r₂ ⊗ ι r₁)
  pos-combine (ι k₀) (ι k₁) = ι k₀ ⊗ ι k₁

  split-foldr : ∀ 
    {r₁ r₂ : ℕ} 
    → (xs : Ar (ι r₁ ⊗ ι r₂) ℂ)
    → foldr {r₂ *ₙ r₁} _+_ 0ℂ (λ k → xs (k ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩)) ≡ foldr {r₂} _+_ 0ℂ (λ k₀ → foldr {r₁} _+_ 0ℂ (λ k₁ → xs (k₁ ⊗ k₀)))
  split-foldr {r₁} {r₂} xs = ?

  --combine-foldr : ∀
  --  {r₁ r₂ : ℕ} 
  --  → (f : Position (ι r₂) → Position (ι r₁) → ℂ)
  --  → foldr {r₂} _+_ 0ℂ (λ k₀ → foldr {r₁} _+_ 0ℂ (λ k₁ → f k₀ k₁)) ≡ foldr {r₂ *ₙ r₁} _+_ 0ℂ (λ k → (λ{ (k₀ ⊗ k₁) → ?}) k ⟨ ? ⟩)



    -- {xs : Ar (ι r₁ ⊗ ι r₂) ℂ } 
    -- → (r : Reshape (ι r₁ ⊗ ι r₂) (ι (r₂ *ₙ r₁) ))
    -- → foldr {r₂ *ₙ r₁} _+_ 0ℂ (λ k → reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat) xs k ) ≡ foldr {r₂} _+_ 0ℂ (λ k₀ → foldr {r₁} _+_ 0ℂ (λ k₁ → (xs (k₁ ⊗ k₀))))
   
   --tmp : ∀ {N : ℕ} → posVec k ≡ (posVec k₁ *ₙ r₂) + posVec k₀
   
  innerVal : ∀ {r₁ r₂ : ℕ} (arr : Ar (ι r₁ ⊗ ι r₂) ℂ) (j : Position (ι r₂ ⊗ ι r₁)) (k₀ : Position (ι r₂)) (k₁ : Position (ι r₁)) → ℂ
  innerVal {r₁} {r₂} arr (ι j₁ ⊗ ι j₀) k₀ k₁ = arr (k₁ ⊗ k₀) * -ω (r₂ *ₙ r₁) (((toℕ j₁ *ₙ r₁) +ₙ toℕ j₀) *ₙ ((posVec k₁ *ₙ r₂) +ₙ posVec k₀))

  mergeFoldr : ∀ {r₁ r₂ : ℕ} → (f : Position (ι r₂) → Position (ι r₁) → ℂ) → 
    foldr {r₂ *ₙ r₁} _+_ 0ℂ (λ k → (unnest f) (k ⟨ flat ⟩ ) )
    ≡
    foldr {r₂} _+_ 0ℂ (λ k₀ → foldr {r₁} _+_ 0ℂ (λ k₁ → f k₀ k₁)) 
  mergeFoldr {r₁} {zero} f = refl
  mergeFoldr {zero} {suc r₂} f rewrite mergeFoldr {zero} {r₂} (tail₁ f) = ?
  mergeFoldr {suc r₁} {suc r₂} f = ?


  proj₁-remQuot-combine : ∀ {r₁ r₂ : ℕ} (p₁ : Fin r₂) (p₀ : Fin r₁) → 
    proj₁ (remQuot {r₁} r₂ (combine p₀ p₁)) ≡ p₀ 
  proj₁-remQuot-combine {suc r₁} {r₂} p₁ fzero     rewrite splitAt-↑ˡ r₂ p₁ (r₁ *ₙ r₂) = refl
  proj₁-remQuot-combine {suc r₁} {r₂} p₁ (fsuc p₀) rewrite 
      splitAt-↑ʳ r₂    (r₁ *ₙ r₂) (combine p₀ p₁) 
    | (proj₁-remQuot-combine p₁ p₀)
    = refl

  proj₂-remQuot-combine : ∀ {r₁ r₂ : ℕ} (p₁ : Fin r₂) (p₀ : Fin r₁) → 
    proj₂ (remQuot {r₁} r₂ (combine p₀ p₁)) ≡ p₁ 
  proj₂-remQuot-combine {suc r₁} {r₂} p₁ fzero     rewrite splitAt-↑ˡ r₂ p₁ (r₁ *ₙ r₂) = refl
  proj₂-remQuot-combine {suc r₁} {r₂} p₁ (fsuc p₀) rewrite
      splitAt-↑ʳ r₂     (r₁ *ₙ r₂) (combine p₀ p₁)
    | proj₂-remQuot-combine p₁ p₀
    = refl

  posMerge : ∀ {r₁ r₂ : ℕ} {X : Set} (p₀ : Fin r₁) (p₁ : Fin r₂) (arr : Ar (ι r₁ ⊗ ι r₂) X) → (ι p₀ ⊗ ι p₁) ≡ (ι (combine p₀ p₁) ) ⟨ comm-eq refl ⟩ ⟨ flat ⟩
  posMerge {r₁} {r₂} {X} p₀ p₁ arr rewrite 
      proj₁-remQuot-combine p₁ p₀
    | proj₂-remQuot-combine p₁ p₀ 
    = refl
  
  j₁*r₁+j₀-is-combine : ∀ 
    {r₁ r₂ : ℕ} 
    {j₀ : Fin r₁}
    {j₁ : Fin r₂}
    → toℕ j₁ *ₙ r₁ +ₙ toℕ j₀ ≡ toℕ (combine j₁ j₀)
  j₁*r₁+j₀-is-combine {r₁} {r₂} {j₀} {j₁} rewrite
      toℕ-combine j₁ j₀ = solve 3 
        (λ r₁ℕ j₁ℕ j₀ℕ → j₁ℕ :* r₁ℕ :+ j₀ℕ := r₁ℕ :* j₁ℕ :+ j₀ℕ) 
        refl 
        r₁ (toℕ j₁) (toℕ j₀)
  
  sub-proof₁ : ∀
    {r₁ r₂ : ℕ}
    (f : Position (ι r₂) → Position (ι r₁) → ℂ)
    (g : Position (ι r₂) → Position (ι r₁) → ℂ)
    → 
        reshape flat (unnest
        (λ k₀ k₁ →
           (f k₀ k₁) *
           (g k₀ k₁ )
        )) 
     ≅
        (λ ix → 
          reshape flat (unnest f) ix
          *
          reshape flat (unnest g) ix
        )
  sub-proof₁ {r₁} {r₂} f g (ι x) = ?

  sub-proof₂ : ∀ 
    {r₁ r₂ : ℕ} 
    (ix : Position (ι (r₂ *ₙ r₁)))
    (arr : Ar (ι r₁ ⊗ ι r₂) ℂ)
    → (unnest (λ k₀ k₁ → arr (k₁ ⊗ k₀) ) (ix ⟨ flat ⟩)) ≡ ( arr (ix ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩) )
  sub-proof₂ {r₁} {r₂} (ι x) arr = ?

  sub-proof₃ : ∀
      {r₁ r₂ : ℕ}
      {j₀ : Fin r₁}
      {j₁ : Fin r₂}
      (ix : Position (ι (r₂ *ₙ r₁)))
    → (unnest
      (λ k₀ k₁ →
         -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ (posVec {r₁} k₁ *ₙ r₂ +ₙ posVec {r₂} k₀))
      ) (ix ⟨ flat ⟩))
    ≡ 
      -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ posVec ix)
  sub-proof₃ = ?

  theorm : ∀ {r₁ r₂ : ℕ} → ∀ (arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ)
    → FFT arr ≅ ((reshape _♯) ∘ DFT ∘ (reshape {ι r₁ ⊗ ι r₂} _♭₂)) arr
  theorm {r₁} {r₂} arr ((ι j₁) ⊗ (ι j₀)) =
        begin
          foldr _+_ 0ℂ 
            (λ k₀ →
               foldr _+_ 0ℂ 
                 (λ k₁ → 
                      arr (k₁ ⊗ k₀) 
                    * -ω r₁ (posVec k₁ *ₙ toℕ j₀)
                 )
               * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (offset-n k₀))
               * -ω r₂ (posVec k₀ *ₙ toℕ j₁)
            )
        ≡⟨ foldr-cong _+_ 0ℂ (*-distribʳ-sum-application arr j₀ j₁) ⟩
          foldr _+_ 0ℂ 
            (λ k₀ →
               foldr _+_ 0ℂ 
                 (λ k₁ → 
                      arr (k₁ ⊗ k₀) 
                    * -ω r₁ (posVec k₁ *ₙ toℕ j₀)
                    * -ω (r₁ *ₙ r₂) (toℕ j₀ *ₙ (posVec k₀))
                    * -ω r₂ (posVec k₀ *ₙ toℕ j₁)
                 )
            )
        ≡⟨ foldr-cong _+_ 0ℂ (λ k₀ → foldr-cong _+_ 0ℂ (inner-rearange arr j₀ j₁ k₀)) ⟩
          foldr _+_ 0ℂ 
            (λ k₀ →
               foldr _+_ 0ℂ 
                 (λ k₁ → 
                     arr (k₁ ⊗ k₀) 
                   * -ω (r₂ *ₙ r₁) (((toℕ j₁ *ₙ r₁) +ₙ toℕ j₀) *ₙ ((posVec k₁ *ₙ r₂) +ₙ posVec k₀))
                 )
            )
        ≡⟨⟩
          foldr _+_ 0ℂ 
            (λ k₀ →
               foldr _+_ 0ℂ 
                 (λ k₁ → innerVal arr (ι j₁ ⊗ ι j₀) k₀ k₁)
            )
        ≡⟨ sym (mergeFoldr (λ k₀ k₁ → innerVal arr (ι j₁ ⊗ ι j₀) k₀ k₁)) ⟩
          foldr _+_ 0ℂ (λ k → (unnest (λ k₀ k₁ → innerVal arr (ι j₁ ⊗ ι j₀) k₀ k₁)) (k ⟨ flat ⟩ ))
        ≡⟨⟩
          foldr _+_ 0ℂ (reshape flat (unnest (innerVal arr (ι j₁ ⊗ ι j₀))))
        ≡⟨⟩
          foldr _+_ 0ℂ
            (λ ix →
               unnest
               (λ k₀ k₁ →
                  arr (k₁ ⊗ k₀) *
                  -ω (r₂ *ₙ r₁) ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀)))
               (ix ⟨ flat ⟩))
        ≡⟨ ? ⟩ -- j₁*r₁+j₀-is-combine
          foldr _+_ 0ℂ
            (λ ix →
               unnest
               (λ k₀ k₁ →
                  arr (k₁ ⊗ k₀) *
                  -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀)))
               (ix ⟨ flat ⟩))
        ≡⟨ foldr-cong 
              _+_ 
              0ℂ 
              (sub-proof₁ 
                (λ k₀ k₁ → arr (k₁ ⊗ k₀)) 
                (λ k₀ k₁ → -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ (posVec {r₁} k₁ *ₙ r₂ +ₙ posVec {r₂} k₀)))
              )
          ⟩
          foldr _+_ 0ℂ
            (λ ix →
               (unnest
               (λ k₀ k₁ →
                  arr (k₁ ⊗ k₀) 
               ) (ix ⟨ flat ⟩))
               *
               (unnest
               (λ k₀ k₁ →
                  -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ (posVec {r₁} k₁ *ₙ r₂ +ₙ posVec {r₂} k₀))
               ) (ix ⟨ flat ⟩))
            )
        ≡⟨ ? ⟩ -- sub-proof₂
          foldr _+_ 0ℂ
            (λ ix →
               ( arr (ix ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩) )
               *
               (unnest
               (λ k₀ k₁ →
                  -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ (posVec {r₁} k₁ *ₙ r₂ +ₙ posVec {r₂} k₀))
               ) (ix ⟨ flat ⟩))
            )
        ≡⟨ ? ⟩ -- sub-proof₃
          foldr _+_ 0ℂ
            (λ ix →
               ( arr (ix ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩) )
               * -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ posVec ix)
            )
        ≡⟨⟩
          foldr _+_ 0ℂ
            (λ k →
                 arr (k ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩)
               * -ω (r₂ *ₙ r₁) (toℕ (combine j₁ j₀) *ₙ posVec k)
            )
        ≡⟨ ? ⟩
          foldr _+_ 0ℂ
            (λ k →
                 arr (k ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩)
               * -ω (r₂ *ₙ r₁) (posVec k *ₙ toℕ (combine j₁ j₀))
            )
        ≡⟨⟩
          foldr _+_ 0ℂ
            (λ k →
                 arr (k ⟨ comm-eq (*ₙ-comm r₁ r₂) ⟩ ⟨ flat ⟩)
               * -ω (r₂ *ₙ r₁) (posVec k *ₙ toℕ (combine j₁ j₀))
            )
        ≡⟨⟩
          (DFT (reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat) arr)) (ι (combine j₁ j₀))
        ≡⟨⟩
          (DFT (reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat) arr)) ((ι j₁ ⊗ ι j₀) ⟨ split ⟩)
        ≡⟨⟩
          (reshape _♯ (DFT (reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat) arr))) (ι j₁ ⊗ ι j₀)
        ≡⟨ cong (λ f → (reshape _♯ (DFT ((reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat) (f))))) (ι j₁ ⊗ ι j₀)) (sym (eq+eq arr)) ⟩
          (reshape {ι (length (ι r₂ ⊗ ι r₁))} {ι r₂ ⊗ ι r₁} _♯ (DFT ((reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat) (reshape (eq ⊕ eq) arr))))) (ι j₁ ⊗ ι j₀)
        ≡⟨⟩
          (reshape _♯ (DFT ((reshape (comm-eq (*ₙ-comm r₁ r₂) ∙ flat ∙ eq ⊕ eq)) arr))) (ι j₁ ⊗ ι j₀)
        ∎


-- eq+eq≅arr : ∀ {n m : ℕ} {X : Set} {xs : Ar (ι n ⊗ ι m) X} → reshape (eq ⊕ eq) xs ≅ xs
