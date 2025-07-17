open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

module src.Proof3 (real : Real) (cplx : Cplx real) where

  open Real real using (_ᵣ)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_; *-comm to *ᵣ-comm; *-identityʳ to *ᵣ-identityʳ)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing using (distribˡ; *-comm; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm)

  open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
  open import Data.Nat.Properties using (suc-injective) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)

  open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (inj₁; inj₂ )

  open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr; splitAr; splitArₗ; splitArᵣ; toFin)
  open import src.Matrix.Equality using (_≅_; foldr-cong; eq+eq≅arr)
  open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; _♭₃; comm-eq; eq+eq-position-wrapper; reindex; rev-eq)

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

  --swap-foldr : ∀ {n m : ℕ} (arr : Ar (ι (m *ₙ n)) ℂ) (acc : ℂ) → 
  --    foldr {n} _+_ acc
  --      (λ k₀ →
  --         foldr {m} _+_ 0ℂ 
  --           (λ k₁ → 
  --              arr ((k₁ ⊗ k₀) ⟨ split ⟩ )
  --           )
  --      )
  --      ≡
  --      foldr {m} _+_ acc
  --        (λ k₀ →
  --           foldr {n} _+_ 0ℂ 
  --             (λ k₁ → 
  --                arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {m} {n} ⟩ )
  --             )
  --        )
  --swap-foldr {n} {m} arr acc = ?


  --generalMergeFoldr : ∀ {n m : ℕ} (arr : Ar (ι (m *ₙ n)) ℂ) (acc : ℂ) → 
  --    foldr {m} _+_ acc
  --      (λ k₀ →
  --         foldr {n} _+_ 0ℂ 
  --           (λ k₁ → 
  --              arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {m} {n} ⟩ )
  --           )
  --      )
  --  ≡
  --    foldr {m *ₙ n} _+_ acc arr
  --generalMergeFoldr {n} {m} arr acc = ?

  --flattenFoldLemma : ∀ {r₁ r₂ : ℕ} (arr : Ar (ι (r₂ *ₙ r₁)) ℂ) →
  --  foldr {r₂} _+_ 0ℂ (λ k₀ → foldr {r₁} _+_ 0ℂ (λ k₁ → arr (ι (combine (toFin k₀) (toFin k₁)))))
  --  ≡
  --  foldr {r₂ *ₙ r₁} _+_ 0ℂ arr
  --flattenFoldLemma {r₁} {r₂} arr = ?

  newMergeFoldr : ∀ {r₁ r₂ : ℕ} (arr : Ar (ι (r₂ *ₙ r₁)) ℂ) →
      foldr {r₂} _+_ 0ℂ 
        (λ k₀ →
           foldr {r₁} _+_ 0ℂ 
             (λ k₁ → 
                arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ )
             )
        )
    ≡
      foldr {r₂ *ₙ r₁} _+_ (0ℂ) (arr)
  newMergeFoldr {r₁} {r₂} arr =
    begin
      foldr {r₂} _+_ 0ℂ 
        (λ k₀ →
           foldr {r₁} _+_ 0ℂ 
             (λ k₁ → 
                arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ )
             )
        )
    ≡⟨⟩
      ?




  innerVal : ∀ {r₁ r₂ : ℕ} (arr : Ar (ι r₁ ⊗ ι r₂) ℂ) (j : Position (ι r₂ ⊗ ι r₁)) (k₀ : Position (ι r₂)) (k₁ : Position (ι r₁)) → ℂ
  innerVal {r₁} {r₂} arr (ι j₁ ⊗ ι j₀) k₀ k₁ = arr (k₁ ⊗ k₀) * -ω (r₂ *ₙ r₁) (((toℕ j₁ *ₙ r₁) +ₙ toℕ j₀) *ₙ ((posVec k₁ *ₙ r₂) +ₙ posVec k₀))

  posVec-is-toℕ : ∀ {n : ℕ} (f : Fin n) → posVec (ι f) ≡ toℕ f
  posVec-is-toℕ f = refl

  reorder-inner′ : ∀
    {arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ} 
    (j₀ : (Fin r₁)) 
    (j₁ : (Fin r₂))
    (k₀ : Position (ι r₂)) 
    (k₁ : Position (ι r₁))
    → ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))
      ≡
      (posVec (((k₁ ⊗ k₀) ⟨ split ⟩) ⟨ reindex {r₂} {r₁} ⟩) *ₙ toℕ (combine j₁ j₀))
  reorder-inner′ {r₁} {r₂} {arr} j₀ j₁ (ι k₀) (ι k₁) =
    begin
      (toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec (ι k₁) *ₙ r₂ +ₙ posVec (ι k₀))
    ≡⟨ *ₙ-comm (toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) (posVec (ι k₁) *ₙ r₂ +ₙ posVec (ι k₀)) ⟩
      (posVec (ι k₁) *ₙ r₂ +ₙ posVec (ι k₀)) *ₙ (toℕ j₁ *ₙ r₁ +ₙ toℕ j₀)
    ≡⟨ cong (λ f → (posVec (ι k₁) *ₙ r₂ +ₙ posVec (ι k₀)) *ₙ (f +ₙ toℕ j₀)) (*ₙ-comm (toℕ j₁) r₁) ⟩
      (posVec (ι k₁) *ₙ r₂ +ₙ posVec (ι k₀)) *ₙ (r₁ *ₙ toℕ j₁ +ₙ toℕ j₀)
    ≡⟨ cong (λ f → (posVec (ι k₁) *ₙ r₂ +ₙ posVec (ι k₀)) *ₙ f) (sym (toℕ-combine j₁ j₀)) ⟩
      (toℕ k₁ *ₙ r₂ +ₙ toℕ k₀) *ₙ toℕ (combine j₁ j₀)
    ≡⟨ cong (_*ₙ toℕ (combine j₁ j₀)) (cong (_+ₙ toℕ k₀) (*ₙ-comm (toℕ k₁) r₂)) ⟩
      (r₂ *ₙ toℕ k₁ +ₙ toℕ k₀) *ₙ toℕ (combine j₁ j₀)
    ≡⟨ cong (_*ₙ toℕ (combine j₁ j₀)) (sym (toℕ-combine k₁ k₀)) ⟩
      toℕ (combine k₁ k₀) *ₙ toℕ (combine j₁ j₀)
    ≡⟨ cong (_*ₙ toℕ (combine j₁ j₀)) (sym (toℕ-cast (*ₙ-comm r₁ r₂) (combine k₁ k₀))) ⟩
      toℕ (cast _ (combine k₁ k₀)) *ₙ toℕ (combine j₁ j₀)
    ≡⟨⟩
      posVec (ι (cast _ (combine k₁ k₀))) *ₙ toℕ (combine j₁ j₀)
    ∎
  reorder-inner′′ : ∀
    (k₀ : Position (ι r₂)) 
    (k₁ : Position (ι r₁))
    →
      (((k₁ ⊗ k₀) ⟨ split ⟩) ⟨ flat ⟩) ≡
      (((((k₁ ⊗ k₀) ⟨ split ⟩) ⟨ reindex {r₂} {r₁} ⟩) ⟨ reindex {r₁} {r₂} ⟩) ⟨ flat {r₁} {r₂} ⟩)
  reorder-inner′′ {r₁} {r₂} (ι k₀) (ι k₁) rewrite 
      cast-trans (*ₙ-comm r₂ r₁) (*ₙ-comm r₁ r₂) (combine k₁ k₀) 
    | cast-is-id refl (combine k₁ k₀)
    = refl

  reorder-inner : ∀ 
    {arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ} 
    (j₀ : (Fin r₁)) 
    (j₁ : (Fin r₂))
    (k₀ : Position (ι r₂)) 
    (k₁ : Position (ι r₁))
    → 
       innerVal arr (ι j₁ ⊗ ι j₀) k₀ k₁
      ≡
       (λ pos →
            arr ((pos ⟨ reindex {r₁} {r₂} ⟩) ⟨ flat ⟩)
          * -ω (r₂ *ₙ r₁) (posVec pos *ₙ toℕ (combine j₁ j₀))) ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ )
  reorder-inner {r₁} {r₂} {arr} j₀ j₁ k₀ k₁ = begin
      arr (k₁ ⊗ k₀) 
      * -ω (r₂ *ₙ r₁) ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))
    ≡⟨ cong (_* -ω (r₂ *ₙ r₁) ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))) (cong arr (sym (rev-eq split (k₁ ⊗ k₀)))) ⟩
      arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ flat ⟩)
      * -ω (r₂ *ₙ r₁) ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))
    ≡⟨ cong (_* -ω (r₂ *ₙ r₁) ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))) (cong (arr) (reorder-inner′′ k₀ k₁)) ⟩
      arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ ⟨ reindex {r₁} {r₂} ⟩ ⟨ flat {r₁} {r₂} ⟩)
      * -ω (r₂ *ₙ r₁) ((toℕ j₁ *ₙ r₁ +ₙ toℕ j₀) *ₙ (posVec k₁ *ₙ r₂ +ₙ posVec k₀))
    ≡⟨ cong (arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ ⟨ reindex {r₁} {r₂} ⟩ ⟨ flat ⟩) *_) (cong (-ω (r₂ *ₙ r₁)) (reorder-inner′ {r₁} {r₂} {arr} j₀ j₁ k₀ k₁)) ⟩
      arr (((((k₁ ⊗ k₀) ⟨ split ⟩) ⟨ reindex {r₂} {r₁} ⟩) ⟨ reindex {r₁} {r₂} ⟩) ⟨ flat ⟩)
      * -ω (r₂ *ₙ r₁) (posVec (((k₁ ⊗ k₀) ⟨ split ⟩) ⟨ reindex {r₂} {r₁} ⟩) *ₙ toℕ (combine j₁ j₀))
    ∎


  theorm : ∀ {r₁ r₂ : ℕ} → ∀ (arr : Ar ((ι r₁) ⊗ (ι r₂)) ℂ)
    → FFT arr ≅ ((reshape _♯) ∘ DFT ∘ (reshape {ι r₁ ⊗ ι r₂} _♭₃)) arr
  theorm {r₁} {r₂} arr ((ι j₁) ⊗ (ι j₀)) = begin
      FFT arr (ι j₁ ⊗ ι j₀) 
    ≡⟨⟩
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
      foldr {r₂} _+_ 0ℂ 
        (λ k₀ →
           foldr {r₁} _+_ 0ℂ 
             (λ k₁ → innerVal arr (ι j₁ ⊗ ι j₀) k₀ k₁)
        )
    ≡⟨ foldr-cong _+_ 0ℂ (λ k₀ → foldr-cong _+_ 0ℂ (λ k₁ → reorder-inner {r₁} {r₂} {arr} j₀ j₁ k₀ k₁ )) ⟩
      foldr {r₂} _+_ 0ℂ 
        (λ k₀ →
           foldr {r₁} _+_ 0ℂ 
             (λ k₁ → 
               (λ pos →
                    arr ((pos ⟨ reindex {r₁} {r₂} ⟩) ⟨ flat ⟩)
                  * -ω (r₂ *ₙ r₁) (posVec pos *ₙ toℕ (combine j₁ j₀))) ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ )
             )
        )
    ≡⟨ (newMergeFoldr {r₁} {r₂} ((λ pos →
                   arr ((pos ⟨ reindex {r₁} {r₂} ⟩) ⟨ flat ⟩)
                 * -ω (r₂ *ₙ r₁) (posVec pos *ₙ toℕ (combine j₁ j₀))))) ⟩
      foldr {r₂ *ₙ r₁} _+_ (fromℝ (0 ᵣ))
              (λ pos →
                   arr ((pos ⟨ reindex {r₁} {r₂} ⟩) ⟨ flat ⟩)
                 * -ω (r₂ *ₙ r₁) (posVec pos *ₙ toℕ (combine j₁ j₀)))
    ≡⟨⟩
      (DFT (reshape (reindex {r₁} {r₂} ∙ flat) arr)) (ι (combine j₁ j₀))
    ≡⟨⟩
      reshape _♯ (DFT (reshape (reindex {r₁} {r₂} ∙ flat) arr)) (ι j₁ ⊗ ι j₀)
    ≡⟨ cong (λ f → (reshape _♯ (DFT ((reshape (reindex {r₁} {r₂} ∙ flat) (f))))) (ι j₁ ⊗ ι j₀)) (sym (eq+eq arr)) ⟩
      (reshape _♯ ∘ DFT ∘ reshape (reindex {r₁} {r₂} ∙ flat ∙ eq ⊕ eq)) arr
      (ι j₁ ⊗ ι j₀)
    ∎
