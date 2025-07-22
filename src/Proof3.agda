open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app; trans)
open Eq.≡-Reasoning

module src.Proof3 (real : Real) (cplx : Cplx real) where

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

  open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr; splitAr; splitArₗ; splitArᵣ; toFin)
  open import src.Matrix.Equality using (_≅_; foldr-cong; eq+eq≅arr; reduce-≅; tail₁-cong)
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

  sum : ∀ {m : ℕ} → (arr : Ar (ι m) ℂ) → ℂ
  sum {zero} arr = 0ℂ
  sum {suc m} arr = (arr (ι fzero)) + (sum ∘ tail₁) arr

  sum-nil : ∀ {n : ℕ} (arr : Ar (ι n) ℂ) (prf : n ≡ 0) → sum arr ≡ 0ℂ
  sum-nil {zero} arr prf = refl

  tail₁-const : ∀ {n : ℕ} {c : ℂ} → tail₁ {n} (λ i → c) ≅ (λ j → c)
  tail₁-const {zero} {c} (ι x) = refl
  tail₁-const {suc n} {c} (ι x) = refl

  sum-cong : ∀ {n : ℕ} → {xs ys : Ar (ι n) ℂ} → xs ≅ ys → sum xs ≡ sum ys
  sum-cong {zero } {xs} {ys} prf = refl
  sum-cong {suc n} {xs} {ys} prf = cong₂ _+_ (prf (ι fzero)) (sum-cong {n} {tail₁ xs} {tail₁ ys} (reduce-≅ prf))

  sum-zeros : ∀ {n : ℕ} → sum {n} (λ i → 0ℂ) ≡ 0ℂ 
  sum-zeros {zero} = refl
  sum-zeros {suc n} rewrite 
      sum-cong {n} (tail₁-const {n} {0ℂ}) 
    | sum-zeros {n}
    | +-identityʳ 0ℂ
    = refl

  foldr≡sum : ∀ {m : ℕ} (arr : Ar (ι m) ℂ) → foldr {m} _+_ 0ℂ arr ≡ sum {m} arr
  foldr≡sum {zero} arr = refl
  foldr≡sum {suc m} arr rewrite 
      foldr-pull-out {m} (arr (ι fzero)) 0ℂ (tail₁ arr) 
    | foldr≡sum {m} (tail₁ arr)
    = refl

  splitArᵣ-zero : ∀ {n : ℕ} (arr : Ar (ι n) ℂ) → splitArᵣ {0} arr ≅ arr
  splitArᵣ-zero {n} arr (ι i) = refl
  
  splitSum : ∀ {m n : ℕ} → (arr : Ar (ι (n +ₙ m)) ℂ) → sum arr ≡ sum (splitArₗ {n} arr) + sum (splitArᵣ {n} arr)
  splitSum {m} {zero} arr rewrite
      +-identityˡ (sum (splitArᵣ {0} arr)) = sum-cong {m} (λ{(ι i) → refl })
  splitSum {m} {suc n} arr rewrite
      +-assoc (arr (ι fzero)) (sum (tail₁ (splitArₗ {suc n} arr))) (sum (splitArᵣ {suc n} arr))
    = cong₂ _+_ refl 
        ( trans 
            (splitSum {m} {n} (tail₁ arr)) 
            ( cong₂ _+_ 
              (sum-cong {n} λ{(ι i) → refl }) 
              (sum-cong {m} λ{(ι j) → refl }) 
            )
        )

  mergeSumₗ : ∀ {m n : ℕ} → (arr : Ar (ι (suc m *ₙ suc n)) ℂ) → (tail₁ (λ j → arr ((ι (fzero {m}) ⊗ j) ⟨ split ⟩))) ≅ (splitArₗ {n} (tail₁ arr))
  mergeSumₗ {m} {n} arr (ι i) = cong (arr ∘ ι) refl

  --mergeSumᵣ : ∀ {m n : ℕ} → (arr : Ar (ι (suc (n +ₙ m *ₙ suc n))) ℂ) → 
  --      (tail₁ {?} (λ i → arr ((i ⊗ ι (fzero {?} )) ⟨ split {?} {?} ⟩) + sum (tail₁ {?} (λ j → arr ((i ⊗ j) ⟨ split {?} {?} ⟩)))))
  --    ≅ 
  --      (splitArᵣ {n} {m *ₙ suc n} (tail₁ arr))

  
  sum-tail₁ : ∀ {n : ℕ} (arr : Ar (ι (suc n)) ℂ) → sum {n} (tail₁ (λ i → arr i)) ≡ sum {n} (λ i → (splitArᵣ (tail₁ arr)) i)
  sum-tail₁ {zero} arr = refl
  sum-tail₁ {suc n} arr rewrite 
      sum-tail₁ {n} (tail₁ arr) 
    | sum-cong (splitArᵣ-zero (tail₁ (tail₁ arr))) 
    | sum-cong (tail₁-cong (splitArᵣ-zero (tail₁ arr)))
    = refl

    
  mergeSum : ∀ {m n : ℕ} → (arr : Ar (ι (m *ₙ n)) ℂ) → sum {m} (λ i → sum {n} (λ j → arr ((i ⊗ j) ⟨ split ⟩ ))) ≡ sum arr
  mergeSum {zero} {n} arr = refl
  mergeSum {suc m} {zero} arr rewrite 
      sum-nil arr (*ₙ-zeroʳ m) 
    | +-identityˡ (sum {m} (tail₁ (λ i → 0ℂ)))
    | sum-cong (tail₁-const {m} {0ℂ})
    | sum-zeros {m}
    = refl
  mergeSum {suc m} {suc n} arr 
    rewrite splitSum {m *ₙ suc n} {n} (tail₁ arr) rewrite 
        sym (+-assoc (arr (ι fzero)) (sum (splitArₗ {n} (tail₁ arr))) (sum (splitArᵣ {n} (tail₁ arr))))
      | sum-cong (mergeSumₗ {m} {n} arr)
      = cong₂ _+_ refl 
        (trans 
          (sum-cong {m} (λ{ (ι i) → cong₂ _+_ refl (sum-cong {n} (λ{(ι j) → refl})) }))
          (mergeSum {m} {suc n} (splitArᵣ {n} (tail₁ arr)))
        )

  distrib-tail₁ : ∀ {n : ℕ} (xs ys : Ar (ι (suc n)) ℂ) → sum (tail₁ (λ i → xs i + ys i)) ≡ sum (λ i → (tail₁ xs) i + (tail₁ ys) i)
  distrib-tail₁ {n} xs ys = sum-cong {n} λ{(ι i) → refl }


  expand-sum : ∀ {n : ℕ} (xs ys : Ar (ι (n)) ℂ) → sum (λ i → xs i + ys i) ≡ sum (λ i → xs i) + sum (λ i → ys i)
  expand-sum {zero} xs ys rewrite +-identityʳ 0ℂ = refl
  expand-sum {suc n} xs ys rewrite
      +-assoc (xs (ι fzero)) (ys (ι fzero)) (sum (tail₁ (λ i → xs i + ys i)))
    | +-assoc (xs (ι fzero)) (sum (tail₁ xs)) (ys (ι fzero) + sum (tail₁ ys))
    | +-comm  (sum (tail₁ xs)) (ys (ι fzero) + sum (tail₁ ys))
    | +-assoc (ys (ι fzero)) (sum (tail₁ ys)) (sum (tail₁ xs))
    | distrib-tail₁ xs ys
    | expand-sum (tail₁ xs) (tail₁ ys)
    | +-comm (sum (tail₁ xs)) (sum (tail₁ ys))
    = refl


  {-
  expandˡ-tail₁ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc m))) → tail₁ (a p) ≅ (λ{(ι j) → a p (ι (fsuc j))})
  expandˡ-tail₁ a p (ι x) = refl

  expandʳ-tail₁ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc n))) → tail₁ (λ i → a i p) ≅ (λ{(ι i) → a (ι (fsuc i)) p})
  expandʳ-tail₁ a p (ι x) = refl

  sumSwap-helperˡ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc n))) → tail₁ (λ i → a i p + sum (tail₁ (a i))) ≅ (λ{(ι i) → a (ι (fsuc i)) p + sum (λ{(ι j) → a (ι (fsuc i)) (ι (fsuc j))})})
  sumSwap-helperˡ {m} {n} a p (ι x) rewrite sum-cong (expandˡ-tail₁ a (ι (fsuc x))) = cong₂ _+_ refl (sum-cong {n} (λ{(ι j) → refl }))

  sumSwap-helperʳ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc n))) → tail₁ (λ j → a (ι fzero) j + sum (tail₁ (λ i → a i j))) ≅ (λ{ (ι j) → a (ι fzero) (ι (fsuc j)) + sum (λ{ (ι i) → a (ι (fsuc i)) (ι (fsuc j))})})
  sumSwap-helperʳ {m} {n} a p (ι x) rewrite sum-cong (expandʳ-tail₁ a (ι (fsuc x))) = cong₂ _+_ refl (sum-cong {m} (λ{(ι i) → refl }))
  -}

  {-
  expandˡ-tail₁ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc m))) → tail₁ (a p) ≅ (λ j → (tail₁ (a p)) j)
  expandˡ-tail₁ a p (ι x) = refl

  expandʳ-tail₁ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc n))) → tail₁ (λ i → a i p) ≅ (λ i → (tail₁ a) i p)
  expandʳ-tail₁ a p (ι x) = refl
  -}

  sumSwap-helperˡ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc n))) → tail₁ (λ i → a i p + sum (tail₁ (a i))) ≅ (λ i → (tail₁ a) i p + sum (λ j → (tail₁ ((tail₁ a) i)) j))
  sumSwap-helperˡ {m} {n} a p (ι x) = cong₂ _+_ refl (sum-cong {n} (λ{(ι j) → refl }))

  sumSwap-helperʳ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) → (p : Position (ι (suc n))) → tail₁ (λ j → a (ι fzero) j + sum (tail₁ (λ i → a i j))) ≅ (λ j → (tail₁ (a (ι fzero))) j + sum (λ i → tail₁ ((tail₁ a) i) j))
  sumSwap-helperʳ {m} {n} a p (ι x) = cong₂ _+_ refl (sum-cong {m} (λ{(ι i) → refl }))


  --expand-sum-applicationˡ : ∀ {m n : ℕ} → (a : Position (ι (suc m)) → Position (ι (suc n)) → ℂ) →
  --          sum {m} (λ { (ι i) → 
  --              a (ι (fsuc i)) (ι fzero) 
  --            + sum (λ { (ι j) → a (ι (fsuc i)) (ι (fsuc j)) })
  --          })
  --          ≡
  --          sum {m} (λ { (ι i) → 
  --              a (ι (fsuc i)) (ι fzero) 
  --          })
  --          +
  --          sum {m} (λ { (ι i) → 
  --            sum (λ { (ι j) → a (ι (fsuc i)) (ι (fsuc j)) })
  --          })
  --expand-sum-applicationˡ {m} {n} a = trans (expand-sum {m} ? ?) ?


  sumSwap : ∀ {m n : ℕ} → (a : Position (ι m) → Position (ι n) → ℂ) → sum {m} (λ i → sum {n} (λ j → a i j)) ≡ sum {n} (λ j → sum {m} (λ i → a i j))
  sumSwap {zero} {n} a rewrite sum-zeros {n} = refl
  sumSwap {suc m} {zero} a rewrite
      sum-cong {m} (tail₁-const {m} {0ℂ}) 
    | sum-zeros {m} 
    | +-identityʳ 0ℂ = refl
  sumSwap {suc m} {suc n} a rewrite
      +-assoc (a (ι fzero) (ι fzero)) (sum (tail₁ (a (ι fzero))))         (sum (tail₁ (λ i → a i (ι fzero) + sum (tail₁ (a i)))))
    | +-assoc (a (ι fzero) (ι fzero)) (sum (tail₁ (λ i → a i (ι fzero)))) (sum (tail₁ (λ j → a (ι fzero) j + sum (tail₁ (λ i → a i j)))))
    | sum-cong (sumSwap-helperˡ a (ι fzero))
    | sum-cong (sumSwap-helperʳ a (ι fzero))
    | expand-sum (λ z → tail₁ a z (ι fzero)) (λ z → sum (tail₁ (tail₁ a z)))        -- z here is a horrible varaible name but it was auto assigned and works
    | expand-sum (tail₁ (a (ι fzero)))  (λ z → sum (λ i → (tail₁ (tail₁ a i) z)))
    | sym (+-assoc (sum (tail₁ (a (ι fzero))))         (sum (λ z → tail₁ a z (ι fzero))) (sum (λ z → sum (tail₁ (tail₁ a z)))))
    | sym (+-assoc (sum (tail₁ (λ i → a i (ι fzero)))) (sum (tail₁ (a (ι fzero))))       (sum (λ z → sum (λ i → tail₁ (tail₁ a i) z))))
    | +-comm (sum (tail₁ (a (ι fzero)))) (sum (λ z → tail₁ a z (ι fzero)))
    = cong₂ _+_ refl (cong₂ _+_ (cong₂ _+_ (sum-cong {m} (λ{(ι z) → refl })) refl) (trans (sumSwap (λ z → (tail₁ (tail₁ a z)))) refl))

  
  ext : ∀ {m n : ℕ} → (arr : Ar (ι m) ℂ) → (prf : m ≡ n)
      → subst (λ s → Ar (ι s) ℂ) prf arr ≅ (reshape (comm-eq (sym prf)) arr)
  ext arr refl (ι x) = cong arr (cong ι (sym (cast-is-id refl x)))


  cong-sum-comm-eq : ∀ {m n : ℕ} (arr : Ar (ι m) ℂ) (prf : m ≡ n)
           → sum arr ≡ sum (reshape (comm-eq (sym prf)) arr)
  cong-sum-comm-eq {m} {n} arr refl = sum-cong {m} {arr} {reshape (comm-eq refl) arr} (ext arr refl)

  reindex-is-comm-eq : ∀ {m n : ℕ} {arr : Ar (ι (m *ₙ n)) ℂ} → reshape (comm-eq (sym (*ₙ-comm m n))) arr ≅ reshape (reindex {m}) arr
  reindex-is-comm-eq {m} {n} (ι x) = refl

  sumReindex : ∀ {m n : ℕ} → (arr : Ar (ι (m *ₙ n)) ℂ) → sum arr ≡ sum (reshape (reindex {m}) arr)
  sumReindex {m} {n} arr = trans (cong-sum-comm-eq arr (*ₙ-comm m n)) (sum-cong (reindex-is-comm-eq {m} {n} {arr}))

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
  newMergeFoldr {r₁} {r₂} arr rewrite 
      foldr≡sum arr 
    | foldr≡sum (λ k₀ → foldr {r₁} _+_ 0ℂ (λ k₁ → arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ )))
    | sum-cong  (λ k₀ → foldr≡sum {r₁} (λ k₁ → arr ((k₁ ⊗ k₀) ⟨ split ⟩ ⟨ reindex {r₂} {r₁} ⟩ )))
    | sumSwap {r₂} {r₁} (λ i j → arr ((j ⊗ i) ⟨ split ∙ reindex {r₂} ⟩ ))
    | mergeSum {r₁} (reshape (reindex {r₂}) arr)
    | sumReindex {r₂} arr
    = refl




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

  zipWith-congˡ : ∀ {s : Shape} {X Y Z : Set} {xs ys : Ar s X} {zs : Ar s Y} {f : X → Y → Z} → xs ≅ ys → zipWith f xs zs ≅ zipWith f ys zs
  zipWith-congˡ {s} {X} {Y} {Z} {xs} {ys} {zs} {f} prf i = cong₂ f (prf i) refl

  zipWith-congʳ : ∀ {s : Shape} {X Y Z : Set} {xs : Ar s X} {ys zs : Ar s Y} {f : X → Y → Z} → ys ≅ zs → zipWith f xs ys ≅ zipWith f xs zs
  zipWith-congʳ {s} {X} {Y} {Z} {xs} {ys} {zs} {f} prf i = cong₂ f refl    (prf i)

  DFT-cong : ∀ {n : ℕ} {xs ys : Ar (ι n) ℂ} → xs ≅ ys → DFT xs ≅ DFT ys
  DFT-cong {n} {xs} {ys} prf (ι x) = foldr-cong {ℂ} {ℂ} {n} _+_ 0ℂ (zipWith-congˡ {zs = posVec} {f = (λ xₙ n₁ → xₙ * -ω n (n₁ *ₙ toℕ x))} prf )

  FFT-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → xs ≅ ys → FFT xs ≅ FFT ys
  FFT-cong {ι x   } {xs} {ys} prf i = DFT-cong prf i
  FFT-cong {s ⊗ s₁} {xs} {ys} prf (i ⊗ i₁) = (FFT-cong {s₁} λ { j₁ → (cong₂ _*_ ((FFT-cong {s} λ {j₂ → prf (j₂ ⊗ j₁) }) i₁ ) refl) }) i

  main-theorm : ∀ {s : Shape} → ∀ (arr : Ar s ℂ)
    → FFT arr ≅ ((reshape _♯) ∘ DFT ∘ (reshape {s} _♭₃)) arr
  main-theorm {ι r} arr i = refl
  main-theorm {ι r₁ ⊗ ι r₂} arr i = theorm arr i
  main-theorm {ι r₁ ⊗ (s₁ ⊗ s₂)} arr ((i₁ ⊗ i₂) ⊗ ι i₃) = 
    trans 
      ( FFT-cong (λ j → 
        cong₂ _*_ 
          (main-theorm (nest (reshape swap (nest (zipWith _*_ (reshape swap (nestedMap FFT (reshape swap arr))) twiddles) (ι i₃))) j) i₂) 
          refl
        ) i₁
      )
      ( trans
        (main-theorm (λ z →
                         (reshape {(ι (length (recursive-transpose s₁)))} {recursive-transpose s₁} _♯ ∘ DFT ∘ reshape _♭₃)
                         (nest
                          (reshape swap
                           (nest
                            (zipWith _*_ (reshape swap (nestedMap FFT (reshape swap arr)))
                             twiddles)
                            (ι i₃)))
                          z)
                         i₂
                         * twiddles (i₂ ⊗ z)) i₁)
        ( begin
            ( reshape {ι (length (recursive-transpose s₂))} {recursive-transpose s₂} _♯ 
              ( DFT 
                ( reshape _♭₃
                  (λ z →
                    reshape _♯
                      ( DFT
                        ( reshape _♭₃
                          ( nest
                            ( reshape swap
                              ( nest
                                ( zipWith _*_
                                  ( reshape swap (nestedMap (λ arr₁ → DFT arr₁) (reshape swap arr)))
                                  twiddles
                                ) (ι i₃)
                              )
                            ) z
                          )
                        )
                      ) i₂
                    * twiddles (i₂ ⊗ z)
                  )
                )
              ) i₁
            )
          ≡⟨⟩ 
            ( reshape {ι (length (recursive-transpose s₂))} {recursive-transpose s₂} _♯ 
              ( DFT 
                ( reshape _♭₃
                  (λ z →
                    reshape _♯
                      ( DFT
                        ( reshape _♭₃
                          ( nest
                            ( reshape swap
                              ( nest
                                ( zipWith _*_
                                  ( reshape swap (nestedMap (λ arr₁ → DFT arr₁) (reshape swap arr)))
                                  twiddles
                                ) (ι i₃)
                              )
                            ) z
                          )
                        )
                      ) i₂
                    * twiddles (i₂ ⊗ z)
                  )
                )
              ) i₁
            )
          ≡⟨⟩
            DFT
            (λ ix →
               DFT
               (λ ix₁ →
                  foldr _+_ (fromℝ (0 ᵣ))
                  (λ pos →
                     arr (pos ⊗ ((ix₁ ⟨ _♭₃ ⟩) ⊗ (ix ⟨ _♭₃ ⟩))) *
                     -ω r₁ (posVec pos *ₙ toℕ i₃))
                  *
                  -ω (r₁ *ₙ (length s₁ *ₙ length s₂))
                  (toℕ i₃ *ₙ
                   (offset-n ((ix₁ ⟨ _♭₃ ⟩) ⊗ (ix ⟨ _♭₃ ⟩)))))
               (i₂ ⟨ rev _♭ ⟩)
               *
               -ω (length (recursive-transpose s₁) *ₙ length s₂)
               ((offset-n i₂) *ₙ (offset-n {s₂} (ix ⟨ _♭₃ ⟩))))
            (i₁ ⟨ rev _♭ ⟩)
          ≡⟨⟩
            ?


        )
      )
    --begin
    --  FFT (λ j →
    --    FFT (λ j₁ →
    --      foldr _+_ (fromℝ (0 ᵣ)) (λ pos →
    --        arr (pos ⊗ (j₁ ⊗ j)) * -ω r₁ (posVec pos *ₙ toℕ i₃)
    --      )
    --      * -ω (r₁ *ₙ (length s₁ *ₙ length s₂)) (toℕ i₃ *ₙ (offset-n (j₁ ⊗ j)))
    --    ) i₂
    --    *
    --    -ω (length (recursive-transpose s₁) *ₙ length s₂) ((offset-n i₂) *ₙ (offset-n j ))
    --  ) i₁
    --≡⟨ FFT-cong ? i₁ ⟩
    --  FFT (λ j →
    --    FFT (λ j₁ →
    --      foldr _+_ (fromℝ (0 ᵣ)) (λ pos →
    --        arr (pos ⊗ (j₁ ⊗ j)) * -ω r₁ (posVec pos *ₙ toℕ i₃)
    --      )
    --      * -ω (r₁ *ₙ (length s₁ *ₙ length s₂)) (toℕ i₃ *ₙ (offset-n (j₁ ⊗ j)))
    --    ) i₂
    --    *
    --    -ω (length (recursive-transpose s₁) *ₙ length s₂) ((offset-n i₂) *ₙ (offset-n j ))
    --  ) i₁
    --≡⟨⟩
    --  ?

  main-theorm {(s ⊗ s₂) ⊗ s₁} arr i = ?


















