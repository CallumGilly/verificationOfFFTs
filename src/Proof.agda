open import src.Real using (Real)
module src.Proof (r : Real) where

open import Data.Nat.Base using (ℕ; suc; zero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (*-zeroʳ)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import src.Matrix using (Ar; Shape; _⊗_; ι; _==_; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length)
open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; flatten; _⊕_; swap; eq; split; _⟨_⟩; reshape-reshape; eq+eq)
open import src.Complex r using (ℂ; _*_; _+_; ℂfromℕ; -ω; +-identityʳ; ω-N-0; *-identityʳ; _+_i)
open ℂ using (real; imaginary)
open import src.FFT r using (FFT; twiddles; position-sum; FFT₁)
open import src.DFTMatrix r using (DFT; posVec; step)
open import src.Extensionality using (extensionality)
open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ; +ᵣ-identityʳ; +ᵣ-assoc; +ᵣ-comm)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)

open import Function.Base using (_$_; id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

sub-θ : {s s₁ : Shape} (pos : Position (ι (length s))) → (p : Fin (length s *ₙ length s₁)) → ℝ 
sub-θ {s} {s₁} pos p = (((posVec pos *ₙ toℕ (proj₂ (quotRem {length s} (length s₁) p))) ᵣ) /ᵣ (length s ᵣ))

FFT₁≡FFT : ∀ {s : Shape} → FFT₁ {s} ≡ reshape (_♭ ∙ (rev recursive-transposeᵣ)) ∘ FFT {s} 
FFT₁≡FFT {ι x} = refl
FFT₁≡FFT {s ⊗ s₁} =
  extensionality λ{ arr → 
    extensionality λ{ (ι p) → 
      ?
    }
  }

--tmp : ∀ {n : ℕ} {real-arr complex-arr : Ar (ι n) ℝ} 
--  → foldr {n} _+_  ((0 ᵣ) + 0 ᵣ i) (λ pos → (real-arr pos) + (complex-arr pos)  i) ≡ 
--    foldr {n} _+ᵣ_  (0 ᵣ)          (λ pos → (real-arr pos)                       )
--                                                           +
--    foldr {n} _+ᵣ_         (0 ᵣ)   (λ pos →                  (complex-arr pos)) i
--tmp {zero } {real-arr} {complex-arr} = refl
--tmp {suc n} {real-arr} {complex-arr} =
--  begin
--    foldr _+_
--            (head₁ (λ pos → real-arr pos + complex-arr pos i) + ((0 ᵣ) + 0 ᵣ i))
--            (tail₁ (λ pos → real-arr pos + complex-arr pos i))
--  ≡⟨ tmp {?} {?} {?} ⟩
--    ?

-- TODO: Prove this (however that requires assoc and comm proofs for complex so will push till I know I need this
foldr-lemma₂ : ∀ {n : ℕ} {val acc : ℂ} {arr : Ar (ι n) ℂ} → foldr {n} _+_ (val + acc) arr ≡ val + (foldr {n} _+_ acc arr)
tail-ι-cons : ∀ {X : Set} {n : ℕ} {x : X} {xs : Ar (ι n) X} → tail₁ (ι-cons x xs) ≡ xs
prf : ∀ {n : ℕ} {real-arr complex-arr : Ar (ι (suc n)) ℝ}
    →
      (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
    ≡ 
      (tail₁ (λ pos → real-arr pos + complex-arr pos i))
--prf {n} {real-arr} {complex-arr} =
--  begin
--    (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
--   ≡⟨ sym (tail-ι-cons {ℂ} {n} {head₁ real-arr + head₁ complex-arr i} {λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i }) ⟩
--     tail₁ (ι-cons (head₁ real-arr + head₁ complex-arr i) (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i))
--  ≡⟨⟩
--     tail₁ (ι-cons (head₁ real-arr + head₁ complex-arr i) (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i))
--  ≡⟨⟩
--    ?
foldr-lemma₁ : ∀ {n : ℕ} {val acc : ℝ} {arr : Ar (ι n) ℝ} → foldr {n} _+ᵣ_ (val +ᵣ acc) arr ≡ val +ᵣ (foldr {n} _+ᵣ_ acc arr)
foldr-lemma₁ {zero } {val} {acc} {arr} = refl
foldr-lemma₁ {suc n} {val} {acc} {arr} =
  begin
    foldr _+ᵣ_ ((head₁ arr) +ᵣ (val +ᵣ acc)) (tail₁ arr)
  ≡⟨ cong (λ f → foldr _+ᵣ_ (f) (tail₁ arr)) (+ᵣ-comm (head₁ arr) (val +ᵣ acc)) ⟩
    foldr _+ᵣ_ ((val +ᵣ acc) +ᵣ head₁ arr) (tail₁ arr)
  ≡⟨ cong (λ f → foldr _+ᵣ_ (f) (tail₁ arr)) (+ᵣ-assoc val acc (head₁ arr)) ⟩
    foldr _+ᵣ_ (val +ᵣ (acc +ᵣ head₁ arr)) (tail₁ arr)
  ≡⟨ foldr-lemma₁ {n} {val} {acc +ᵣ head₁ arr} {tail₁ arr} ⟩
    (val +ᵣ foldr _+ᵣ_ (acc +ᵣ head₁ arr) (tail₁ arr))
  ≡⟨ cong (λ f → val +ᵣ (foldr _+ᵣ_ (f) (tail₁ arr))) (+ᵣ-comm acc (head₁ arr)) ⟩
    (val +ᵣ foldr _+ᵣ_ (head₁ arr +ᵣ acc) (tail₁ arr))
  ∎

+-in-ℂ-folding : ∀ {r₁ r₂ c₁ c₂ : ℝ} → (r₁ +ᵣ r₂) + (c₁ +ᵣ c₂) i ≡ (r₁ + c₁ i) + (r₂ + c₂ i)
+-in-ℂ-folding {r₁} {r₂} {c₁} {c₂} = refl

merge-foldr : ∀ {n : ℕ} {real-arr complex-arr : Ar (ι n) ℝ} 
  → foldr {n} _+ᵣ_  (0 ᵣ)          (λ pos → (real-arr pos)                       )
                                                           +
    foldr {n} _+ᵣ_         (0 ᵣ)   (λ pos →                  (complex-arr pos)) i
  ≡
    foldr {n} _+_  ((0 ᵣ) + 0 ᵣ i) (λ pos → (real-arr pos) + (complex-arr pos)  i) 
merge-foldr {zero} {real-arr} {complex-arr} = refl
merge-foldr {suc n} {real-arr} {complex-arr} =
  begin
      (foldr _+ᵣ_ (head₁ real-arr    +ᵣ (0 ᵣ)) (tail₁ real-arr   ) 
    + 
       foldr _+ᵣ_ (head₁ complex-arr +ᵣ (0 ᵣ)) (tail₁ complex-arr) 
    i)
  ≡⟨ cong (λ f → (f) + foldr _+ᵣ_ (head₁ complex-arr +ᵣ (0 ᵣ)) (tail₁ complex-arr) i) (foldr-lemma₁ {n} {head₁ real-arr} {0 ᵣ} {tail₁ real-arr}) ⟩
      (((head₁ real-arr) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ real-arr   )))
    + 
       foldr _+ᵣ_ (head₁ complex-arr +ᵣ (0 ᵣ)) (tail₁ complex-arr) 
    i)
  ≡⟨ cong (λ f → ((head₁ real-arr) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ real-arr   ))) + (f) i) (foldr-lemma₁ {n} {head₁ complex-arr} {0 ᵣ} {tail₁ complex-arr}) ⟩
      (((head₁ real-arr   ) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ real-arr   )))
    + 
       ((head₁ complex-arr) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ complex-arr)))
    i)
  ≡⟨⟩
    ((head₁ real-arr) + (head₁ complex-arr) i)
      +
    (   (foldr _+ᵣ_ (0 ᵣ) (tail₁ real-arr   ))
      +
        (foldr _+ᵣ_ (0 ᵣ) (tail₁ complex-arr))
      i
    )
  ≡⟨ cong (λ f → ((head₁ real-arr) + (head₁ complex-arr) i) + (f)) (merge-foldr {n} {tail₁ real-arr} {tail₁ complex-arr}) ⟩
    (head₁ real-arr + head₁ complex-arr i)
      +
    foldr _+_ ((0 ᵣ) + 0 ᵣ i) (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
  ≡⟨ sym (foldr-lemma₂ {n} {(head₁ real-arr) + (head₁ complex-arr) i} {(0 ᵣ) + 0 ᵣ i} {λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i }) ⟩
    foldr _+_ 
      ((head₁ real-arr + head₁ complex-arr i) + ((0 ᵣ) + 0 ᵣ i))
      (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
  ≡⟨ cong (λ f → foldr _+_ ((head₁ real-arr + head₁ complex-arr i) + ((0 ᵣ) + 0 ᵣ i)) (f)) (prf {n} {real-arr} {complex-arr}) ⟩
    foldr _+_ 
      ((head₁ real-arr + head₁ complex-arr i) + ((0 ᵣ) + 0 ᵣ i))
      (tail₁ (λ pos → real-arr pos + complex-arr pos i))
  ∎
  
    

      
--foldr-lemma₁ : ∀ {n : ℕ} {val acc : ℝ} {arr : Ar (ι n) ℝ} → foldr {n} _+ᵣ_ (val +ᵣ acc) arr ≡ val +ᵣ (foldr {n} _+ᵣ_ acc arr)
    
      

theorm₇ : ∀ {s : Shape} → FFT₁ {s} ≡ (DFT ∘ reshape _♭)
theorm₇ {ι x} = refl
theorm₇ {s₀ ⊗ s₁} =
  extensionality λ{ arr → 
    extensionality λ{ (ι p) → 
      begin
        FFT₁ arr (ι p)
      ≡⟨⟩
        reshape 
          (flat ∙ swap)
          (nestedMap FFT₁ 
            (reshape 
              swap 
              (zipWith _*_ (nestedMap FFT₁ arr) twiddles)
            )
          )
          (ι p)
      ≡⟨ cong (λ f → reshape (flat ∙ swap) (nestedMap FFT₁ (reshape swap (zipWith _*_ (nestedMap f arr) twiddles))) (ι p)) theorm₇ ⟩
        reshape 
          (flat ∙ swap)
          (nestedMap FFT₁ 
            (reshape 
              swap 
              (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles)
            )
          )
          (ι p)
      ≡⟨ cong (λ f → reshape (flat ∙ swap) (nestedMap f (reshape swap (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles))) (ι p)) theorm₇ ⟩
        reshape 
          (flat ∙ swap)
          (nestedMap (DFT ∘ reshape _♭)
            (reshape 
              swap 
              (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles)
            )
          )
          (ι p)
      ≡⟨⟩
        map DFT (
        map (reshape _♭) (
          nest (reshape swap (zipWith _*_ (unnest (map DFT (map (reshape _♭) (nest arr)))) twiddles))
        )) (ι j₁) (ι j₀)
      ≡⟨⟩
        foldr _+_ ((0 ᵣ) + 0 ᵣ i)
            (λ pos →
               ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
                -ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ sin (θ pos p)))
               +
                (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ sin (θ pos p))
                +ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
               i)
      ≡⟨ sym (merge-foldr {length s₀} {
          (λ pos → ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)) -ᵣ (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))) *ᵣ cos (θ pos p)) -ᵣ (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)) +ᵣ (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))) *ᵣ sin (θ pos p))))
        } {
          (λ pos → (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)) -ᵣ (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))) *ᵣ sin (θ pos p)) +ᵣ (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)) +ᵣ (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))) *ᵣ cos (θ pos p)))
        }) ⟩
        foldr _+ᵣ_ (0 ᵣ)
            (λ pos →
               ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
                -ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ sin (θ pos p)))
               )
       +
        foldr _+ᵣ_ (0 ᵣ)
            (λ pos →
                (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ sin (θ pos p))
                +ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
               )
       i
          ≡⟨⟩
            ? -- TODO: Talk to Artjoms about where to go from here, stuck at this stage and this split hasn't really helped me
    }
  }
  where
    j₀ : {p : Position (ι (length s₀ *ₙ length s₁))} → Fin (length s₀)
    j₀ {ι p} = proj₂ (quotRem {length s₀} (length s₁) p)
    j₁ : {p : Position (ι (length s₀ *ₙ length s₁))} → Fin (length s₁)
    j₁ {ι p} = proj₁ (quotRem {length s₀} (length s₁) p)

    θ : (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → ℝ
    θ pos p = ((-ᵣ 2 ᵣ *ᵣ π *ᵣ (posVec pos *ₙ toℕ j₀) ᵣ) /ᵣ (length s₀ ᵣ))

    θ₂ : (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → ℝ
    θ₂ pos p = (-ᵣ 2 ᵣ *ᵣ π *ᵣ
                    (position-sum {s₀} (pos ⟨ _♭ ⟩) *ₙ
                     position-sum (ι (j₁)))
                    ᵣ)
                   /ᵣ ((length s₀ *ₙ length s₁) ᵣ)
    innerDFT : (arr : Ar (s₀ ⊗ s₁) ℂ) → (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → ℂ
    innerDFT arr pos p = (foldr _+_ ((0 ᵣ) + 0 ᵣ i)
                    (λ pos₁ →
                       ((real (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                         cos
                         ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                           (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                          /ᵣ (length s₁ ᵣ)))
                        -ᵣ
                        (imaginary (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                         sin
                         ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                           (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                          /ᵣ (length s₁ ᵣ))))
                       +
                       (real (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                        sin
                        ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                          (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                         /ᵣ (length s₁ ᵣ)))
                       +ᵣ
                       (imaginary (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                        cos
                        ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                          (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                         /ᵣ (length s₁ ᵣ)))
                       i))
    --hypothetical : (arr : Ar (s₀ ⊗ s₁) ℂ) → (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → 
    --    (((real (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)) -ᵣ (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))) *ᵣ cos (θ pos p))
    --  ≡
    --    (real (arr ((pos ⟨ flat ⟩) ⟨ _♭ ⊕ _♭ ⟩)) *ᵣ cos ((-ᵣ 2 ᵣ *ᵣ π *ᵣ (posVec pos *ₙ toℕ p) ᵣ) /ᵣ ((length s₀ *ₙ length s₁) ᵣ)))




-- lemma₁ : ∀ 
--   {s s₁ : Shape}
--   {pos  : Position (ι (length s₁))}
--   {p    : Fin (length s *ₙ length s₁)}
--   → 
--     (((posVec pos *ₙ toℕ                                        p)   ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ)) 
--   ≡ 
--     (((posVec pos *ₙ toℕ {length s} (proj₂ (quotRem {length s} (length s₁) p))) ᵣ) /ᵣ ( length s               ᵣ))
-- lemma₁ {s} {s₁} {ι x} {p} =
--   begin
--     (((posVec (ι x) *ₙ toℕ p) ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ))
--   ≡⟨⟩
--     (((toℕ x *ₙ toℕ p) ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ))
--   ≡⟨⟩
--     ?






