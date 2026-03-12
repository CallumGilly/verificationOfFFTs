{-# OPTIONS --allow-unsolved-metas #-}
open import Complex using (Cplx)
open import Matrix.Mon


module FFT.Parameterised.FFT (cplx : Cplx) (M : Mon) where

open Cplx cplx using (ℂ) renaming (_*_ to _*ᶜ_)

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (raise)
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)
open import Data.Product.Properties
open import Data.Sum as Sum hiding (swap; map)

--postulate
--  ℂ : Set
--  _*ᶜ_ : ℂ → ℂ → ℂ

private
  infixl 4 _⊡_
  _⊡_ = trans


open import Matrix.Parameterised M
open import Matrix.Parameterised.Levels
open Mon M using (U; El)
--open A M
open PL M

private
  variable
    s p : S
    n : U

fft : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
      (twid : ∀ {s p} → P s → P p → ℂ)
    → Ar s ℂ → Ar (transp s) ℂ
fft {s = ι n} dft twid = dft
fft {s = s ⊗ p} dft twid a =
  let 
    b = map (fft dft twid) (nest (reshape swap a))
    c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
    d = map (fft dft twid) (nest (reshape swap c))
  in reshape swap (unnest d)


fft-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
            {twid : ∀ {s p} → P s → P p → ℂ}
          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {n} a i ≡ dft b i)
          → ∀ {s} a b → (∀ i → a i ≡ b i)
          → ∀ i → fft {s} dft twid a i ≡ fft dft twid b i
fft-cong dft-cong {ι x} a b a≡b i = dft-cong a b a≡b i
fft-cong dft-cong {s ⊗ p} a b a≡b (i ⊗ j) = fft-cong 
      dft-cong _ _
      (λ k → cong (_ *ᶜ_) 
                  (fft-cong 
                      dft-cong _ _ 
                      (λ l → a≡b (l ⊗ k))
                      j))
      i

fft-dft-cong : ∀ (dft₁ dft₂ : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
             → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
             → (dft₂-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                          → ∀ i → dft₂ {n} a i ≡ dft₂ b i)
             → ∀ {s : S}
             → ∀ (xs : Ar s ℂ)
             → (prf : ∀ {n} → ∀ (ys : Ar (ι n) ℂ) → ∀ j → dft₁ ys j ≡ dft₂ ys j)
             → ∀ i
             → fft dft₁ twid xs i ≡ fft dft₂ twid xs i
fft-dft-cong dft₁ dft₂ {twid} _ {ι x} xs prf = prf xs
fft-dft-cong dft₁ dft₂ {twid} dft₂-cong {s₁ ⊗ s₂} xs prf (i₁ ⊗ i₂) =
    fft-dft-cong _ _ dft₂-cong _ prf i₁
  ⊡ fft-cong dft₂-cong _ _ (λ j → cong₂ _*ᶜ_ refl (fft-dft-cong _ _ dft₂-cong _ prf i₂)) i₁

