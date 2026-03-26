open import Matrix.Mon
open import ComplexNew

module FFT.Leveled.UFFT2 (cplx : Cplx) (M : Mon) where

open Mon M
open Cplx cplx

open import Matrix.Leveled M
open import FFT.Leveled.FFT cplx M
open import FFT.Leveled.UFFT cplx M

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

open import Function
open import Algebra.Definitions

private
  infixl 4 _⊡_
  _⊡_ = trans

  variable
    l : L
