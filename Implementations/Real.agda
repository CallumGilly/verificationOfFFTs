{-# OPTIONS --guardedness #-}

open import Real using (Real)

import Agda.Builtin.Float as Float 

open import Data.Nat using (ℕ; _*_)

open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatACos; primFloatSin; primShowFloat)
open Float using (primRatioToFloat)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Agda.Builtin.String

open import Algebra.Structures {A = Float} _≡_

module Implementations.Real where
  postulate 
    +-*-isCommutativeRing : IsCommutativeRing primFloatPlus primFloatTimes primFloatNegate (primNatToFloat 0) (primNatToFloat 1)

    0/N≡0 : ∀ (N : Float) → primFloatDiv (primNatToFloat 0) N ≡ (primNatToFloat 0)

    cos0 : primFloatCos (primNatToFloat 0) ≡ (primNatToFloat 1)
    sin0 : primFloatSin (primNatToFloat 0) ≡ (primNatToFloat 0)

    cos-2πn : ∀ (n : ℕ) → primFloatCos (primFloatTimes (primFloatNegate (primFloatTimes (primNatToFloat 2) (primFloatACos (primFloatNegate (primNatToFloat 1))))) (primNatToFloat n)) ≡ primNatToFloat 1
    sin-2πn : ∀ (n : ℕ) → primFloatSin (primFloatTimes (primFloatNegate (primFloatTimes (primNatToFloat 2) (primFloatACos (primFloatNegate (primNatToFloat 1))))) (primNatToFloat n)) ≡ primNatToFloat 0

    ᵣ-distrib-* : ∀ (n m : ℕ) → primNatToFloat (n * m) ≡ primFloatTimes (primNatToFloat n) (primNatToFloat m)
    -distrib-* : ∀ (n m : Float) → primFloatTimes (primFloatNegate n) m ≡ primFloatNegate (primFloatTimes n m)

    Nm/N≡m : ∀ (N m : Float) → primFloatDiv (primFloatTimes N m) N ≡ m

  module Base where
    realImplementation : Real
    realImplementation = record
     { ℝ               = Float
     ; _ᵣ              = primNatToFloat
     ; π               = primFloatACos (primFloatNegate (primNatToFloat 1))
     ; _+_             = primFloatPlus
     ; _-_             = primFloatMinus
     ; _*_             = primFloatTimes
     ; _/_             = primFloatDiv
     ; -_              = primFloatNegate
     ; cos             = primFloatCos
     ; sin             = primFloatSin

     ; +-*-isCommutativeRing = +-*-isCommutativeRing
     ; 0/N≡0 = 0/N≡0
     
     ; cos0 = cos0
     ; sin0 = sin0

     ; cos-2πn = cos-2πn
     ; sin-2πn = sin-2πn

     ; ᵣ-distrib-* = ᵣ-distrib-*
     ; -distrib-* = -distrib-*

     ; Nm/N≡m = Nm/N≡m
     }

  open Base public
  open Real.Real realImplementation
  
  showℝ : ℝ → String
  showℝ = primShowFloat

