{-# OPTIONS --guardedness #-}

open import Real using (Real)

import Agda.Builtin.Float as Float 

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
     }
  open Base public
  open Real.Real realImplementation
  
  showℝ : ℝ → String
  showℝ = primShowFloat

