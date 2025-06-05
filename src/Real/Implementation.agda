{-# OPTIONS --guardedness #-}

open import src.Real.Base using (RealBase)
open import src.Real.Properties using (RealProperties)

import Agda.Builtin.Float as Float 

open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatACos; primFloatSin; primShowFloat)
open Float using (primRatioToFloat)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

module src.Real.Implementation where
  module Base where
    realBaseImplementation : RealBase
    realBaseImplementation = record
     { ℝ               = Float
     ; 0ℝ              = (primNatToFloat 0)
     ; -1ℝ             = (primFloatNegate (primNatToFloat 1))
     ; 1ℝ              = (primNatToFloat 1)
     ; _ᵣ              = primNatToFloat
     ; π               = primFloatACos (primFloatNegate (primNatToFloat 1))
     ; _+_             = primFloatPlus
     ; _-_             = primFloatMinus
     ; _*_             = primFloatTimes
     ; _/_             = primFloatDiv
     ; -_              = primFloatNegate
     ; cos             = primFloatCos
     ; sin             = primFloatSin
     }
  open Base public
  open RealBase realBaseImplementation

  module Properties where
    open import Algebra.Structures  {A = ℝ} _≡_
    open import Algebra.Definitions {A = ℝ} _≡_

    realPropertiesImplementation : RealProperties realBaseImplementation
    realPropertiesImplementation = record {
      }
  open Properties public
  open RealProperties realPropertiesImplementation

-- builtinReals : Real
-- builtinReals = record
--   { ℝ = Float
--   ; _ᵣ              = primNatToFloat
--   ; π               = primFloatACos (primFloatNegate (primNatToFloat 1))
--   ; _+_             = primFloatPlus
--   ; _-_             = primFloatMinus
--   ; _*_             = primFloatTimes
--   ; _/_             = primFloatDiv
--   ; -_              = primFloatNegate
--   ; cos             = primFloatCos
--   ; sin             = primFloatSin
--   ; double-negative = double-negative
--   ; *ᵣ-zeroᵣ        = *ᵣ-zeroᵣ
--   ; /ᵣ-zeroₜ        = /ᵣ-zeroₜ
--   ; +ᵣ-identityˡ    = +ᵣ-identityˡ  
--   ; +ᵣ-identityʳ    = +ᵣ-identityʳ  
--   ; -ᵣ-identityʳ    = -ᵣ-identityʳ  
--   ; *ᵣ-identityʳ    = *ᵣ-identityʳ  
--   ; neg-distrib-*   = neg-distrib-* 
--   ; *ᵣ-assoc        = *ᵣ-assoc      
--   ; *ᵣ-comm         = *ᵣ-comm       
--   ; *-cancels-/     = *-cancels-/   
--   ; show            = primShowFloat
--   ; +ᵣ-comm         = +ᵣ-comm
--   ; +ᵣ-assoc        = +ᵣ-assoc
--   }

