{-# OPTIONS --guardedness #-}
module src.TestFloatImplementation where

open import src.Real using (Real)

import Agda.Builtin.Float as Float 
open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatSin; primShowFloat)
open Float using (primRatioToFloat)

open import Agda.Builtin.Int using (pos)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import IO using (IO; run; Main)
open import IO.Finite using (putStrLn)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String

open import Data.Nat using (ℕ)
--open import Data.Nat.Show using (show)

open import Level

postulate
  double-negative : ∀ (x : Float) → primFloatNegate (primFloatNegate x) ≡ x
  *ᵣ-zeroᵣ        : ∀ (x : Float) → primFloatTimes x (primNatToFloat 0)  ≡ primNatToFloat 0
  /ᵣ-zeroₜ        : ∀ (x : Float) → primFloatDiv (primNatToFloat 0) x  ≡ primNatToFloat 0
  +ᵣ-identityˡ    : ∀ (x : Float) → primFloatPlus (primNatToFloat 0) x ≡ x
  +ᵣ-identityʳ    : ∀ (x : Float) → primFloatPlus x (primNatToFloat 0) ≡ x
  -ᵣ-identityʳ    : ∀ (x : Float) → primFloatMinus x (primNatToFloat 0) ≡ x
  *ᵣ-identityʳ    : ∀ (x : Float) → primFloatTimes x (primNatToFloat 1) ≡ x
  neg-distrib-*   : ∀ (x y : Float) → primFloatTimes (primFloatNegate x) y ≡ primFloatNegate (primFloatTimes x y)
  *ᵣ-assoc        : ∀ (x y z : Float) → primFloatTimes (primFloatTimes x y) z ≡ primFloatTimes x (primFloatTimes y z) 
  *ᵣ-comm         : ∀ (x y   : Float) →  primFloatTimes x y      ≡ primFloatTimes y x
  *-cancels-/     : ∀ (x y : Float) → primFloatTimes x (primFloatDiv y x) ≡ y

builtinReals : Real
builtinReals = record
  { ℝ = Float
  ; _ᵣ              = primNatToFloat
  ; π               = primRatioToFloat (pos 22) (pos 7)
  ; _+_             = primFloatPlus
  ; _-_             = primFloatMinus
  ; _*_             = primFloatTimes
  ; _/_             = primFloatDiv
  ; -_              = primFloatNegate
  ; cos             = primFloatCos
  ; sin             = primFloatSin
  ; double-negative = double-negative
  ; *ᵣ-zeroᵣ        = *ᵣ-zeroᵣ
  ; /ᵣ-zeroₜ        = /ᵣ-zeroₜ
  ; +ᵣ-identityˡ    = +ᵣ-identityˡ  
  ; +ᵣ-identityʳ    = +ᵣ-identityʳ  
  ; -ᵣ-identityʳ    = -ᵣ-identityʳ  
  ; *ᵣ-identityʳ    = *ᵣ-identityʳ  
  ; neg-distrib-*   = neg-distrib-* 
  ; *ᵣ-assoc        = *ᵣ-assoc      
  ; *ᵣ-comm         = *ᵣ-comm       
  ; *-cancels-/     = *-cancels-/   
  ; show            = primShowFloat
  }

open Real builtinReals using (ℝ; _ᵣ; π) renaming (show to showReal)

-- Complex numbers stuff

open import src.Complex builtinReals using (ℂfromℕ; ℂ; fromℝ;_+_i; _+_)
open import src.ComplexShow builtinReals renaming (show to showComplex)

-- Printing stuff
private
  variable
   a : Level

objectToPrint : ℂ
objectToPrint = ((3 ᵣ) + (7 ᵣ) i) + ((8 ᵣ) + (11 ᵣ) i)

testDFT : IO {a} ⊤
testDFT = putStrLn (showComplex objectToPrint)

main : Main
main = run testDFT







-- open Real myReals using (-_; _ᵣ; ℝ)
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)
-- open Eq.≡-Reasoning
-- open import src.Vector using (Vec; cons; nil)
-- open import src.DFT myReals using (DFT)
-- open import src.Complex myReals using (ℂfromℕ; ℂ; fromℝ;_+_i)
-- 
-- val36 : ℂ
-- val36 = ℂfromℕ 36
-- val22 : ℂ
-- val22 = ℂfromℕ 22
-- val45 : ℂ
-- val45 = ℂfromℕ 45
-- val15 : ℂ
-- val15 = ℂfromℕ 15
-- 
-- val118 : ℝ 
-- val118 = 118 ᵣ
-- val0   : ℝ 
-- val0   = 0 ᵣ
-- val-9  : ℝ 
-- val-9  = (- (9 ᵣ))
-- val-7  : ℝ 
-- val-7  = (- (7 ᵣ))
-- val44  : ℝ
-- val44  = 44 ᵣ
-- val7   : ℝ  
-- val7   = 7 ᵣ
-- 
-- val1   : ℂ 
-- val1   = ℂfromℕ 1
-- val-1   : ℂ 
-- val-1   = fromℝ (- (1 ᵣ))
-- 
-- -- _ : DFT (cons val36 (cons val22 (cons val45 (cons val15 nil)))) == cons (val118 + val0 i) (cons (val-9 + val-7 i) (cons (val44 + val0 i) (cons (val-9 + val7 i) nil)))
-- -- _ = ?
-- -- 
-- -- _ : DFT (cons val1 (cons val1 (cons val1 (cons val1 nil)))) ≡ (cons val1 (cons val1 (cons val1 (cons val-1 nil))))
-- -- _ = ?






