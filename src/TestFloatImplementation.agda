{-# OPTIONS --guardedness #-}
module src.TestFloatImplementation where

open import src.Real using (Real)

import Agda.Builtin.Float as Float 
open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatACos; primFloatSin; primShowFloat)
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

open import Function.Base using (_$_)

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
  ; π               = primFloatACos (primFloatNegate (primNatToFloat 1))
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

open Real builtinReals using (ℝ; _ᵣ; π; cos; -_) renaming (show to showReal)

-- Complex numbers stuff

open import src.Complex builtinReals using (ℂfromℕ; ℂ; fromℝ;_+_i; _+_; _*_)
open import src.ComplexShow builtinReals renaming (show to showComplex)

complex-02 : ℂ
complex-02 = ℂfromℕ 2
complex-03 : ℂ
complex-03 = ℂfromℕ 3

-- Matrix Stuff
open import src.Matrix using (Ar; Shape; ι; _⊗_; ι-cons; nil; unnest)
open import src.MatrixShow renaming (show to showMatrix)

small-matrix : Ar (ι 2) ℂ
small-matrix = ι-cons complex-02 (ι-cons complex-03 nil)

tiny-matrix : Ar (ι 1) ℂ
tiny-matrix = ι-cons complex-02 nil

----------
-- 1  2 -- 
----------
-- 3  4 --
----------
open import Data.Fin using (zero; suc)

counting-matrix : Ar (ι 2 ⊗ ι 2) ℂ
counting-matrix (ι zero       ⊗ ι zero      ) = ℂfromℕ 1 
counting-matrix (ι zero       ⊗ ι (suc zero)) = ℂfromℕ 2
counting-matrix (ι (suc zero) ⊗ ι zero      ) = ℂfromℕ 3
counting-matrix (ι (suc zero) ⊗ ι (suc zero)) = ℂfromℕ 4

-- DFT

-----------------------------------------------
-- DFT example                               --
-- For an input   [1   ,  3   , 3   ,  1   ] --
-- We should get  [8+0i, -2-2i, 0+0i, -2+2i] --
-----------------------------------------------

open import src.DFTMatrix builtinReals using (DFT)
dft-example-input : Ar (ι 4) ℂ
dft-example-input (ι zero)                   = ℂfromℕ 1
dft-example-input (ι (suc zero))             = ℂfromℕ 3
dft-example-input (ι (suc (suc zero)))       = ℂfromℕ 3
dft-example-input (ι (suc (suc (suc zero)))) = ℂfromℕ 1

-- FFT example
-- Same as DFT example above
-- For an input   [[1   ,  3], [3 ,  1]] --
-- We should get  [8+0i, -2-2i, 0+0i, -2+2i] --
-----------------------------------------------
-- Second FFT example
-- For an input   [[1   ,  2], [3 ,  4]] --
-- We should get  [10+0i, -2+2i, -2+0i, -2-2i] --
-----------------------------------------------

open import src.FFT builtinReals using (FFT; twiddles)
open import src.Reshape using (Reshape; eq; _∙_; _⊕_; split; flat; swap)
open import src.Reshape using (reshape; rev; rev-eq; rev-rev; transpose; transposeᵣ; recursive-transposeᵣ)
open import src.FFTSpliter using (FFT-flattern)

fft-example-input : Ar (ι 2 ⊗ ι 2) ℂ
fft-example-input = reshape split (ι-cons (ℂfromℕ 1) (ι-cons (ℂfromℕ 3) (ι-cons (ℂfromℕ 2) (ι-cons (ℂfromℕ 4) nil))))

fft-example-input-unstructured : Ar (ι 8) ℂ
fft-example-input-unstructured =
  ι-cons (ℂfromℕ 1) $
  ι-cons (ℂfromℕ 2) $
  ι-cons (ℂfromℕ 3) $
  ι-cons (ℂfromℕ 4) $
  ι-cons (ℂfromℕ 5) $
  ι-cons (ℂfromℕ 6) $
  ι-cons (ℂfromℕ 7) $
  ι-cons (ℂfromℕ 8) nil

giant-fft : Ar (ι 16) ℂ
giant-fft = 
  ι-cons (ℂfromℕ 1 ) $
  ι-cons (ℂfromℕ 2 ) $
  ι-cons (ℂfromℕ 3 ) $
  ι-cons (ℂfromℕ 4 ) $
  ι-cons (ℂfromℕ 5 ) $
  ι-cons (ℂfromℕ 6 ) $
  ι-cons (ℂfromℕ 7 ) $
  ι-cons (ℂfromℕ 8 ) $
  ι-cons (ℂfromℕ 9 ) $
  ι-cons (ℂfromℕ 10) $
  ι-cons (ℂfromℕ 11) $
  ι-cons (ℂfromℕ 12) $
  ι-cons (ℂfromℕ 13) $
  ι-cons (ℂfromℕ 14) $
  ι-cons (ℂfromℕ 15) $
  ι-cons (ℂfromℕ 16) nil
  
step1 : Ar (ι 4) ℂ
step1 = (
  ι-cons (ℂfromℕ 1) (
  ι-cons (ℂfromℕ 3) (
  ι-cons (ℂfromℕ 5) (
  ι-cons (ℂfromℕ 7) nil
  ))))

-- Printing stuff
private
  variable
   a : Level

objectToPrint : ℂ
objectToPrint = ((3 ᵣ) + (7 ᵣ) i) + ((8 ᵣ) + (11 ᵣ) i)

testDFT : IO {a} ⊤
-- testDFT = putStrLn (showMatrix showComplex (FFT fft-example-input))
-- testDFT = putStrLn (showMatrix showComplex (reshape (flat ∙ rev recursive-transposeᵣ) (FFT fft-example-input)))
--testDFT = putStrLn (showMatrix showComplex (reshape FFT-flattern (reshape (swap ∙ split {2} {2}) (fft-example-input-unstructured))))
-- testDFT = putStrLn (showMatrix showComplex (FFT ((reshape (swap ∙ split {4} {2}) (fft-example-input-unstructured)))))
--testDFT = putStrLn $ showMatrix showComplex $ FFT $ reshape (swap ∙ split {4} {4}) $ giant-fft
testDFT = putStrLn $ showMatrix showComplex $ reshape (rev $ swap ∙ split {2} {4}) $ FFT $ reshape (swap ∙ split {4} {2}) $ fft-example-input-unstructured
--reshape (swap ∙ split {4} {4}) $ 
-- reshape (rev (swap ∙ split {2} {4})) $ 
--testDFT = putStrLn (showMatrix showComplex (DFT step1))

showTwiddles : IO {a} ⊤
showTwiddles = putStrLn $ showMatrix showComplex $ twiddles {ι 4 ⊗ ι 4}

main : Main
main = run testDFT




-- open Real myReals using (-_; _ᵣ; ℝ)
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)
-- open Eq.≡-Reasoning
-- open import src.Vector using (Vec; cons; nil)
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






