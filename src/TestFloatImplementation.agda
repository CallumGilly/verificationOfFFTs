{-# OPTIONS --guardedness #-}
module src.TestFloatImplementation where

open import src.Real using (Real)

import Agda.Builtin.Float as Float 
open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatACos; primFloatSin; primShowFloat)
open Float using (primRatioToFloat)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import IO using (IO; run; Main; _>>_; _>>=_)
open import IO.Finite using (putStrLn)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String

open import Data.Nat using (ℕ) renaming (_*_ to _*ₙ_)
open import Data.Nat.Show renaming (show to showNat)

open import Level

open import Function.Base using (_$_; _∘_)

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
  +ᵣ-comm         : ∀ (x y : Float) → (primFloatPlus x y) ≡ (primFloatPlus y x)
  +ᵣ-assoc        : ∀ (x y z : Float) → primFloatPlus (primFloatPlus x y) z ≡ primFloatPlus x (primFloatPlus y z)

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
  ; +ᵣ-comm         = +ᵣ-comm
  ; +ᵣ-assoc        = +ᵣ-assoc
  }

open Real builtinReals using (ℝ; _ᵣ; π; cos; sin) renaming (show to showReal; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)

-- Complex numbers stuff

open import src.Complex builtinReals using (ℂfromℕ; ℂ; fromℝ;_+_i; _+_; _*_)
open import src.ComplexShow builtinReals renaming (show to showComplex)

complex-02 : ℂ
complex-02 = ℂfromℕ 2
complex-03 : ℂ
complex-03 = ℂfromℕ 3

-- Matrix Stuff
open import src.Matrix using (Ar; Shape; ι; _⊗_; ι-cons; nil; unnest; Position; length; nest)
open import src.MatrixShow using (showShape) renaming (show to showMatrix)

small-matrix : Ar (ι 2) ℂ
small-matrix = ι-cons complex-02 (ι-cons complex-03 nil)

tiny-matrix : Ar (ι 1) ℂ
tiny-matrix = ι-cons complex-02 nil

----------
-- 1  2 -- 
----------
-- 3  4 --
----------
open import Data.Fin using (Fin; quotRem; toℕ) renaming (zero to fzero; suc to fsuc)

-- DFT

-----------------------------------------------
-- DFT example                               --
-- For an input   [1   ,  3   , 3   ,  1   ] --
-- We should get  [8+0i, -2-2i, 0+0i, -2+2i] --
-----------------------------------------------

open import src.DFTMatrix builtinReals using (DFT; posVec)
dft-example-input : Ar (ι 4) ℂ
dft-example-input (ι fzero)                      = ℂfromℕ 1
dft-example-input (ι (fsuc fzero))               = ℂfromℕ 3
dft-example-input (ι (fsuc (fsuc fzero)))        = ℂfromℕ 3
dft-example-input (ι (fsuc (fsuc (fsuc fzero)))) = ℂfromℕ 1

-- FFT example
-- Same as DFT example above
-- For an input   [[1   ,  3], [3 ,  1]] --
-- We should get  [8+0i, -2-2i, 0+0i, -2+2i] --
-----------------------------------------------
-- Second FFT example
-- For an input   [[1   ,  2], [3 ,  4]] --
-- We should get  [10+0i, -2+2i, -2+0i, -2-2i] --
-----------------------------------------------

open import src.FFT builtinReals using (FFT; twiddles; FFT₁; position-sum; twiddles₂; FFT₂)
open import src.Reshape using (Reshape; eq; _∙_; _⊕_; split; flat; swap; _♭; _♯; _⟨_⟩; _♯₂)
open import src.Reshape using (reshape; rev; rev-eq; rev-rev; transpose; transposeᵣ;recursive-transpose; recursive-transposeᵣ; eq)
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

giant-fft-half-split : Ar (ι 4 ⊗ ι 4) ℂ
giant-fft-half-split = unnest $ ι-cons (
      ι-cons (ℂfromℕ 1 ) $ 
      ι-cons (ℂfromℕ 5 ) $ 
      ι-cons (ℂfromℕ 9 ) $ 
      ι-cons (ℂfromℕ 13) $ nil
  ) $ ι-cons (
      ι-cons (ℂfromℕ 2 ) $ 
      ι-cons (ℂfromℕ 6 ) $
      ι-cons (ℂfromℕ 10) $ 
      ι-cons (ℂfromℕ 14) $ nil
  ) $ ι-cons (
      ι-cons (ℂfromℕ 3 ) $ 
      ι-cons (ℂfromℕ 7 ) $
      ι-cons (ℂfromℕ 11) $ 
      ι-cons (ℂfromℕ 15) $ nil
  ) $ ι-cons (
      ι-cons (ℂfromℕ 4 ) $ 
      ι-cons (ℂfromℕ 8 ) $
      ι-cons (ℂfromℕ 12) $
      ι-cons (ℂfromℕ 16) $ nil
  ) $ nil

giant-fft-split : Ar (ι 4 ⊗ (ι 2 ⊗ ι 2)) ℂ
giant-fft-split =
  unnest $ ι-cons (
    unnest $ ι-cons (
      ι-cons (ℂfromℕ 1 ) $ 
      ι-cons (ℂfromℕ 9 ) $ nil
    ) $ ι-cons (
      ι-cons (ℂfromℕ 5 ) $ 
      ι-cons (ℂfromℕ 13) $ nil
    ) nil
  ) $ ι-cons (
    unnest $ ι-cons (
      ι-cons (ℂfromℕ 2 ) $ 
      ι-cons (ℂfromℕ 10) $ nil
    ) $ ι-cons (
      ι-cons (ℂfromℕ 6 ) $ 
      ι-cons (ℂfromℕ 14) $ nil
    ) nil
  ) $ ι-cons (
    unnest $ ι-cons (
      ι-cons (ℂfromℕ 3 ) $ 
      ι-cons (ℂfromℕ 11) $ nil
    ) $ ι-cons (
      ι-cons (ℂfromℕ 7 ) $ 
      ι-cons (ℂfromℕ 15) $ nil
    ) nil
  ) $ ι-cons (
    unnest $ ι-cons (
      ι-cons (ℂfromℕ 4 ) $ 
      ι-cons (ℂfromℕ 12) $ nil
    ) $ ι-cons (
      ι-cons (ℂfromℕ 8 ) $ 
      ι-cons (ℂfromℕ 16) $ nil
    ) nil
  ) $ nil


--giant-fft-in-order : Ar (ι 4 ⊗ (ι 2 ⊗ ι 2)) ℂ
--giant-fft-in-order = reshape ((eq ⊕ split {2} {2}) ∙ split {4} {4}) giant-fft
--giant-fft-in-order = reshape ((eq ⊕ split {2} {2}) ∙ swap ∙ split {4} {4}) giant-fft
--giant-fft-in-order : Ar ((ι 2 ⊗ ι 2) ⊗ ι 4) ℂ
--giant-fft-in-order = reshape ((split {2} {2} ⊕ eq) ∙ split {4} {4}) giant-fft

{-
giant-fft-in-order : Ar (ι 4 ⊗ ι 4) ℂ
giant-fft-in-order = reshape (split {4} {4}) giant-fft
-}

giant-fft-in-order : Ar (ι 4 ⊗ (ι 2 ⊗ ι 2)) ℂ
giant-fft-in-order = reshape ((eq ⊕ split {2} {2}) ∙ split {4} {4}) giant-fft

{-
giant-fft-in-order : Ar ((ι 2 ⊗ ι 2) ⊗ ι 4) ℂ
giant-fft-in-order = reshape ((split {2} {2} ⊕ eq) ∙ split {4} {4}) giant-fft
-}
  
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

-- testDFT : IO {a} ⊤
-- testDFT = putStrLn (showMatrix showComplex (FFT fft-example-input))
-- testDFT = putStrLn (showMatrix showComplex (reshape (flat ∙ rev recursive-transposeᵣ) (FFT fft-example-input)))
--testDFT = putStrLn (showMatrix showComplex (reshape FFT-flattern (reshape (swap ∙ split {2} {2}) (fft-example-input-unstructured))))
-- testDFT = putStrLn (showMatrix showComplex (FFT ((reshape (swap ∙ split {4} {2}) (fft-example-input-unstructured)))))
--testDFT = putStrLn $ showMatrix showComplex $ FFT $ reshape (swap ∙ split {4} {4}) $ giant-fft
--testDFT = putStrLn $ showMatrix showComplex $ reshape (rev $ swap ∙ split {2} {4}) $ FFT $ reshape (swap ∙ split {4} {2}) $ fft-example-input-unstructured
--reshape (swap ∙ split {4} {4}) $ 
-- reshape (rev (swap ∙ split {2} {4})) $ 
--testDFT = putStrLn (showMatrix showComplex (DFT step1))

tmp : (s : Shape) → Reshape (ι $ length $ recursive-transpose s) (ι $ length s)
tmp (ι x) = eq
tmp (s ⊗ s₁) = flat ∙ swap ∙ tmp s₁ ⊕ tmp s ∙ split
 
showTwiddles : IO {a} ⊤ 
showTwiddles = putStrLn $ showMatrix showComplex $ twiddles {ι 2 ⊗ ι 2} {ι 2 ⊗ ι 2}

--theorm : ∀ {s : Shape} {arr : Ar s ℂ} {pos : Position s}→  (reshape (_♯ ∙ reshape-length {s}) ∘ DFT ∘ reshape (_♭ ∙ recursive-transposeᵣ )) arr pos ≡ FFT {s} arr pos
showProofLeft  : IO {a} ⊤
showProofLeft  = putStrLn $ showMatrix showComplex 
  $ (FFT giant-fft-in-order)
  --$ (DFT ∘ reshape (_♭)) giant-fft-in-order
showProofRight : IO {a} ⊤
showProofRight = putStrLn $ showMatrix showComplex $ ((reshape {ι 16} {recursive-transpose (ι 4 ⊗ (ι 2 ⊗ ι 2))} _♯₂) ∘ DFT ∘ (reshape {ι 4 ⊗ (ι 2 ⊗ ι 2) } _♭)) giant-fft-in-order
--showProofRight = putStrLn $ showMatrix showComplex $ ((reshape _♯)(reshape  _♯) ∘ DFT ∘ (reshape {ι 4 ⊗ (ι 2 ⊗ ι 2) } _♭)) giant-fft-in-order

  --$ reshape {ι (length (ι 16))} {recursive-transpose (ι 4 ⊗ (ι 2 ⊗ ι 2)) } _♯₂ ((DFT ∘ (reshape {ι 4 ⊗ (ι 2 ⊗ ι 2) } (_♭))) giant-fft-in-order) 
  --$ reshape (_♭) (FFT giant-fft-in-order)
--showGiantFFTed : IO {a} ⊤
--showGiantFFTed = putStrLn $ showMatrix showComplex $ FFT (giant-fft-split)

  --00→ (FFT arr) (pos ⟨ rev recursive-transposeᵣ ⟩) ≡ reshape _♯ ((DFT ∘ (reshape {s} (_♭))) arr) pos
showGiantShape : IO {a} ⊤
showGiantShape = putStrLn $ showMatrix showComplex $  reshape (_♭) giant-fft-in-order
showGiantShape₂ : IO {a} ⊤
showGiantShape₂ = putStrLn $ showMatrix showComplex $  (reshape recursive-transposeᵣ giant-fft-in-order)

bunchOStuff : IO {a} ⊤
bunchOStuff = do 
 -- showTwiddles
 showProofLeft
 showProofRight
 --showGiantFFTed
-- showGiantShape
-- showGiantShape₂


main : Main
main = run bunchOStuff 
  



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






