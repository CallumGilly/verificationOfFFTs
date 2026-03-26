{-# OPTIONS --guardedness #-}

module Implementations.FFT where

open import Real using (Real)
open import Implementations.Real using (realImplementation; showℝ)
open import Complex using (Cplx)
open import Implementations.Complex realImplementation using (complexImplementation; _+_i; fromℝ)

open Real.Real realImplementation using (ℝ; _ᵣ; -_)
open Cplx complexImplementation using (ℂ)

open import Matrix.Simple.Base
open import Matrix.Simple.Reshape
open import Matrix.Simple.Show using (showShape; showCSV) renaming (show to showTensor)
open import Matrix.Simple.NonZero using (nonZeroDec)

open import FFT.Simple.Base complexImplementation using (FFT; DFT)
--open import FFT-Vec complexImplementation

open import IO using (IO; run; Main; _>>_; _>>=_)
open import IO.Finite using (putStrLn)
open import Relation.Nullary
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String

open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin renaming (suc to +; zero to z)

open import Level

open import Function.Base using (_$_; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)

--open import CLang
--open Interp realImplementation complexImplementation using (interp-inp)

private
  variable
   a : Level
   s : Shape

private
  infixl 4 _++_
  _++_ : String → String → String
  _++_ = primStringAppend

--------------------
--- Show Complex ---
--------------------

showℂ : ℂ → String
showℂ (real + imaginary i) = (showℝ real) ++ " + " ++ (showℝ imaginary) ++ " i"

showℂSV : ℂ → String
showℂSV (real + imaginary i) = (showℝ real) ++ ", " ++ (showℝ imaginary)

showDemoℂ : IO {a} ⊤
showDemoℂ = putStrLn $ showℂ ((4 ᵣ) + (2 ᵣ) i)

demo-mat₁ : Ar (ι 4 ⊗ (ι 4 ⊗ ι 3)) ℂ
demo-mat₁ = reshape ( eq ⊕ split ∙ split) demo-mat₁-vec
  where
    demo-mat₁-vec : Ar (ι 48) ℂ
    demo-mat₁-vec =
      ι-cons (fromℝ $   87  ᵣ) $
      ι-cons (fromℝ $   13  ᵣ) $
      ι-cons (fromℝ $   72  ᵣ) $
      ι-cons (fromℝ $ - 44  ᵣ) $
      ι-cons (fromℝ $   99  ᵣ) $
      ι-cons (fromℝ $   8   ᵣ)  $
      ι-cons (fromℝ $ - 63  ᵣ) $
      ι-cons (fromℝ $   25  ᵣ) $
      ι-cons (fromℝ $   90  ᵣ) $
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   56  ᵣ) $
      ι-cons (fromℝ $   19  ᵣ) $
      ι-cons (fromℝ $ - 100 ᵣ) $
      ι-cons (fromℝ $   37  ᵣ) $
      ι-cons (fromℝ $   4   ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) $
      ι-cons (fromℝ $   87  ᵣ) $
      ι-cons (fromℝ $   13  ᵣ) $
      ι-cons (fromℝ $   72  ᵣ) $
      ι-cons (fromℝ $ - 44  ᵣ) $
      ι-cons (fromℝ $   99  ᵣ) $
      ι-cons (fromℝ $   8   ᵣ)  $
      ι-cons (fromℝ $ - 63  ᵣ) $
      ι-cons (fromℝ $   25  ᵣ) $
      ι-cons (fromℝ $   90  ᵣ) $
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   56  ᵣ) $
      ι-cons (fromℝ $   19  ᵣ) $
      ι-cons (fromℝ $ - 100 ᵣ) $
      ι-cons (fromℝ $   37  ᵣ) $
      ι-cons (fromℝ $   4   ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) nil
      

demo-mat₂ : Ar (ι 12 ⊗ (ι 4 ⊗ ι 3)) ℂ
demo-mat₂ = reshape ((eq ⊕ split) ∙ split ) demo-mat₂-vec
  where
    demo-mat₂-vec : Ar (ι 144) ℂ
    demo-mat₂-vec =
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) nil

demo-mat₃ : Ar (ι 2 ⊗ (ι 2)) ℂ
demo-mat₃ = reshape ( eq ∙ split) demo-mat₁-vec
  where
    demo-mat₁-vec : Ar (ι 4) ℂ
    demo-mat₁-vec =
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) $ 
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) nil

demo-mat₄ : Ar ((ι 2 ⊗ ι 2) ⊗ ι 2) ℂ
demo-mat₄ = reshape ( split ⊕ eq ∙ split) demo-mat₁-vec
  where
    demo-mat₁-vec : Ar (ι 8) ℂ
    demo-mat₁-vec =
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   23  ᵣ) $ 
      ι-cons (fromℝ $ - 54  ᵣ) $
      ι-cons (fromℝ $ - 43  ᵣ) $
      ι-cons (fromℝ $ - 12  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) $ 
      ι-cons (fromℝ $ - 56  ᵣ) $
      ι-cons (fromℝ $   91  ᵣ) nil

3-dim-prime : Ar (((ι 2 ⊗ ι 4) ⊗ ι 6) ⊗ ι 8) ℂ
3-dim-prime = reshape ((split ⊕ eq ∙ split) ⊕ eq ∙ split) 3-dim-prime-flat
  where
    3-dim-prime-flat : Ar (ι 384) ℂ
    3-dim-prime-flat =
                ι-cons (fromℝ $   0   ᵣ) $
                ι-cons (fromℝ $   1   ᵣ) $
                ι-cons (fromℝ $   2   ᵣ) $
                ι-cons (fromℝ $   3   ᵣ) $
                ι-cons (fromℝ $   4   ᵣ) $
                ι-cons (fromℝ $   5   ᵣ) $
                ι-cons (fromℝ $   6   ᵣ) $
                ι-cons (fromℝ $   7   ᵣ) $
                ι-cons (fromℝ $   8   ᵣ) $
                ι-cons (fromℝ $   9   ᵣ) $
                ι-cons (fromℝ $   10   ᵣ) $
                ι-cons (fromℝ $   11   ᵣ) $
                ι-cons (fromℝ $   12   ᵣ) $
                ι-cons (fromℝ $   13   ᵣ) $
                ι-cons (fromℝ $   14   ᵣ) $
                ι-cons (fromℝ $   15   ᵣ) $
                ι-cons (fromℝ $   16   ᵣ) $
                ι-cons (fromℝ $   17   ᵣ) $
                ι-cons (fromℝ $   18   ᵣ) $
                ι-cons (fromℝ $   19   ᵣ) $
                ι-cons (fromℝ $   20   ᵣ) $
                ι-cons (fromℝ $   21   ᵣ) $
                ι-cons (fromℝ $   22   ᵣ) $
                ι-cons (fromℝ $   23   ᵣ) $
                ι-cons (fromℝ $   24   ᵣ) $
                ι-cons (fromℝ $   25   ᵣ) $
                ι-cons (fromℝ $   26   ᵣ) $
                ι-cons (fromℝ $   27   ᵣ) $
                ι-cons (fromℝ $   28   ᵣ) $
                ι-cons (fromℝ $   29   ᵣ) $
                ι-cons (fromℝ $   30   ᵣ) $
                ι-cons (fromℝ $   31   ᵣ) $
                ι-cons (fromℝ $   32   ᵣ) $
                ι-cons (fromℝ $   33   ᵣ) $
                ι-cons (fromℝ $   34   ᵣ) $
                ι-cons (fromℝ $   35   ᵣ) $
                ι-cons (fromℝ $   36   ᵣ) $
                ι-cons (fromℝ $   37   ᵣ) $
                ι-cons (fromℝ $   38   ᵣ) $
                ι-cons (fromℝ $   39   ᵣ) $
                ι-cons (fromℝ $   40   ᵣ) $
                ι-cons (fromℝ $   41   ᵣ) $
                ι-cons (fromℝ $   42   ᵣ) $
                ι-cons (fromℝ $   43   ᵣ) $
                ι-cons (fromℝ $   44   ᵣ) $
                ι-cons (fromℝ $   45   ᵣ) $
                ι-cons (fromℝ $   46   ᵣ) $
                ι-cons (fromℝ $   47   ᵣ) $
                ι-cons (fromℝ $   48   ᵣ) $
                ι-cons (fromℝ $   49   ᵣ) $
                ι-cons (fromℝ $   50   ᵣ) $
                ι-cons (fromℝ $   51   ᵣ) $
                ι-cons (fromℝ $   52   ᵣ) $
                ι-cons (fromℝ $   53   ᵣ) $
                ι-cons (fromℝ $   54   ᵣ) $
                ι-cons (fromℝ $   55   ᵣ) $
                ι-cons (fromℝ $   56   ᵣ) $
                ι-cons (fromℝ $   57   ᵣ) $
                ι-cons (fromℝ $   58   ᵣ) $
                ι-cons (fromℝ $   59   ᵣ) $
                ι-cons (fromℝ $   60   ᵣ) $
                ι-cons (fromℝ $   61   ᵣ) $
                ι-cons (fromℝ $   62   ᵣ) $
                ι-cons (fromℝ $   63   ᵣ) $
                ι-cons (fromℝ $   64   ᵣ) $
                ι-cons (fromℝ $   65   ᵣ) $
                ι-cons (fromℝ $   66   ᵣ) $
                ι-cons (fromℝ $   67   ᵣ) $
                ι-cons (fromℝ $   68   ᵣ) $
                ι-cons (fromℝ $   69   ᵣ) $
                ι-cons (fromℝ $   70   ᵣ) $
                ι-cons (fromℝ $   71   ᵣ) $
                ι-cons (fromℝ $   72   ᵣ) $
                ι-cons (fromℝ $   73   ᵣ) $
                ι-cons (fromℝ $   74   ᵣ) $
                ι-cons (fromℝ $   75   ᵣ) $
                ι-cons (fromℝ $   76   ᵣ) $
                ι-cons (fromℝ $   77   ᵣ) $
                ι-cons (fromℝ $   78   ᵣ) $
                ι-cons (fromℝ $   79   ᵣ) $
                ι-cons (fromℝ $   80   ᵣ) $
                ι-cons (fromℝ $   81   ᵣ) $
                ι-cons (fromℝ $   82   ᵣ) $
                ι-cons (fromℝ $   83   ᵣ) $
                ι-cons (fromℝ $   84   ᵣ) $
                ι-cons (fromℝ $   85   ᵣ) $
                ι-cons (fromℝ $   86   ᵣ) $
                ι-cons (fromℝ $   87   ᵣ) $
                ι-cons (fromℝ $   88   ᵣ) $
                ι-cons (fromℝ $   89   ᵣ) $
                ι-cons (fromℝ $   90   ᵣ) $
                ι-cons (fromℝ $   91   ᵣ) $
                ι-cons (fromℝ $   92   ᵣ) $
                ι-cons (fromℝ $   93   ᵣ) $
                ι-cons (fromℝ $   94   ᵣ) $
                ι-cons (fromℝ $   95   ᵣ) $
                ι-cons (fromℝ $   96   ᵣ) $
                ι-cons (fromℝ $   97   ᵣ) $
                ι-cons (fromℝ $   98   ᵣ) $
                ι-cons (fromℝ $   99   ᵣ) $
                ι-cons (fromℝ $   100   ᵣ) $
                ι-cons (fromℝ $   101   ᵣ) $
                ι-cons (fromℝ $   102   ᵣ) $
                ι-cons (fromℝ $   103   ᵣ) $
                ι-cons (fromℝ $   104   ᵣ) $
                ι-cons (fromℝ $   105   ᵣ) $
                ι-cons (fromℝ $   106   ᵣ) $
                ι-cons (fromℝ $   107   ᵣ) $
                ι-cons (fromℝ $   108   ᵣ) $
                ι-cons (fromℝ $   109   ᵣ) $
                ι-cons (fromℝ $   110   ᵣ) $
                ι-cons (fromℝ $   111   ᵣ) $
                ι-cons (fromℝ $   112   ᵣ) $
                ι-cons (fromℝ $   113   ᵣ) $
                ι-cons (fromℝ $   114   ᵣ) $
                ι-cons (fromℝ $   115   ᵣ) $
                ι-cons (fromℝ $   116   ᵣ) $
                ι-cons (fromℝ $   117   ᵣ) $
                ι-cons (fromℝ $   118   ᵣ) $
                ι-cons (fromℝ $   119   ᵣ) $
                ι-cons (fromℝ $   120   ᵣ) $
                ι-cons (fromℝ $   121   ᵣ) $
                ι-cons (fromℝ $   122   ᵣ) $
                ι-cons (fromℝ $   123   ᵣ) $
                ι-cons (fromℝ $   124   ᵣ) $
                ι-cons (fromℝ $   125   ᵣ) $
                ι-cons (fromℝ $   126   ᵣ) $
                ι-cons (fromℝ $   127   ᵣ) $
                ι-cons (fromℝ $   128   ᵣ) $
                ι-cons (fromℝ $   129   ᵣ) $
                ι-cons (fromℝ $   130   ᵣ) $
                ι-cons (fromℝ $   131   ᵣ) $
                ι-cons (fromℝ $   132   ᵣ) $
                ι-cons (fromℝ $   133   ᵣ) $
                ι-cons (fromℝ $   134   ᵣ) $
                ι-cons (fromℝ $   135   ᵣ) $
                ι-cons (fromℝ $   136   ᵣ) $
                ι-cons (fromℝ $   137   ᵣ) $
                ι-cons (fromℝ $   138   ᵣ) $
                ι-cons (fromℝ $   139   ᵣ) $
                ι-cons (fromℝ $   140   ᵣ) $
                ι-cons (fromℝ $   141   ᵣ) $
                ι-cons (fromℝ $   142   ᵣ) $
                ι-cons (fromℝ $   143   ᵣ) $
                ι-cons (fromℝ $   144   ᵣ) $
                ι-cons (fromℝ $   145   ᵣ) $
                ι-cons (fromℝ $   146   ᵣ) $
                ι-cons (fromℝ $   147   ᵣ) $
                ι-cons (fromℝ $   148   ᵣ) $
                ι-cons (fromℝ $   149   ᵣ) $
                ι-cons (fromℝ $   150   ᵣ) $
                ι-cons (fromℝ $   151   ᵣ) $
                ι-cons (fromℝ $   152   ᵣ) $
                ι-cons (fromℝ $   153   ᵣ) $
                ι-cons (fromℝ $   154   ᵣ) $
                ι-cons (fromℝ $   155   ᵣ) $
                ι-cons (fromℝ $   156   ᵣ) $
                ι-cons (fromℝ $   157   ᵣ) $
                ι-cons (fromℝ $   158   ᵣ) $
                ι-cons (fromℝ $   159   ᵣ) $
                ι-cons (fromℝ $   160   ᵣ) $
                ι-cons (fromℝ $   161   ᵣ) $
                ι-cons (fromℝ $   162   ᵣ) $
                ι-cons (fromℝ $   163   ᵣ) $
                ι-cons (fromℝ $   164   ᵣ) $
                ι-cons (fromℝ $   165   ᵣ) $
                ι-cons (fromℝ $   166   ᵣ) $
                ι-cons (fromℝ $   167   ᵣ) $
                ι-cons (fromℝ $   168   ᵣ) $
                ι-cons (fromℝ $   169   ᵣ) $
                ι-cons (fromℝ $   170   ᵣ) $
                ι-cons (fromℝ $   171   ᵣ) $
                ι-cons (fromℝ $   172   ᵣ) $
                ι-cons (fromℝ $   173   ᵣ) $
                ι-cons (fromℝ $   174   ᵣ) $
                ι-cons (fromℝ $   175   ᵣ) $
                ι-cons (fromℝ $   176   ᵣ) $
                ι-cons (fromℝ $   177   ᵣ) $
                ι-cons (fromℝ $   178   ᵣ) $
                ι-cons (fromℝ $   179   ᵣ) $
                ι-cons (fromℝ $   180   ᵣ) $
                ι-cons (fromℝ $   181   ᵣ) $
                ι-cons (fromℝ $   182   ᵣ) $
                ι-cons (fromℝ $   183   ᵣ) $
                ι-cons (fromℝ $   184   ᵣ) $
                ι-cons (fromℝ $   185   ᵣ) $
                ι-cons (fromℝ $   186   ᵣ) $
                ι-cons (fromℝ $   187   ᵣ) $
                ι-cons (fromℝ $   188   ᵣ) $
                ι-cons (fromℝ $   189   ᵣ) $
                ι-cons (fromℝ $   190   ᵣ) $
                ι-cons (fromℝ $   191   ᵣ) $
                ι-cons (fromℝ $   192   ᵣ) $
                ι-cons (fromℝ $   193   ᵣ) $
                ι-cons (fromℝ $   194   ᵣ) $
                ι-cons (fromℝ $   195   ᵣ) $
                ι-cons (fromℝ $   196   ᵣ) $
                ι-cons (fromℝ $   197   ᵣ) $
                ι-cons (fromℝ $   198   ᵣ) $
                ι-cons (fromℝ $   199   ᵣ) $
                ι-cons (fromℝ $   200   ᵣ) $
                ι-cons (fromℝ $   201   ᵣ) $
                ι-cons (fromℝ $   202   ᵣ) $
                ι-cons (fromℝ $   203   ᵣ) $
                ι-cons (fromℝ $   204   ᵣ) $
                ι-cons (fromℝ $   205   ᵣ) $
                ι-cons (fromℝ $   206   ᵣ) $
                ι-cons (fromℝ $   207   ᵣ) $
                ι-cons (fromℝ $   208   ᵣ) $
                ι-cons (fromℝ $   209   ᵣ) $
                ι-cons (fromℝ $   210   ᵣ) $
                ι-cons (fromℝ $   211   ᵣ) $
                ι-cons (fromℝ $   212   ᵣ) $
                ι-cons (fromℝ $   213   ᵣ) $
                ι-cons (fromℝ $   214   ᵣ) $
                ι-cons (fromℝ $   215   ᵣ) $
                ι-cons (fromℝ $   216   ᵣ) $
                ι-cons (fromℝ $   217   ᵣ) $
                ι-cons (fromℝ $   218   ᵣ) $
                ι-cons (fromℝ $   219   ᵣ) $
                ι-cons (fromℝ $   220   ᵣ) $
                ι-cons (fromℝ $   221   ᵣ) $
                ι-cons (fromℝ $   222   ᵣ) $
                ι-cons (fromℝ $   223   ᵣ) $
                ι-cons (fromℝ $   224   ᵣ) $
                ι-cons (fromℝ $   225   ᵣ) $
                ι-cons (fromℝ $   226   ᵣ) $
                ι-cons (fromℝ $   227   ᵣ) $
                ι-cons (fromℝ $   228   ᵣ) $
                ι-cons (fromℝ $   229   ᵣ) $
                ι-cons (fromℝ $   230   ᵣ) $
                ι-cons (fromℝ $   231   ᵣ) $
                ι-cons (fromℝ $   232   ᵣ) $
                ι-cons (fromℝ $   233   ᵣ) $
                ι-cons (fromℝ $   234   ᵣ) $
                ι-cons (fromℝ $   235   ᵣ) $
                ι-cons (fromℝ $   236   ᵣ) $
                ι-cons (fromℝ $   237   ᵣ) $
                ι-cons (fromℝ $   238   ᵣ) $
                ι-cons (fromℝ $   239   ᵣ) $
                ι-cons (fromℝ $   240   ᵣ) $
                ι-cons (fromℝ $   241   ᵣ) $
                ι-cons (fromℝ $   242   ᵣ) $
                ι-cons (fromℝ $   243   ᵣ) $
                ι-cons (fromℝ $   244   ᵣ) $
                ι-cons (fromℝ $   245   ᵣ) $
                ι-cons (fromℝ $   246   ᵣ) $
                ι-cons (fromℝ $   247   ᵣ) $
                ι-cons (fromℝ $   248   ᵣ) $
                ι-cons (fromℝ $   249   ᵣ) $
                ι-cons (fromℝ $   250   ᵣ) $
                ι-cons (fromℝ $   251   ᵣ) $
                ι-cons (fromℝ $   252   ᵣ) $
                ι-cons (fromℝ $   253   ᵣ) $
                ι-cons (fromℝ $   254   ᵣ) $
                ι-cons (fromℝ $   255   ᵣ) $
                ι-cons (fromℝ $   256   ᵣ) $
                ι-cons (fromℝ $   257   ᵣ) $
                ι-cons (fromℝ $   258   ᵣ) $
                ι-cons (fromℝ $   259   ᵣ) $
                ι-cons (fromℝ $   260   ᵣ) $
                ι-cons (fromℝ $   261   ᵣ) $
                ι-cons (fromℝ $   262   ᵣ) $
                ι-cons (fromℝ $   263   ᵣ) $
                ι-cons (fromℝ $   264   ᵣ) $
                ι-cons (fromℝ $   265   ᵣ) $
                ι-cons (fromℝ $   266   ᵣ) $
                ι-cons (fromℝ $   267   ᵣ) $
                ι-cons (fromℝ $   268   ᵣ) $
                ι-cons (fromℝ $   269   ᵣ) $
                ι-cons (fromℝ $   270   ᵣ) $
                ι-cons (fromℝ $   271   ᵣ) $
                ι-cons (fromℝ $   272   ᵣ) $
                ι-cons (fromℝ $   273   ᵣ) $
                ι-cons (fromℝ $   274   ᵣ) $
                ι-cons (fromℝ $   275   ᵣ) $
                ι-cons (fromℝ $   276   ᵣ) $
                ι-cons (fromℝ $   277   ᵣ) $
                ι-cons (fromℝ $   278   ᵣ) $
                ι-cons (fromℝ $   279   ᵣ) $
                ι-cons (fromℝ $   280   ᵣ) $
                ι-cons (fromℝ $   281   ᵣ) $
                ι-cons (fromℝ $   282   ᵣ) $
                ι-cons (fromℝ $   283   ᵣ) $
                ι-cons (fromℝ $   284   ᵣ) $
                ι-cons (fromℝ $   285   ᵣ) $
                ι-cons (fromℝ $   286   ᵣ) $
                ι-cons (fromℝ $   287   ᵣ) $
                ι-cons (fromℝ $   288   ᵣ) $
                ι-cons (fromℝ $   289   ᵣ) $
                ι-cons (fromℝ $   290   ᵣ) $
                ι-cons (fromℝ $   291   ᵣ) $
                ι-cons (fromℝ $   292   ᵣ) $
                ι-cons (fromℝ $   293   ᵣ) $
                ι-cons (fromℝ $   294   ᵣ) $
                ι-cons (fromℝ $   295   ᵣ) $
                ι-cons (fromℝ $   296   ᵣ) $
                ι-cons (fromℝ $   297   ᵣ) $
                ι-cons (fromℝ $   298   ᵣ) $
                ι-cons (fromℝ $   299   ᵣ) $
                ι-cons (fromℝ $   300   ᵣ) $
                ι-cons (fromℝ $   301   ᵣ) $
                ι-cons (fromℝ $   302   ᵣ) $
                ι-cons (fromℝ $   303   ᵣ) $
                ι-cons (fromℝ $   304   ᵣ) $
                ι-cons (fromℝ $   305   ᵣ) $
                ι-cons (fromℝ $   306   ᵣ) $
                ι-cons (fromℝ $   307   ᵣ) $
                ι-cons (fromℝ $   308   ᵣ) $
                ι-cons (fromℝ $   309   ᵣ) $
                ι-cons (fromℝ $   310   ᵣ) $
                ι-cons (fromℝ $   311   ᵣ) $
                ι-cons (fromℝ $   312   ᵣ) $
                ι-cons (fromℝ $   313   ᵣ) $
                ι-cons (fromℝ $   314   ᵣ) $
                ι-cons (fromℝ $   315   ᵣ) $
                ι-cons (fromℝ $   316   ᵣ) $
                ι-cons (fromℝ $   317   ᵣ) $
                ι-cons (fromℝ $   318   ᵣ) $
                ι-cons (fromℝ $   319   ᵣ) $
                ι-cons (fromℝ $   320   ᵣ) $
                ι-cons (fromℝ $   321   ᵣ) $
                ι-cons (fromℝ $   322   ᵣ) $
                ι-cons (fromℝ $   323   ᵣ) $
                ι-cons (fromℝ $   324   ᵣ) $
                ι-cons (fromℝ $   325   ᵣ) $
                ι-cons (fromℝ $   326   ᵣ) $
                ι-cons (fromℝ $   327   ᵣ) $
                ι-cons (fromℝ $   328   ᵣ) $
                ι-cons (fromℝ $   329   ᵣ) $
                ι-cons (fromℝ $   330   ᵣ) $
                ι-cons (fromℝ $   331   ᵣ) $
                ι-cons (fromℝ $   332   ᵣ) $
                ι-cons (fromℝ $   333   ᵣ) $
                ι-cons (fromℝ $   334   ᵣ) $
                ι-cons (fromℝ $   335   ᵣ) $
                ι-cons (fromℝ $   336   ᵣ) $
                ι-cons (fromℝ $   337   ᵣ) $
                ι-cons (fromℝ $   338   ᵣ) $
                ι-cons (fromℝ $   339   ᵣ) $
                ι-cons (fromℝ $   340   ᵣ) $
                ι-cons (fromℝ $   341   ᵣ) $
                ι-cons (fromℝ $   342   ᵣ) $
                ι-cons (fromℝ $   343   ᵣ) $
                ι-cons (fromℝ $   344   ᵣ) $
                ι-cons (fromℝ $   345   ᵣ) $
                ι-cons (fromℝ $   346   ᵣ) $
                ι-cons (fromℝ $   347   ᵣ) $
                ι-cons (fromℝ $   348   ᵣ) $
                ι-cons (fromℝ $   349   ᵣ) $
                ι-cons (fromℝ $   350   ᵣ) $
                ι-cons (fromℝ $   351   ᵣ) $
                ι-cons (fromℝ $   352   ᵣ) $
                ι-cons (fromℝ $   353   ᵣ) $
                ι-cons (fromℝ $   354   ᵣ) $
                ι-cons (fromℝ $   355   ᵣ) $
                ι-cons (fromℝ $   356   ᵣ) $
                ι-cons (fromℝ $   357   ᵣ) $
                ι-cons (fromℝ $   358   ᵣ) $
                ι-cons (fromℝ $   359   ᵣ) $
                ι-cons (fromℝ $   360   ᵣ) $
                ι-cons (fromℝ $   361   ᵣ) $
                ι-cons (fromℝ $   362   ᵣ) $
                ι-cons (fromℝ $   363   ᵣ) $
                ι-cons (fromℝ $   364   ᵣ) $
                ι-cons (fromℝ $   365   ᵣ) $
                ι-cons (fromℝ $   366   ᵣ) $
                ι-cons (fromℝ $   367   ᵣ) $
                ι-cons (fromℝ $   368   ᵣ) $
                ι-cons (fromℝ $   369   ᵣ) $
                ι-cons (fromℝ $   370   ᵣ) $
                ι-cons (fromℝ $   371   ᵣ) $
                ι-cons (fromℝ $   372   ᵣ) $
                ι-cons (fromℝ $   373   ᵣ) $
                ι-cons (fromℝ $   374   ᵣ) $
                ι-cons (fromℝ $   375   ᵣ) $
                ι-cons (fromℝ $   376   ᵣ) $
                ι-cons (fromℝ $   377   ᵣ) $
                ι-cons (fromℝ $   378   ᵣ) $
                ι-cons (fromℝ $   379   ᵣ) $
                ι-cons (fromℝ $   380   ᵣ) $
                ι-cons (fromℝ $   381   ᵣ) $
                ι-cons (fromℝ $   382   ᵣ) $
                ι-cons (fromℝ $   384   ᵣ) nil



--open import Implementations.VeryLargeShapeAuto
--postulate
--  SIMD-demo-vec : Ar (ι 240) ℂ

--SIMD-Shape : Shape
--SIMD-Shape = (((ι V ⊗ ι 3) ⊗ (ι V ⊗ ι 5)))
--SIMD-Shape = (((ι V ) ⊗ ((ι 3 ⊗ ι V) ⊗ ι 5)))
--SIMD-demo : Ar SIMD-Shape ℂ
--SIMD-demo = reshape (split ⊕ split ∙ split) SIMD-demo-vec
--SIMD-demo = reshape ( eq ⊕ ((split ⊕ eq) ∙ split) ∙ split) SIMD-demo-vec

show-arr                  : Ar s ℂ → IO {a} ⊤
show-flat-arr             : Ar s ℂ → IO {a} ⊤
--show-flat-Inp-FFT-result  : Ar s ℂ → IO {a} ⊤
show-flat-Orig-FFT-result : Ar s ℂ → IO {a} ⊤
show-flat-DFT-result      : Ar s ℂ → IO {a} ⊤


show-arr             xs =          putStrLn $ "Tensor:          " ++ (showTensor showℂ $ xs)
show-flat-arr        xs =          putStrLn $ "Flat Tensor:     " ++ (showTensor showℂ $ reshape flatten-reindex xs)
--show-flat-Inp-FFT-result {s} xs with nonZeroDec s
--... | no ¬a = putStrLn "ERROR"
--... | yes a = putStrLn $ "Inp FFT Result: " ++ (showTensor showℂ $ reshape (rev ♯) ((interp-inp (`ffti a)) xs))
--show-flat-Orig-FFT-result {s} xs = putStrLn $ "Orig FFT Result: " ++ (showTensor showℂ $ reshape (rev ♯) (FFT xs))
show-flat-Orig-FFT-result {s} xs = putStrLn $ "Orig FFT Result: " ++ "" --(showTensor showℂ $ reshape (rev ♯) (ufft′ xs))
show-flat-DFT-result xs          = putStrLn $ "DFT Result:      " ++ "" --(showTensor showℂ $ (DFT (reshape flatten-reindex xs)))

show-full-stack : Ar s ℂ → IO {a} ⊤
show-full-stack xs = do
  show-arr             xs
  show-flat-arr        xs
  --show-flat-Inp-FFT-result xs
  show-flat-Orig-FFT-result xs
  show-flat-DFT-result xs

CSVStack : Ar s ℂ → Ar (ι 3 ⊗ ι (length s)) ℂ
CSVStack xs     (ι z ⊗ x₁)         = (reshape ♭ xs) x₁
CSVStack {s} xs (ι (+ z) ⊗ x₁)     = (DFT (reshape ♭ xs)) x₁
CSVStack xs     (ι (+ (+ z)) ⊗ x₁) = (reshape ♭ xs) x₁
                                      --reshape (♭ ∙ (rev CMᵗ)) (FFT xs) x₁


--OFFTStack : Ar (ι 3 ⊗ ι (length SIMD-Shape)) ℂ
--OFFTStack (ι z ⊗ x₁)         = (reshape ♭ SIMD-demo) x₁
--OFFTStack (ι (+ z) ⊗ x₁)     = (DFT (reshape flatten-reindex SIMD-demo)) x₁
--OFFTStack (ι (+ (+ z)) ⊗ x₁) = (reshape (♭) (nofft (ι) SIMD-demo)) x₁

--CSVStack xs (ι (+ (+ z)) ⊗ x₁) = reshape ♭ (offt ? ?) x₁

CSVStackHead : Ar (ι 3) String
CSVStackHead (ι z) =         " Input-Real" ++ ", " ++ "Input-Imag"
CSVStackHead (ι (+ z)) =     "DFT-Real"   ++ ", " ++ "DFT-Imag"
CSVStackHead (ι (+ (+ z))) = "FFT-Real"   ++ ", " ++ "FFT-Imag"

main : Main
--main = run $ putStrLn $ showCSV showℂSV CSVStackHead (CSVStack demo-mat₄)
main = run $ show-arr (reshape (CMᵗ) 3-dim-prime)


--main = run $ show-full-stack demo-mat₄

--fft≅dft : 
--    ∀ (arr : Ar s ℂ) 
--  → FFT arr 
--    ≅ 
--    ( (reshape ♯) 
--    ∘ DFT
--    ∘ (reshape flatten-reindex)) arr











