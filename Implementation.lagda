%TC:ignore
\begin{code}[hide]
{-# OPTIONS --guardedness #-}
module Implementation where
\end{code}
%TC:endignore
\section{Compilation}

Given the definition of the FFT, and proof of its correctness, it is 
is now possible for us to generate runnable code with the same guarantees of 
correctness attached.
A runnable instance of this FFT implementation can be generated through use of
Agda's Builtin IO library, and the GHC Haskell backend.
The IO library allows for the definition of output and an entry point into the
program.
The GHC Haskell backend allows for translation into runnable Haskell, allowing
us to confirm that the FFT and DFT implementations run and produce expected
results.

\subsection{Complex Numbers}
To generate a runnable instance of the FFT as defined, an implementation of
the Complex numbers must be defined.
For the example shown here, I have defined complex numbers as pairs of
Agda's builtin \AF{Float}.

Unlike other number systems in Agda, builtin \AF{Float} is not defined 
inductively, and is instead a wrapper around IEEE 754 \cite{IEEE754}.
This means that no properties, such as commutativity or associativity, are 
provided and that any such property must be assumed through postulations.
This weakens implementations built on top of \AF{Float}, as they
become prone to minor floating point errors.
Such errors are generally unavoidable, however, within floating point 
mathematics, and the resultant effects are generally well 
studied.\cite{FFT4Profit}
This makes the use of builtin \AF{Float} acceptable for 
most implementations.

Given this implementation of floating point numbers as ℝ, the carrier, ℂ,
for complex numbers can be defined as a pair of floating point numbers, 
representing the real and imaginary components.
%TC:ignore
\begin{code}[hide]
open import Real using (Real)
open import Complex using (Cplx)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Algebra.Structures using (IsCommutativeRing)
open import Function using (_∘_)
open import Data.Nat using (ℕ; NonZero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (m*n≢0)

open import Agda.Builtin.String

module implementationComplex (real : Real) where
  open import Agda.Builtin.Float using (primFloatPlus) renaming (Float to ℝ)
  -- open Real.Real real using (ℝ; _ᵣ; cos; sin; π) renaming (-_ to -ᵣ_; 
  --   _+_ to _+ᵣ_; _-_ to _-ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)

  module Base where
\end{code}
%TC:endignore

\begin{AgdaMultiCode}
\begin{code}
    record ℂ : Set where
      constructor _+_i
      field
        real-component      : ℝ
        imaginary-component : ℝ
\end{code}

A constructor for ℂ is defined at the same time, allowing for composition 
and decomposition into component parts.
Builtin \AF{Float} then provides wrappers around some primitive operations 
which can be used to define the required methods on this carrier set,
such as addition.

\begin{code}
    _+_ : ℂ → ℂ → ℂ
    _+_ (xRe + xIm i) (yRe + yIm i) 
      = (primFloatPlus xRe yRe) + (primFloatPlus xIm  yIm) i
\end{code}
\end{AgdaMultiCode}

Once all of these method are defined, their properties can be proven or
postulated.
In an ideal implementation, all postulations would be made on the methods of 
builtin \AF{Float}, and the properties of complex would be paired with proofs.
However, for this example I have chosen to postulate the properties
of complex directly as to improve the simplicity of this example.

%TC:ignore
\begin{code}[hide]

module Complex2 (real : Real) where
  open Real.Real real using (ℝ; _ᵣ; cos; sin; π) renaming (-_ to -ᵣ_; 
      _+_ to _+ᵣ_; _-_ to _-ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)

  module Base where
    record ℂ : Set where
      constructor _+_i
      field
        real-component      : ℝ
        imaginary-component : ℝ

    0ℂ  : ℂ
    0ℂ  = (    (0 ᵣ)  + (0 ᵣ) i)
    -1ℂ : ℂ
    -1ℂ = ((-ᵣ (1 ᵣ)) + (0 ᵣ) i)
    1ℂ  : ℂ
    1ℂ  = (    (1 ᵣ)  + (0 ᵣ) i)

    _+_ : ℂ → ℂ → ℂ
    _+_ (xRe + xIm i) (yRe + yIm i) = (xRe +ᵣ yRe) + (xIm +ᵣ yIm) i

    _-_ : ℂ → ℂ → ℂ
    _-_ (xRe + xIm i) (yRe + yIm i) = (xRe -ᵣ yRe) + (xIm -ᵣ yIm) i

    -_ : ℂ → ℂ
    -_ (re + im i) = ((-ᵣ re) + (-ᵣ im) i)

    _*_ : ℂ → ℂ → ℂ
    _*_ (xRe + xIm i) (yRe + yIm i)
      = ((xRe *ᵣ yRe) -ᵣ (xIm *ᵣ yIm)) + ((xRe *ᵣ yIm) +ᵣ (xIm *ᵣ yRe)) i

    fromℝ : ℝ → ℂ
    fromℝ x = x + (0 ᵣ) i
    
    ℂfromℕ : ℕ → ℂ
    ℂfromℕ = fromℝ ∘ _ᵣ

    e^i_ : ℝ → ℂ
    e^i_ x = (cos x) + (sin x) i
    
    ℂ-conjugate : ℂ → ℂ
    ℂ-conjugate (re + im i) = re + (-ᵣ im) i

    -ω : (N : ℕ) → .⦃ nonZero-n : NonZero N ⦄ → (k : ℕ) → ℂ
    -ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))


    postulate
      isCommutativeRing : IsCommutativeRing {A = ℂ} _≡_ _+_ _*_ -_ 0ℂ 1ℂ
      ω-N-0 : ∀ {N : ℕ} → ⦃ nonZero-n : NonZero N ⦄ → -ω N 0 ≡ 1ℂ
      ω-N-mN : ∀ {N m : ℕ} → ⦃ nonZero-n : NonZero N ⦄ → -ω N (N *ₙ m) ≡ 1ℂ
      ω-r₁x-r₁y : 
        ∀ (r₁ x y : ℕ) 
        → ⦃ nonZero-r₁ : NonZero r₁ ⦄
        → ⦃ nonZero-x : NonZero x ⦄ 
        → -ω (r₁ *ₙ x) ⦃ m*n≢0 r₁ x ⦄ (r₁ *ₙ y) ≡ -ω x y
      ω-N-k₀+k₁ : ∀ {N k₀ k₁ : ℕ} → ⦃ nonZero-n : NonZero N ⦄ 
        → -ω N (k₀ +ₙ k₁) ≡ (-ω N k₀) * (-ω N k₁)

\end{code}
%TC:endignore
\begin{AgdaAlign}
\begin{code}
    complexImplementation : Cplx real
    complexImplementation = record {
          ℂ = ℂ
        ; _+_ = _+_
        -- ...
\end{code}
\end{AgdaAlign}
%TC:ignore
\begin{code}[hide]
        ; _-_ = _-_
        ; -_  = -_
        ; _*_ = _*_

        ; fromℝ = fromℝ

        ; e^i_ = e^i_
        ; ℂ-conjugate = ℂ-conjugate

        ; -ω = -ω

        ; +-*-isCommutativeRing = isCommutativeRing
        ; ω-N-0                 = ω-N-0 
        ; ω-N-mN                = ω-N-mN 
        ; ω-r₁x-r₁y             = ω-r₁x-r₁y 
        ; ω-N-k₀+k₁             = ω-N-k₀+k₁
      }
  open Base public
  open Cplx complexImplementation
\end{code}
%TC:endignore

This implementation of complex numbers then allows for the FFT to be
instantiated. 

\subsection{Runnable FFT}

Given a concrete definition of the complex numbers, it is now possible to run 
my implementation of the FFT.
The methods are not intended to be efficiant or practical for most uses.
The input is hard coded before compilation, and the Haskell back-end is used to
execute, however, it does allow for the results to be shown and analysed.

The \verb|main| method is the entry point to the program and defines the input 
to run on which is parsed to \AF{show-full-stack}.
\AF{show-full-stack} is then able to print out 
the original tensor, the tensor in vector form, the flat
result of running the FFT, and the flat result of running the DFT.

%TC:ignore
\begin{code}[hide]

module Implementation where

open import Real using (Real)
open import Implementations.Real using (realImplementation; showℝ)
open import Complex using (Cplx)
open import Implementations.Complex realImplementation using 
  (complexImplementation; _+_i)

open Real.Real realImplementation using (ℝ; _ᵣ; -_)
open Cplx complexImplementation using (ℂ; fromℝ)

open import Matrix
open import Matrix.Reshape
open import Matrix.Show using (showShape) renaming (show to showTensor)

open import FFT realImplementation complexImplementation using (FFT; DFT)

open import IO using (IO; run; Main; _>>_; _>>=_)
open import IO.Finite using (putStrLn)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String

open import Data.Nat.Show renaming (show to showNat)

open import Level

open import Function.Base using (_$_; _∘_)

private
  variable
   a : Level

private
  infixl 4 _++_
  _++_ : String → String → String
  _++_ = primStringAppend

--------------------
--- Show Complex ---
--------------------

showℂ : ℂ → String
showℂ (real + imaginary i) = (showℝ real) ++ " + " ++ (showℝ imaginary) ++ " i"

showDemoℂ : IO {a} ⊤
showDemoℂ = putStrLn $ showℂ ((4 ᵣ) + (2 ᵣ) i)

demo-mat₁ : Ar (ι 8) ℂ
demo-mat₁ =
  ι-cons (fromℝ $ 1 ᵣ) $
  ι-cons (fromℝ $ 2 ᵣ) $
  ι-cons (fromℝ $ 3 ᵣ) $
  ι-cons (fromℝ $ 4 ᵣ) $
  ι-cons (fromℝ $ 5 ᵣ) $
  ι-cons (fromℝ $ 6 ᵣ) $
  ι-cons (fromℝ $ 7 ᵣ) $
  ι-cons (fromℝ $ 8 ᵣ) nil

demo-mat₂ : Ar (ι 16) ℂ
demo-mat₂ =
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
  ι-cons (fromℝ $   61  ᵣ) nil

demo-mat₃ : Ar (ι 3 ⊗ ι 4) ℂ
demo-mat₃ =
  unnest $
      ι-cons (
    ι-cons (fromℝ $ 1  ᵣ) $
    ι-cons (fromℝ $ 2  ᵣ) $
    ι-cons (fromℝ $ 3  ᵣ) $
    ι-cons (fromℝ $ 4  ᵣ) nil
  ) $ ι-cons (
    ι-cons (fromℝ $ 5  ᵣ) $
    ι-cons (fromℝ $ 6  ᵣ) $
    ι-cons (fromℝ $ 7  ᵣ) $
    ι-cons (fromℝ $ 8  ᵣ) nil
  ) $ ι-cons (
    ι-cons (fromℝ $ 9  ᵣ) $
    ι-cons (fromℝ $ 10 ᵣ) $
    ι-cons (fromℝ $ 11 ᵣ) $
    ι-cons (fromℝ $ 12 ᵣ) nil
  ) nil

show-arr             : Ar s ℂ → IO {a} ⊤
show-flat-arr        : Ar s ℂ → IO {a} ⊤
show-flat-FFT-result : Ar s ℂ → IO {a} ⊤
show-flat-DFT-result : Ar s ℂ → IO {a} ⊤
\end{code}
%TC:endignore

\begin{code}
show-arr              arr = putStrLn $ "Tensor:     " 
                          ++ (showTensor showℂ $ arr)
show-flat-arr         arr = putStrLn $ "Flat Tensor:" 
                          ++ (showTensor showℂ $ reshape flatten-reindex arr)
show-flat-FFT-result  arr = putStrLn $ "FFT Result: " 
                          ++ (showTensor showℂ $ reshape (rev ♯) (FFT arr))
show-flat-DFT-result  arr = putStrLn $ "DFT Result: " 
                          ++ (showTensor showℂ $ (DFT (reshape flatten-reindex arr)))

show-full-stack : Ar s ℂ → IO {a} ⊤
show-full-stack arr = do
  show-arr              arr
  show-flat-arr         arr
  show-flat-FFT-result  arr
  show-flat-DFT-result  arr
\end{code}

This allows for my implementation of the DFT and FFT to be ran for any input.
The result of this execution can then be compared against the result of Numpy's 
FFT method, allowing for an average floating point error to be established 
against a well known implementation.
We can expect this average error to be low, but not zero, with an expected worst 
case growth bounded by $\left(\log N\right)$\cite{FFT4Profit}.
This is because each operation on floating point numbers introduces minor
rounding errors, and these minor errors then grow with each operation.
As each of the three implementations use different operations in different
orders, can be expected that these rounding errors will grow to different sizes.

I conducted a comparison of results for multiple input tensors.
An example of one of these comparisons is shown below.
All of these comparisons showed similar results, with the results of my 
implementation of the FFT and DFT matching those of the Numpy FFT, 
with some expected rounding errors.
This shows my implementation to work as expected.

\subsubsection{Example test}
For this example, I used the following two dimensional tensor of shape 
\AF{(ι 4 ⊗ ι 4)}, constructed from randomly generated numbers between 
-100 and 100, as input.
\[
\begin{pmatrix}
   87  &  13 &  72 & -44 \\
   99  &   8 & -63 &  25 \\
   90  & -31 &  56 &  19 \\
  -100 &  37 &  4  &  61 \\
\end{pmatrix}
\]

This is flattened for input to the DFT into the vector.

\[
\begin{pmatrix}
   87  &  13 &  72 & -44 & 99  &  \dots   &  61 
\end{pmatrix}
\]

With this tensor used as input, I am able to compare the results of the DFT,
FFT and Python FFT. 
The full results can be found in the attached files, however, they show that the
Agda FFT and DFT produce the same results as the Python FFT, with some expectedly
minor rounding errors.

The average difference between each value of the Agda DFT, and each value of 
the Python FFT is \num{2.23e-13}, while the maximum difference is \num{9.38e-13}.
The same average difference between the Agda FFT, and Python FFT is lower, at 
\num{4.05e-14}, while the maximum difference is \num{1.42e-13}.
Being so low, it is easy to attribute these differences to the issues 
caused by floating point arithmetic as discussed above.

\subsection{Future implementations}

In the paper ``Measuring the Haskell Gap'', Petersen 
et al analyse the difference in performance between the ``best performing 
\verb|c| implementation and the best performing Haskell implementation''.\cite{PetersenHaskell}
In their initial benchmarks, Petersen et al describe implementations compiled
with GHC as between $1.72\times$ and $82.9\times$ slower than \verb|c| counterparts.\cite{PetersenHaskell}
As translation into a GHC Haskell program is a required step to run my above implementation,
this same negative performance is parsed on.

This is not, however, the only method with which an Agda definition can be
made runnable.
My formally proven FFT implementation can instead be ported into a high performace array language
such as SaC \cite{ScholzSac} or Futhark\cite{Futhark}.
Such a port would then allow for the introduction of parallelism, as well as
allowing for the generation of efficient \verb|c|
code, avoiding performance issues caused by use of the Haskell compiler.
Such a port would ideally allow for the correctness properties of my 
FFT definition to be parsed on to the definition built from it in the chosen array language.
% This preservation of properties, however, would only truly hold if a verified:
% Agda to SaC translator, SaC to \verb|c| compiler, and \verb|c| compiler where 
% also used.\cite{ChoosingIsLosing}\cite{BlockedSinkarovs}
In \cite{ChoosingIsLosing}, Šinkarovs and Cockx define such a method for Agda to Sac 
translation.
As the number of operations I have used is very limited, and the small number of operations I
have defined on tensors are very similar to those defined in SaC, this would be 
a easy next step.
This would then allow for future investigation into the generation of code with FFTW like
performance.

% , however, this is not able to ``guarantee that the extracted code 
% preservers the semantics of the original implementation''\cite{ChoosingIsLosing}
% meaning the above chain loses true verifiability at the first step.
% This conversion is not investigated further within this paper, however it would
% allow for the generation of efficient \verb|c| kernels, with verifiable cores.



