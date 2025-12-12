{-# OPTIONS --guardedness #-}

module CGenerator where

  open import CLang using (gen-fft; gen-transpose-test; gen-fft-cube; ?SIMD; ι; _⊗_)
  open import Matrix using (Shape; ι; _⊗_) renaming (length to size)
  open import Matrix.NonZero using (ι; _⊗_; NonZeroₛ)
  open import IO using (IO; run; Main; _>>_; _>>=_)
  open import IO.Finite using (writeFile)
  open import Data.Unit.Polymorphic.Base using (⊤)
  open import Data.String hiding (show)
  open import Data.Product
  open import Data.Nat using (ℕ; NonZero)
  open import Function using (_$_)

  --------------------------
  ---- Set shape of FFT ----
  --------------------------

  sh : Shape
  sh = (ι 4 ⊗ ι 8) ⊗ ι 12   -- ((ι 4 ⊗ ι 2) ⊗ ι 3) ⊗ ι 3

  -- My love for instance arguments remains strong
  instance
    _ : NonZeroₛ sh
    _ = (ι _ ⊗ ι _) ⊗ ι _ 

  pred : ?SIMD sh
  pred = (ι 1 ⊗ ι 2) ⊗ ι 3

  -------------------------------------
  ---- Set shape of transpose test ----
  -------------------------------------

  sh₂ : Shape
  sh₂ = ((ι 2 ⊗ ι 2) ⊗ ι 2) ⊗ ι 2

  -------------------------------
  ---- Set shape of FFT Cube ----
  -------------------------------
  n₁ n₂ n₃ : ℕ 

  n₁ = 4
  n₂ = 5
  n₃ = 2

  -----------------------------------------------------------------------------
  nz-n₁ : NonZero n₁
  nz-n₂ : NonZero n₂
  nz-n₃ : NonZero n₃

  nz-n₁ = _
  nz-n₂ = _
  nz-n₃ = _

  main : Main
  main = run do
    let (fft-head , fft-body) = gen-fft sh pred
    writeFile "./generated/fft.h" fft-head
    writeFile "./generated/fft.c" fft-body

    let (fft-cube-head , fft-cube-body) = gen-fft-cube  ⦃ nz-n₁ ⦄ ⦃ nz-n₂ ⦄ ⦃ nz-n₃ ⦄ 
    writeFile "./generated/fftCube.h" fft-cube-head
    writeFile "./generated/fftCube.c" fft-cube-body

    --let (ufft-head , ufft-body) = gen-ufft sh
    --writeFile "./generated/ufft.h" ufft-head
    --writeFile "./generated/ufft.c" ufft-body

    let (trans-test-head , trans-test-body) = gen-transpose-test sh₂
    writeFile "./generated/transTest.h" trans-test-head
    writeFile "./generated/transTest.c" trans-test-body

