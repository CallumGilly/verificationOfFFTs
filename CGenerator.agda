{-# OPTIONS --guardedness #-}

module CGenerator where

  open import CLang using (gen-fft; gen-transpose-test)
  open import Matrix using (Shape; ι; _⊗_) renaming (length to size)
  open import Matrix.NonZero using (ι; _⊗_; NonZeroₛ)
  open import IO using (IO; run; Main; _>>_; _>>=_)
  open import IO.Finite using (writeFile)
  open import Data.Unit.Polymorphic.Base using (⊤)
  open import Data.String hiding (show)
  open import Data.Product
  open import Function using (_$_)

  sh : Shape
  sh = (ι 3 ⊗ ι 5) -- ((ι 4 ⊗ ι 2) ⊗ ι 3) ⊗ ι 3

  -- My love for instance arguments remains strong
  instance
    _ : NonZeroₛ sh
    _ = (ι _ ⊗ ι _) 

  sh₂ : Shape
  sh₂ = (ι 3 ⊗ ι 5)

  main : Main
  main = run do
    let (fft-head , fft-body) = gen-fft sh
    writeFile "./generated/fft.h" fft-head
    writeFile "./generated/fft.c" fft-body

    --let (ufft-head , ufft-body) = gen-ufft sh
    --writeFile "./generated/ufft.h" ufft-head
    --writeFile "./generated/ufft.c" ufft-body

    let (trans-test-head , trans-test-body) = gen-transpose-test sh₂
    writeFile "./generated/transTest.h" trans-test-head
    writeFile "./generated/transTest.c" trans-test-body

