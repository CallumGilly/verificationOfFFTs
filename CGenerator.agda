{-# OPTIONS --guardedness #-}

module CGenerator where

  open import CLang using (gen-fft; gen-transpose-test)
  open import Matrix using (Shape; ι; _⊗_) renaming (length to size)
  open import Matrix.NonZero using (ι; _⊗_)
  open import IO using (IO; run; Main; _>>_; _>>=_)
  open import IO.Finite using (writeFile)
  open import Data.Unit.Polymorphic.Base using (⊤)
  open import Data.String hiding (show)
  open import Data.Product
  open import Function using (_$_)

  sh : Shape
  sh = (ι 4 ⊗ ι 2) ⊗ (ι 3 ⊗ ι 3) 

  sh₂ : Shape
  sh₂ = (ι 3 ⊗ ι 5)

  main : Main
  main = run do
    let (fft-head , fft-body) = (gen-fft sh ⦃ (ι _ ⊗ ι _) ⊗ (ι _ ⊗ ι _) ⦄)
    --let (dft-head , dft-body) = (gen-dft (size sh) ⦃ _ ⦄)
    writeFile "./generated/fft.h" fft-head
    --writeFile "./generated/dft.h" dft-head
    writeFile "./generated/fft.c" fft-body
    --writeFile "./generated/dft.c" dft-body


    let (trans-test-head , trans-test-body) = gen-transpose-test sh₂
    
    writeFile "./generated/transTest.h" trans-test-head
    writeFile "./generated/transTest.c" trans-test-body

