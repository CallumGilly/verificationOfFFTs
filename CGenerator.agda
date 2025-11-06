{-# OPTIONS --guardedness #-}

module CGenerator where

  open import CLang using (gen-fft; gen-dft)
  open import Matrix using (Shape; ι; _⊗_) renaming (length to size)
  open import Matrix.NonZero using (ι; _⊗_)
  open import IO using (IO; run; Main; _>>_; _>>=_)
  open import IO.Finite using (writeFile)
  open import Data.Unit.Polymorphic.Base using (⊤)
  open import Data.String hiding (show)
  open import Function using (_$_)

  sh : Shape
  sh = (ι 4 ⊗ ι 4) ⊗ (ι 3 ⊗ ι 4)

  main : Main
  main = run do
    writeFile "./generated/fft.c" (gen-fft sh ⦃ (ι _ ⊗ ι _) ⊗ (ι _ ⊗ ι _) ⦄)
    writeFile "./generated/dft.c" (gen-dft (size sh) ⦃ _ ⦄)

