{-# OPTIONS --guardedness #-}
module Implementations.ComplexTrans where
  module FromOld where
    open import ComplexNew using () renaming (Cplx to CplxNew)
    open import Implementations.Real
    --open Base
    --a : ℂ

    open import Complex using () renaming (Cplx to CplxOld)
    open import Implementations.Complex realImplementation as oldInp using ()
    open import Implementations.ComplexNew realImplementation renaming (complexImplementation to newComplexImplementation)

    module newInp = CplxNew newComplexImplementation

    toℂ : oldInp.ℂ → newInp.ℂ
    toℂ (oldInp.Base._+_i real-component imaginary-component) = real-component + imaginary-component i

    fromℂ : newInp.ℂ → oldInp.ℂ
    fromℂ (real-component + imaginary-component i) = oldInp.Base._+_i real-component imaginary-component
  open FromOld public

    







