open import Complex using (Cplx)

module FFT.Simple (cplx : Cplx) where
  open import FFT.Simple.Base cplx public
  open import FFT.Simple.Properties cplx public

