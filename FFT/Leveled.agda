open import Matrix.Mon
open import ComplexNew

module FFT.Leveled (cplx : Cplx) (M : Mon) where
  open import FFT.Leveled.FFT cplx M public
  open import FFT.Leveled.UFFT cplx M public
  open import FFT.Leveled.Properties cplx M public
  open import FFT.Leveled.Specification cplx M public

