{-# OPTIONS --allow-unsolved-metas #-}
open import Matrix.Mon
              
module Matrix.Parameterised (M : Mon) where
  open import Matrix.Parameterised.Base M public
  open import Matrix.Parameterised.Reshape M public
  open import Matrix.Parameterised.Properties M public
