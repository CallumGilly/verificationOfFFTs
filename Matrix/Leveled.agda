open import Matrix.Mon

module Matrix.Leveled (M : Mon) where
  open import Matrix.Leveled.Base M public
  open import Matrix.Leveled.Reshape M public
  open import Matrix.Leveled.Change-Major M public
