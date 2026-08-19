open import Data.String

open import Matrix.Mon

module Matrix.Mon.Show (M : Mon) where 
open Mon M

private variable
  u : U

record MonShow : Set where
  field
    showU  : U    → String
    showEl : El u → String
