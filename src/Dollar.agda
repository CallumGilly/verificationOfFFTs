module src.Dollar where

private
  variable
    X Y : Set

infixr 0 $

$ : (X → Y) → X → Y
$ f x = f x
