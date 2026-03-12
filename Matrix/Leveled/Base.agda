open import Matrix.Mon
module Matrix.Leveled.Base (M : Mon) where

  open Mon M

  data L : Set where
    zz : L
    ss : L → L

  private
    variable
      l : L
      u : U
      X Y Z : Set


  data S : L → Set where
    ν   : U → S zz
    ι   : S l → (S (ss l))
    _⊗_ : S l → S l → S l

  data P : S l → Set where
    ν   : El u → P (ν u) 
    ι   : ∀ {s : S l} → P s → P (ι s)
    _⊗_ : ∀ {s p : S l} → P s → P p → P (s ⊗ p)

  Ar : S l → Set → Set
  Ar s X = P s → X

  map : {s : S l} → (X → Y) → Ar s X → Ar s Y
  map f xs i = f (xs i)

  imap : {s : S l} → (P s → X → Y) → Ar s X → Ar s Y
  imap f a i = f i (a i)

  zipWith : {s : S l} → (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
  zipWith f xs ys i = f (xs i) (ys i)

  nest : {s p : S l} → Ar (s ⊗ p) X → Ar s (Ar p X)
  nest xs i j = xs (i ⊗ j)

  unnest : {s p : S l} → Ar s (Ar p X) → Ar (s ⊗ p) X 
  unnest xs (i ⊗ j) = xs i j
  
 
