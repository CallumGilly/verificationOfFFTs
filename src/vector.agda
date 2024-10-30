module src.vector where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n; _>_; _⊓_)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-comm)
open import Data.Fin.Base using (Fin; fromℕ) renaming (zero to fzero; suc to fsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Function.Base using (_∘_)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

----------------------
---Vector Definition--
----------------------
-- Anything referencing "sampleVec" exists purely to help my own understanding

variable 
  X Y Z : Set
  m n : ℕ

Vec : Set → ℕ → Set
Vec X n = Fin n → X

-- Square braces, pretty useless all things considered but oh well
_[_] : Vec X n → Fin n → X
vec [ index ] = vec index

nil : Vec X 0
nil = λ ()

cons : X → Vec X n → Vec X (suc n)
cons x xs fzero = x
cons x xs (fsuc index) = xs index

sampleVec : Vec ℕ 3
sampleVec = cons 0 (cons 1 (cons 2 nil))

head : Vec X (suc n) → X
head vec = vec fzero
_ : head sampleVec ≡ 0
_ = refl

tail : Vec X (suc n) → Vec X n
tail vec = vec ∘ fsuc 
_ : tail sampleVec ≡ cons 1 (cons 2 nil)
_ = refl

decons : Vec X (suc n) → X × (Vec X n)
decons vec = ⟨ head vec , tail vec ⟩

replicate : (n : ℕ) → X → Vec X n
replicate zero    x = nil
replicate (suc n) x = cons x (replicate n x)

-- Playing arround, not a useful function
-- replicate′ : (n : ℕ) → (X → X) → X → Vec X n
-- replicate′ zero        step start = nil
-- replicate′ (suc count) step start = cons start (replicate′ count step (step start))
-- _ : replicate′ 4 (λ current → current + 4) 2 ≡ cons 2 (cons 6 (cons 10 (cons 14 nil))) 
-- _ = refl

concat : ∀ {n m : ℕ} {X : Set} → Vec X n → Vec X m → Vec X (n + m)
concat {zero } {zero } xs ys = nil
concat {zero } {suc m} xs ys = ys
concat {suc n} {zero } xs ys rewrite +-identityʳ n = xs
concat {suc n} {suc m} xs ys = cons (head xs) (concat (tail xs) ys)

_ : concat {0} {0} {ℕ} nil nil ≡ nil
_ = refl
_ : concat (cons 1 nil) nil ≡ cons 1 nil
_ = refl
_ : concat nil (cons 1 nil) ≡ cons 1 nil
_ = refl
_ : concat (cons 1 nil) (cons 2 nil) ≡ cons 1 (cons 2 (nil))
_ = refl
_ : concat (cons 1 (cons 2 nil)) (cons 3 (cons 4 nil)) ≡ cons 1 (cons 2 (cons 3 (cons 4 nil)))
_ = refl

map : {n : ℕ} {X Y : Set} (f : X → Y) → Vec X n → Vec Y n
map {zero } f vec = nil
map {suc n} f vec = cons (f (head vec)) (map f (tail vec))
_ : map suc nil ≡ nil
_ = refl
_ : map suc sampleVec ≡ cons 1 (cons 2 (cons 3 nil))
_ = refl
    
foldr : ∀ {len : ℕ} {X Y : Set} → (X → Y → Y) → Y → (Vec X len) → Y
foldr {zero   } _⊗_ acc vec = acc
foldr {suc len} _⊗_ acc vec = foldr _⊗_ ((head vec) ⊗ acc) (tail vec)
_ : foldr _+_ 0 sampleVec ≡ 3
_ = refl

sum : Vec ℕ n → ℕ
sum = foldr _+_ 0
_ : sum sampleVec ≡ 3
_ = refl

-- -- I have chosen to require that both the vectors being zipped are the same length here, but I should likely change this to allow vectors of any length
-- zipWith′ : ∀ {n : ℕ} {X Y Z : Set} → (f : X → Y → Z) → Vec X n → Vec Y n → Vec Z n
-- zipWith′ {zero } f xs ys = nil
-- zipWith′ {suc n} f xs ys = cons (f (head xs) (head ys)) (zipWith′ f (tail xs) (tail ys))
-- 
-- _ : zipWith′ _+_ sampleVec sampleVec ≡ cons 0 (cons 2 (cons 4 nil))
-- _ = refl

-- I refuse to type \glb when I want min, sry std lib
min : ℕ → ℕ → ℕ
min x y = x ⊓ y

zip : ∀ {n m : ℕ} {X Y : Set} → Vec X n → Vec Y m → Vec (X × Y) (min n m)
zip {zero } {zero } xs ys = nil
zip {zero } {suc m} xs ys = nil
zip {suc n} {zero } xs ys = nil
zip {suc n} {suc m} xs ys = cons ⟨ head xs , head ys ⟩ (zip (tail xs) (tail ys))

zipWith : ∀ {n m : ℕ} {X Y Z : Set} → (f : X → Y → Z) → Vec X n → Vec Y m → Vec Z (min n m)
zipWith {zero } {zero } f xs ys = nil
zipWith {zero } {suc m} f xs ys = nil
zipWith {suc n} {zero } f xs ys = nil
zipWith {suc n} {suc m} f xs ys = cons (f (head xs) (head ys)) (zipWith f (tail xs) (tail ys)) 
_ : zipWith _+_ sampleVec sampleVec ≡ cons 0 (cons 2 (cons 4 nil))
_ = refl
_ : zipWith _+_ sampleVec (replicate 4 3) ≡ cons 3 (cons 4 (cons 5 nil))
_ = refl

allᵇ : ∀ {n : ℕ} {X : Set} → (P : X → Bool) → Vec X n → Bool
allᵇ {zero } p xs = true
allᵇ {suc n} p xs = p (head xs) ∧ allᵇ p (tail xs)

anyᵇ : ∀ {n : ℕ} {X : Set} → (P : X → Bool) → Vec X n → Bool
anyᵇ {zero } p xs = false
anyᵇ {suc n} p xs with p (head xs)
...                  | true  = true
...                  | false = anyᵇ p (tail xs)










