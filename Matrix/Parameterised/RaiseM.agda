open import Matrix.Parameterised.Mon 

module Matrix.Parameterised.RaiseM (M : Mon) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)

open import Matrix.Parameterised.Base M
private
  variable
    X Y : Set
  --S = S M
  --P = P M

ε-El : Mon.El M (Mon.ε M)
ε-El = Inverse.from (Mon.unit-law M) tt 

unit-inv₁ : {x : ⊤} {y : P (ι (Mon.ε M))} → y ≡ ι (Inverse.from (Mon.unit-law M) tt) → tt ≡ x 
unit-inv₁ {tt} {ι x} prf = refl

unit-inv₂ : {x : P (ι (Mon.ε M))} {y : ⊤} → y ≡ tt → ι (Inverse.from (Mon.unit-law M) tt) ≡ x
unit-inv₂ {ι x} {tt} prf = cong ι (Inverse.inverse (Mon.unit-law M) .proj₂ refl)

unit-law : P (ι (Mon.ε M)) ↔ ⊤
unit-law = record
  { to        = λ _ → tt
  ; from      = λ _ → ι (Inverse.from (Mon.unit-law M) tt)
  ; to-cong   = λ _ → refl
  ; from-cong = λ _ → refl
  ; inverse   = unit-inv₁ , unit-inv₂
  }

pair-law : (a b : S) → P (a ⊗ b) ↔ (P a × P b)
pair-law a b = record
  { to        = λ{(a ⊗ b) → a  ,  b}
  ; from      = λ{(a  ,  b) → a ⊗ b}
  ; to-cong   = λ{refl → refl}
  ; from-cong = λ{refl → refl}
  ; inverse   = (λ{ {a , b} refl → refl }) , λ{ {a ⊗ b} refl → refl }
  }

raise-M : Mon
raise-M = record {
    U    = S
  ; El   = P
  ; ε    = ι (Mon.ε M)
  ; _●_  = _⊗_
  ; unit-law  = unit-law
  ; pair-law  = pair-law
  }

