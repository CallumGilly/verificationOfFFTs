module src.TestFloatImplementation where
open import src.reals using (Real)
import Agda.Builtin.Float as Float 
open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatSin)

myReals : Real
myReals = record
   { ℝ            = Float
   ; fromℕ        = primNatToFloat

    -- In no world should I be representing pi like this this is stupid, but this is a test
   ; π            = 3.14159265359

   ; _+ᵣ_         = primFloatPlus
   ; _-ᵣ_         = primFloatMinus
   ; _*ᵣ_         = primFloatTimes
   ; _/ᵣ_         = primFloatDiv
   ; -ᵣ_          = primFloatNegate

   ; cos          = primFloatCos
   ; sin          = primFloatSin

--    ; +ᵣ-commᵣ     = ?
--    ; *ᵣ-commᵣ     = ?
-- 
--    ; +ᵣ-assocᵣ    = ?
--    ; *ᵣ-assocᵣ    = ?
-- 
--    ; +ᵣ-identityˡ = ?
--    ; *ᵣ-identityˡ = ?
--    ; +ᵣ-identityʳ = ?
--    ; -ᵣ-identityʳ = ?
--    ; *ᵣ-identityʳ = ?
--    ; /ᵣ-identityʳ = ?
  }

open Real myReals using (-ᵣ_; fromℕ; ℝ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import src.vector using (cons; nil)
open import src.DFT myReals using (DFT)
open import src.complex myReals using (ℂfromℕ; ℂ; fromℝ;_+_i)

val36 : ℂ
val36 = ℂfromℕ 36
val22 : ℂ
val22 = ℂfromℕ 22
val45 : ℂ
val45 = ℂfromℕ 45
val15 : ℂ
val15 = ℂfromℕ 15

val118 : ℝ 
val118 = fromℕ 118
val0   : ℝ 
val0   = fromℕ 0
val-9  : ℝ 
val-9  = (-ᵣ (fromℕ 9))
val-7  : ℝ 
val-7  = (-ᵣ (fromℕ 7))
val44  : ℝ
val44  = fromℕ 44
val7   : ℝ  
val7   = fromℕ 7

_ : DFT (cons val36 (cons val22 (cons val45 (cons val15 nil)))) ≡ cons (val118 + val0 i) (cons (val-9 + val-7 i) (cons (val44 + val0 i) (cons (val-9 + val7 i) nil)))
_ = ?


















