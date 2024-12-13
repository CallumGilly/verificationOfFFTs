module src.TestFloatImplementation where
open import src.Real using (Real)
import Agda.Builtin.Float as Float 
open Float using (Float; primNatToFloat; primFloatPlus; primFloatMinus; primFloatTimes; primFloatDiv)
open Float using (primFloatNegate; primFloatCos; primFloatSin)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

myReals : Real
myReals = record
   { ℝ            = Float
   ; _ᵣ           = primNatToFloat

    -- In no world should I be representing pi like this this is stupid, but this is a test
   ; π            = 3.14159265359

   ; _+_         = primFloatPlus
   ; _-_         = primFloatMinus
   ; _*_         = primFloatTimes
   ; _/_         = primFloatDiv
   ; -ᵣ_          = primFloatNegate

   ; cos          = primFloatCos
   ; sin          = primFloatSin
   ; double-negative = λ{x → ?} 

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

open Real myReals using (-_; _ᵣ; ℝ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import src.Vector using (Vec; cons; nil)
open import src.DFT myReals using (DFT)
open import src.Complex myReals using (ℂfromℕ; ℂ; fromℝ;_+_i)

val36 : ℂ
val36 = ℂfromℕ 36
val22 : ℂ
val22 = ℂfromℕ 22
val45 : ℂ
val45 = ℂfromℕ 45
val15 : ℂ
val15 = ℂfromℕ 15

val118 : ℝ 
val118 = 118 ᵣ
val0   : ℝ 
val0   = 0 ᵣ
val-9  : ℝ 
val-9  = (- (9 ᵣ))
val-7  : ℝ 
val-7  = (- (7 ᵣ))
val44  : ℝ
val44  = 44 ᵣ
val7   : ℝ  
val7   = 7 ᵣ

val1   : ℂ 
val1   = ℂfromℕ 1
val-1   : ℂ 
val-1   = fromℝ (- (1 ᵣ))

-- _ : DFT (cons val36 (cons val22 (cons val45 (cons val15 nil)))) == cons (val118 + val0 i) (cons (val-9 + val-7 i) (cons (val44 + val0 i) (cons (val-9 + val7 i) nil)))
-- _ = ?
-- 
-- _ : DFT (cons val1 (cons val1 (cons val1 (cons val1 nil)))) ≡ (cons val1 (cons val1 (cons val1 (cons val-1 nil))))
-- _ = ?



open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Data.Nat using (ℕ)

toString : ∀ {n : ℕ} → Vec n ℂ → String
toString arr = "pp"

testDFT : IO ⊤
testDFT = putStrLn (toString (cons val36 (cons val22 (cons val45 (cons val15 nil)))))

main : IO ⊤
main = testDFT










