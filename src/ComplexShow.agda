open import src.Real using (Real)
module src.ComplexShow (r : Real) where

open Real r using (ℝ) renaming (show to showReal)
open import src.Complex r using (_+_i; ℂ)
open import Agda.Builtin.String using (String; primStringAppend)

-- Makes shit less ugly
_++_ : String → String → String
_++_ = primStringAppend

show : ℂ → String
show (real + imaginary i) = (((showReal real) ++ " + ") ++ (showReal imaginary)) ++ " i"
