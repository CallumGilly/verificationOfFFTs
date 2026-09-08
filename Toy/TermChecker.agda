module Toy.TermChecker where
  open import Data.List as List renaming (_++_ to _++ₗ_; [_] to [_]ₗ)
  open import Data.Nat
  open import Data.String
  open import Function

  data NOp : Set where
    Nconst : ℕ → NOp
    Nmult : NOp → NOp → NOp
    
  data COp : Set where
    var : String → COp
    Cmult : COp → COp → COp
    ω : NOp → NOp → COp

  data AssignmentOperation : Set where
    ≔ : AssignmentOperation
    += : AssignmentOperation

  mutual
    data Instruction : Set where
      comment′ : String → Instruction
      assign′ : String → AssignmentOperation → COp → Instruction
      many : Program → Instruction
      free′ : String → Instruction

    Program : Set
    Program = List Instruction
  
  mutual
    showInstruction : Instruction → String
    showInstruction (many x) = showProgram x
    showInstruction (comment′ x) = unlines $ List.map ("//" <+>_) $ lines x
    showInstruction (assign′ x x₁ x₂) = ?
    showInstruction (free′ x) = ?

    showProgram  : Program → String
    showProgram = unlines ∘ List.map (_++ ";") ∘ List.map showInstruction 

