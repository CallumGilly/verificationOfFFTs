module FFT.SimpleParameterisedRelation where
{-
  
  open import FFT cplx as OLDFFT
  import Proof cplx as Pr
  import Matrix as M
  import Matrix.Reshape as R
  import Matrix.NonZero as NZ

  open import Relation.Nullary
  open import Data.Empty

  open Cplx cplx using (+-*-isCommutativeRing)
  open import Algebra.Structures as AlgebraStructures
  open AlgebraStructures {A = ℂ} _≡_
  open AlgebraStructures.IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid) renaming (*-comm to *𝕔-comm)

  open B
  module NEWFFT = F ℕ-Mon
  module A′ = A ℕ-Mon  

  FFT-cong : ∀ (xs ys : Ar₂ (proj₁ s₂) ℂ) 
              → (∀ j → xs j ≡ ys j) 
              → (∀ i → FFT xs i ≡ FFT ys i)
  FFT-cong _ _ = Pr.FFT-cong 

  newTwid : ∀ {s p : A′.S} → A′.P s → A′.P p → ℂ
  newTwid {s} {p} i j = OLDFFT.twiddles 
                          ((P₁-to-P₂ i) M.⊗ (P₁-to-P₂ j))

  Rtrans≡Atrans : (R.recursive-transpose $ proj₁ (S₁-to-S₂ s₁)) ≡ proj₁ (S₁-to-S₂ (A′.transp s₁))
  Rtrans≡Atrans {ι _} = refl
  Rtrans≡Atrans {s₁ ⊗ s₂} = cong₂ M._⊗_ (Rtrans≡Atrans {s₂}) (Rtrans≡Atrans {s₁})

  lemma₂ : M.length (R.recursive-transpose (proj₁ (S₁-to-S₂ s₁))) ≡
           M.length (proj₁ (S₁-to-S₂ (A′.transp s₁)))
  lemma₂ {ι x} = refl
  lemma₂ {s₁ ⊗ s₂} = cong₂ _*_ (lemma₂ {s₂}) (lemma₂ {s₁})

  lemma₁ : iota 
            ((P₁-to-P₂ i₁ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩) 
            ≡ 
           iota 
            (P₁-to-P₂ (i₁ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
  lemma₁ {ι _} {ι _} = refl
  lemma₁ {s₁ ⊗ s₂} {i₁ ⊗ i₂} =
      Pr.iota-split 
              {R.recursive-transpose $ proj₁ $ S₁-to-S₂ s₁} 
              {R.recursive-transpose $ proj₁ $ S₁-to-S₂ s₂} 
              ((P₁-to-P₂ i₁ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
              ((P₁-to-P₂ i₂ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
      ⊡ cong₂ Nat._+_ 
                {   M.length (R.recursive-transpose (proj₁ (S₁-to-S₂ s₁))) 
                  * 
                    iota ((P₁-to-P₂ i₂ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
                } 
                {M.length (proj₁ (S₁-to-S₂ (A′.transp s₁))) * iota (P₁-to-P₂ (i₂ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)} 
                (cong₂ 
                    _*_ 
                    {M.length (R.recursive-transpose (proj₁ (S₁-to-S₂ s₁)))}
                    {M.length (proj₁ (S₁-to-S₂ (A′.transp s₁)))}
                    (lemma₂ {s₁})
                    (lemma₁ {_} {i₂})
                ) 
                (lemma₁ {_} {i₁})
      ⊡ (sym (Pr.iota-split 
              {proj₁ $ S₁-to-S₂ (A′.transp s₁)} 
              {proj₁ $ S₁-to-S₂ (A′.transp s₂)}
              (P₁-to-P₂ (i₁ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
              (P₁-to-P₂ (i₂ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
      ))

  prf : ∀ (xs : Ar₁ s₁ ℂ) (i : P₁ (s₁)) → 
        OLDFFT.FFT 
          (Ar₁-to-Ar₂ xs) 
          (R._⟨_⟩ (P₁-to-P₂ i) (R.rev R.recursive-transposeᵣ))
      ≡ NEWFFT.fft 
          (Ar₁-from-Ar₂ ∘ OLDFFT.DFT ∘ Ar₁-to-Ar₂) 
          newTwid
          xs 
          (A′._⟨_⟩ i A′.transpᵣ)
  prf {ι _} _ (ι _) = refl
  prf {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) with NZ.nonZeroDec (proj₁ (S₁-to-S₂ s₁) M.⊗ proj₁ (S₁-to-S₂ s₂))
  ... | no ¬a = ⊥-elim (¬a $ proj₂ (S₁-to-S₂ s₁) NZ.⊗ proj₂ (S₁-to-S₂ s₂))
  ... | yes (nz-s₁ NZ.⊗ nz-s₂) =
      (FFT-cong 
          _
          _ 
          (λ j → 
                (*𝕔-comm _ _) 
              ⊡ (cong₂ _*ᶜ_ 
                  (Pr.-ω-cong₂ 
                    {{ NZ.nonZeroₛ-s⇒nonZero-s (nz-s₂ NZ.⊗ (NZ.nonZeroₛ-s⇒nonZeroₛ-sᵗ nz-s₁)) }} 
                    {{ NZ.nonZeroₛ-s⇒nonZero-s (nz-s₂ NZ.⊗ (proj₂ $ S₁-to-S₂ (A′.transp s₁))) }} 
                    (cong₂ _*_ 
                        {M.length (proj₁ (S₁-to-S₂ s₂))} 
                        {M.length (proj₁ (S₁-to-S₂ s₂))} 
                        {M.length (R.recursive-transpose $ proj₁ (S₁-to-S₂ s₁))} 
                        {M.length (proj₁ (S₁-to-S₂ (A′.transp s₁)))} 
                        refl 
                        (cong M.length (Rtrans≡Atrans {s₁}))
                    )
                    (cong₂ _*_ 
                        (cong 
                            iota 
                            (cong 
                                (λ f → R._⟨_⟩ f (R.rev R.♭)) 
                                (sym (P-inv₁ {s₂} {j} {nz-s₂}))
                            )
                        )
                        (lemma₁ {s₁} {i₁})
                    )
                  )
                  (prf (λ j₁ → _) i₁)
              )
          ) 
          (P₁-to-P₂ i₂ R.⟨ R.rev R.recursive-transposeᵣ ⟩)
      )
      ⊡ (prf {s₂} 
          (λ j →
              newTwid {s₂} {A′.transp s₁} j (i₁ A′.⟨ A′.transpᵣ ⟩)
             *ᶜ
             NEWFFT.fft
              (Ar₁-from-Ar₂ ∘ OLDFFT.DFT ∘ Ar₁-to-Ar₂)
              newTwid
              (λ j₁ → xs (j₁ A′.⊗ j)) (i₁ A′.⟨ A′.transpᵣ ⟩)
          ) i₂)
-}
