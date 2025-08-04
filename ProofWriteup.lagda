\begin{code}[hide]
module ProofWriteup where
\end{code}
\section{Proof of correctness}
Given the above defintion of the FFT, and our previous definition of the DFT, 
a proof of equality between the two can be formed.
This proof consists of two component parts, the first of which is the proposition.
The proposition describes the relationship between the FFT and DFT and is shown below.

\begin{code}[hide]
open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning

module Proposition (real : Real) (cplx : Cplx real) where

  open Real.Real real using (_ᵣ; ℝ)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid; distribˡ; *-comm; zeroʳ; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

  open import Data.Nat.Base using (ℕ; zero; suc; NonZero; _≡ᵇ_; nonZero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
  open import Data.Nat.Properties using (suc-injective; m*n≢0; m*n≢0⇒m≢0; m*n≢0⇒n≢0; nonZero?) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)
  open import Data.Bool using (Bool; true; false; not)
  open import Data.Bool using (T)
  open import Data.Empty

  open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
  open import Data.Unit using (⊤; tt)

  open import Matrix using (Ar; Shape; _⊗_; ι; Position; mapRows; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; length; splitAr; splitArₗ; splitArᵣ)
  open import Matrix.Equality using (_≅_; reduce-≅; tail₁-cong)
  open import Matrix.Properties using (splitArᵣ-zero; tail₁-const; zipWith-congˡ)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ; nonZeroₛ-s⇒nonZero-sᵗ; ¬nonZeroₛ-s⇒¬nonZero-sᵗ; ¬nonZero-N⇒PosN-irrelevant; ¬nonZero-sᵗ⇒¬nonZero-s)

  import Matrix.Sum as S
  open S _+_ 0ℂ +-isCommutativeMonoid using (merge-sum; sum-reindex; sum-swap)
  sum = S.sum _+_ 0ℂ +-isCommutativeMonoid
  {-# DISPLAY S.sum _+_ 0ℂ +-isCommutativeMonoid = sum #-}
  sum-cong = S.sum-cong _+_ 0ℂ +-isCommutativeMonoid

  open import Matrix.Reshape using (reshape; Reshape; flat; ♭; ♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; reindex; rev-eq; flatten-reindex; |s|≡|sᵗ|; reindex-reindex; recursive-transpose-inv)
  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

  open import FFT real cplx using (DFT; FFT; DFT′; FFT′; offset-prod; iota; twiddles)

  private
    variable
      s p r₁ r₂ : Shape
      N M : ℕ
  infixl 5 _⊡_
  _⊡_ = trans

  infix 10 #_
  #_ : Shape → ℕ
  #_ = length 

  infix 11 _ᵗ
  _ᵗ : Shape → Shape
  _ᵗ = recursive-transpose

  nz-# : NonZeroₛ s → NonZero (length s)
  nz-# = nonZeroₛ-s⇒nonZero-s

  nz-ι# : NonZeroₛ s → NonZeroₛ (ι (length s))
  nz-ι# (ι x) = ι x
  nz-ι# {s ⊗ p} (nz-s ⊗ nz-p) = ι (m*n≢0 (# s) (# p) ⦃ nz-# nz-s ⦄ ⦃ nz-# nz-p ⦄ )

  nzᵗ : NonZeroₛ s → NonZeroₛ (s ᵗ)
  nzᵗ = nonZeroₛ-s⇒nonZeroₛ-sᵗ

  rev-eq-applied : (rshp : Reshape r₂ r₁) (arr : Ar r₁ ℂ) → reshape (rshp ∙ rev rshp) arr ≅ arr 
  rev-eq-applied rshp arr i = cong arr (rev-eq rshp i)
  postulate
\end{code}
\begin{code}
    fft′≅dft′ : 
        ⦃ nz-s  : NonZeroₛ s ⦄
      → ∀ (arr : Ar s ℂ) 
      → FFT′ arr 
        ≅ 
        ( (reshape ♯) 
        ∘ (DFT′ ⦃ nz-# (nzᵗ nz-s) ⦄ )
        ∘ (reshape (reindex (|s|≡|sᵗ| {s}) ∙ ♭))) arr
\end{code}

To define this relation, pointwise equality \AF{\_≅\_} is used.
This defines equality between two matrices of shape \AF{s} to hold when
\AF{∀ (i : Position s) → xs i ≡ ys i}.
This allows for proofs to be defined for a general position \AF{i}.

As the DFT operates on the vector form, reshape operations are used to
flatten the input matrix and unflatten the output for comparison.
Not mentioned previously, is the reindex operation.
As the output of the FFT must be read in column major order, it is of the
form \AF{recursive-transpose s}.
When flattened this gives a matrix of shape \AF{ι (length (recursive-transpose s))}.
Meanwhile, without the use of reindex, the output of the DFT is of shape
\AF{ι (length s)}.
Reindexing allows this to be modeled as \AF{ι (length (recursive-transpose s))}
without changing the ordering of the results in this matrix.
This allows us to make use of pointwise equality.

% https://q.uiver.app/#q=WzAsMTEsWzAsMCwiXFxvdmVyYnJhY2V7XFxiZWdpbntwbWF0cml4fSB4XzEgJiB4XzIgXFxcXCB4XzMgJiB4XzQgXFxcXCB4XzUgJiB4XzYgXFxcXCB4XzcgJiB4XzggXFxlbmR7cG1hdHJpeH19XntcXHZlcmJ8c3x9Il0sWzMsMCwiXFxvdmVyYnJhY2V7XFxiZWdpbntwbWF0cml4fSB4XzEgJiB4XzIgJiB4XzMgJiB4XzQgJiB4XzUgJiB4XzYgJiB4XzcgJiB4XzggXFxlbmR7cG1hdHJpeH19XntcXHZlcmJ8bGVuZ3RoIHN8fSJdLFsyLDBdLFswLDQsIiBcXG92ZXJicmFjZXtcXGJlZ2lue3BtYXRyaXh9IFhfMSAmIFhfMiAmIFhfMyAmIFhfNCBcXFxcIFhfNSAmIFhfNiAmIFhfNyAmIFhfOCBcXGVuZHtwbWF0cml4fX1ee1xcdmVyYnxyZWN1cnNpdmUtdHJhbnNwb3NlIHN8fSJdLFsxLDJdLFszLDIsIlxcb3ZlcmJyYWNle1xcYmVnaW57cG1hdHJpeH0gWF8xICYgWF8yICYgWF8zICYgWF80ICYgWF81ICYgWF82ICYgWF83ICYgWF84IFxcZW5ke3BtYXRyaXh9fV57XFx2ZXJifGxlbmd0aCBzfH0iXSxbMywxXSxbMyw0LCJcXGJlZ2lue3BtYXRyaXh9IFhfMSAmIFhfMiBcXFxcIFhfMyAmIFhfNCBcXFxcIFhfNSAmIFhfNiBcXFxcIFhfNyAmIFhfOCBcXGVuZHtwbWF0cml4fSJdLFs3LDAsIlxcb3ZlcmJyYWNle1xcYmVnaW57cG1hdHJpeH0geF8xICYgeF8yICYgeF8zICYgeF80ICYgeF81ICYgeF82ICYgeF83ICYgeF84IFxcZW5ke3BtYXRyaXh9fV57XFx2ZXJifGxlbmd0aCAocmVjdXJzaXZlLXRyYW5zcG9zZSBzKXx9Il0sWzcsMiwiXFxvdmVyYnJhY2V7XFxiZWdpbntwbWF0cml4fSBYXzEgJiBYXzIgJiBYXzMgJiBYXzQgJiBYXzUgJiBYXzYgJiBYXzcgJiBYXzggXFxlbmR7cG1hdHJpeH19XntcXHZlcmJ8bGVuZ3RoIChyZWN1cnNpdmUtdHJhbnNwb3NlIHMpfH0iXSxbNyw0LCIgXFxvdmVyYnJhY2V7XFxiZWdpbntwbWF0cml4fSBYXzEgJiBYXzIgJiBYXzMgJiBYXzQgXFxcXCBYXzUgJiBYXzYgJiBYXzcgJiBYXzggXFxlbmR7cG1hdHJpeH19XntcXHZlcmJ8cmVjdXJzaXZlLXRyYW5zcG9zZSBzfH0iXSxbMCwxLCJcXHZlcmJ8cmVzaGFwZSB8IFxcZmxhdCJdLFswLDMsIlxcdmVyYnxGRlR8IiwyXSxbMSw1LCJcXHZlcmJ8REZUfCJdLFs1LDcsIlxcdmVyYnxyZXNoYXBlIHxcXHNoYXJwIl0sWzMsNywiXFxub3RcXGNvbmcgXFx0ZXh0e2FzIH1cXHZlcmJ8cmVjdXJzaXZlLXRyYW5zcG9zZSBzfCBcXG5vdFxcZXF1aXYgcyIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6ImFycm93aGVhZCJ9LCJib2R5Ijp7Im5hbWUiOiJkb3R0ZWQifX19XSxbMSw4LCJcXHZlcmJ8cmVzaGFwZSAocmVpbmRleCB8fHN8XFxlcXVpdnxzXnR8XFx2ZXJifCl8IiwyXSxbOCw5LCJcXHZlcmJ8REZUfCIsMl0sWzksMTAsIlxcdmVyYnxyZXNoYXBlIHwgXFxzaGFycCIsMl0sWzMsMTAsIlxcY29uZyBcXHRleHR7YXMgfVxcdmVyYnxyZWN1cnNpdmUtdHJhbnNwb3NlIHN8IFxcZXF1aXZcXHZlcmJ8cmVjdXJzaXZlLXRyYW5zcG9zZSBzfFxcdGV4dHsgYW5kIGV2ZXJ5IGVsZW1lbnQgaXMgZXF1YWx9IiwyLHsiY3VydmUiOjUsInN0eWxlIjp7InRhaWwiOnsibmFtZSI6ImFycm93aGVhZCJ9fX1dXQ==
% Made with quiver and then messed with to make it actually work....
\[
\resizebox{\linewidth}{!}{
\begin{tikzcd}[ampersand replacement=\&]
	\begin{array}{c} 
		\overbrace{\begin{pmatrix} x_1 & x_2 \\ x_3 & x_4 \\ x_5 & x_6 \\ x_7 & x_8 \end{pmatrix}}^{\text{\texttt{s}}} 
	\end{array} 
	\&\& {} \& 
	{\overbrace{\begin{pmatrix} x_1 & \cdots & x_8 \end{pmatrix}}^{\text{\texttt{length s}}}} 
	\&\&\&\& 
	{\overbrace{\begin{pmatrix} x_1 & \cdots & x_8 \end{pmatrix}}^{\text{\texttt{length (recursive-transpose s)}}}} 
	\\
	\&\&\& {} \\
	\& {} \&\& 
	{\overbrace{\begin{pmatrix} X_1 & \cdots & X_8 \end{pmatrix}}^{\text{\texttt{length s}}}} 
	\&\&\&\& 
	{\overbrace{\begin{pmatrix} X_1 & \cdots & X_8 \end{pmatrix}}^{\text{\texttt{length (recursive-transpose s)}}}} 
	\\
	\\
	\begin{array}{c}  
		\overbrace{\begin{pmatrix} X_1 & X_2 & X_3 & X_4 \\ X_5 & X_6 & X_7 & X_8 \end{pmatrix}}^{\text{\texttt{recursive-transpose s}}} 
	\end{array} 
	\&\&\& 
	\begin{array}{c} 
		\begin{pmatrix} X_1 & X_2 \\ X_3 & X_4 \\ X_5 & X_6 \\ X_7 & X_8 \end{pmatrix} 
	\end{array} 
	\&\&\&\& 
	\begin{array}{c}  
		\overbrace{\begin{pmatrix} X_1 & X_2 & X_3 & X_4 \\ X_5 & X_6 & X_7 & X_8 \end{pmatrix}}^{\text{\texttt{recursive-transpose s}}} 
	\end{array} 
	\\
	{} \& {} \& {} \& {} \& {} \& {} \& {} \& {}  % empty 5th row so references like 5-1 exist
	\arrow["{\texttt{reshape } \flat}", from=1-1, to=1-4]
	\arrow["{\texttt{FFT}}"', from=1-1, to=5-1]
	\arrow["{\texttt{reshape reindex} }", from=1-4, to=1-8]
	\arrow["{\texttt{DFT}}", dotted, from=1-4, to=3-4]
	\arrow["{\texttt{DFT}}"', from=1-8, to=3-8]
	\arrow["{\texttt{reshape } \sharp}", dotted, from=3-4, to=5-4]
	\arrow["{\texttt{reshape } \sharp}"', from=3-8, to=5-8]
	\arrow["{\not\cong \text{ as } \texttt{recursive-transpose s} \not\equiv s}"', dotted, tail reversed, from=5-1, to=5-4]
	\arrow["{\cong \text{ as } \texttt{recursive-transpose s} \equiv \texttt{recursive-transpose s} \text{ and every element is equal}}"', curve={height=60pt}, tail reversed, from=5-1, to=5-8]
\end{tikzcd}
}
\]
\subsection{Chain of Reasoning}
While the proposition defines what we wish to prove, the chain of reasoning is
used to justify that the proof holds.
The full proof can be found in the attached files, while the most important sections
are discussed here.
It is important to note that as proofs must hold every invariant, at every step
a large amount of complexity is held within this chain of reasoning.
As done previously to hide \AF{NonZero}, as much complexity as possible is hidden 
in the below extracts from the main chain of reasoning as to improve readability.
This complexity remains important, however, as it what allows the strict guarantees 
provided by Agda to hold.


\begin{code}[hide]
open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning

module Proof (real : Real) (cplx : Cplx real) where

  open Real.Real real using (_ᵣ; ℝ)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid; distribˡ; *-comm; zeroʳ; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

  open import Data.Nat.Base using (ℕ; zero; suc; NonZero; _≡ᵇ_; nonZero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
  open import Data.Nat.Properties using (suc-injective; m*n≢0; m*n≢0⇒m≢0; m*n≢0⇒n≢0; nonZero?) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)
  open import Data.Bool using (Bool; true; false; not)
  open import Data.Bool using (T)
  open import Data.Empty

  open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
  open import Data.Unit using (⊤; tt)

  open import Matrix using (Ar; Shape; _⊗_; ι; Position; mapRows; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; length; splitAr; splitArₗ; splitArᵣ)
  open import Matrix.Equality using (_≅_; reduce-≅; tail₁-cong)
  open import Matrix.Properties using (splitArᵣ-zero; tail₁-const; zipWith-congˡ)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ; nonZeroₛ-s⇒nonZero-sᵗ; ¬nonZeroₛ-s⇒¬nonZero-sᵗ; ¬nonZero-N⇒PosN-irrelevant; ¬nonZero-sᵗ⇒¬nonZero-s)

  import Matrix.Sum as S
  open S _+_ 0ℂ +-isCommutativeMonoid using (merge-sum; sum-reindex; sum-swap)
  sum = S.sum _+_ 0ℂ +-isCommutativeMonoid
  {-# DISPLAY S.sum _+_ 0ℂ +-isCommutativeMonoid = sum #-}
  sum-cong = S.sum-cong _+_ 0ℂ +-isCommutativeMonoid

  open import Matrix.Reshape using (reshape; Reshape; flat; ♭; ♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; reindex; rev-eq; flatten-reindex; |s|≡|sᵗ|; reindex-reindex; recursive-transpose-inv)
  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

  open import FFT real cplx using (DFT; FFT; DFT′; FFT′; offset-prod; iota; twiddles)

  private
    variable
      s p r₁ r₂ : Shape
      N M : ℕ

  -----------------------------------------
  --- Shorthands to improve readability ---
  -----------------------------------------

  infixl 5 _⊡_
  _⊡_ = trans

  infix 10 #_
  #_ : Shape → ℕ
  #_ = length 

  infix 11 _ᵗ
  _ᵗ : Shape → Shape
  _ᵗ = recursive-transpose

  nz-# : NonZeroₛ s → NonZero (length s)
  nz-# = nonZeroₛ-s⇒nonZero-s

  nz-ι# : NonZeroₛ s → NonZeroₛ (ι (length s))
  nz-ι# (ι x) = ι x
  nz-ι# {s ⊗ p} (nz-s ⊗ nz-p) = ι (m*n≢0 (# s) (# p) ⦃ nz-# nz-s ⦄ ⦃ nz-# nz-p ⦄ )

  nzᵗ : NonZeroₛ s → NonZeroₛ (s ᵗ)
  nzᵗ = nonZeroₛ-s⇒nonZeroₛ-sᵗ

  rev-eq-applied : (rshp : Reshape r₂ r₁) (arr : Ar r₁ ℂ) → reshape (rshp ∙ rev rshp) arr ≅ arr 
  rev-eq-applied rshp arr i = cong arr (rev-eq rshp i)

  -------------------------------------------
  --- 4 way associativity helper function ---
  -------------------------------------------

  assoc₄ : (a b c d : ℂ) → a * b * c * d ≡ a * (b * c * d)
  assoc₄ a b c d rewrite
      *-assoc a b c
    | *-assoc a (b * c) d
    = refl

  --------------------------
  --- Properties of iota ---
  --------------------------

  iota-reindex : ∀ {i : Position (ι N)} → (prf : M ≡ N) → iota (i ⟨ reindex prf ⟩) ≡ iota i
  iota-reindex refl = refl

  iota-split : ∀ 
     (k₀   : Position (ι (# r₂)))
     (k₁   : Position (ι (# r₁)))
     → iota ((k₁ ⊗ k₀) ⟨ split ⟩) ≡ (# r₂ *ₙ iota k₁) +ₙ iota k₀
  iota-split (ι k₀) (ι k₁) rewrite toℕ-combine k₁ k₀ = refl

  -----------------------------
  --- Congurance properties ---
  -----------------------------

  -ω-cong₂ : 
    ∀ {n m : ℕ} 
    → ⦃ nonZero-n : NonZero n ⦄
    → ⦃ nonZero-m : NonZero m ⦄
    → ∀ {k j : ℕ} 
    → (prfₗ : n ≡ m)
    → k ≡ j 
    → -ω n ⦃ nonZero-n ⦄ k ≡ -ω m ⦃ nonZero-m ⦄ j
  -ω-cong₂ refl refl = refl

  DFT′-cong : ∀ {xs ys : Ar (ι N) ℂ} → ⦃ nonZero-N : NonZero N ⦄ → xs ≅ ys → DFT′ xs ≅ DFT′ ys
  DFT′-cong {suc N} ⦃ nonZero-N ⦄ prf (ι j) = sum-cong {suc N} (λ i → cong₂ _*_ (prf i) refl)

  FFT′-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → ⦃ nonZeroₛ-s : NonZeroₛ s ⦄ → xs ≅ ys → FFT′ xs ≅ FFT′ ys
  FFT′-cong {ι N} ⦃ ι nonZero-N ⦄ = DFT′-cong ⦃ nonZero-N ⦄
  FFT′-cong {r₁ ⊗ r₂} {xs} {ys} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ prf (j₁ ⊗ j₀) =
    let instance
      _ : NonZeroₛ r₁
      _ = nonZero-r₁
      _ : NonZeroₛ r₂
      _ = nonZero-r₂
    in  (FFT′-cong {r₂} λ{ k₀ → 
          (cong₂ _*_ 
            ((FFT′-cong {r₁} λ{k₁ → 
              prf (k₁ ⊗ k₀) 
            }) j₀ ) 
            refl
          ) 
        }) j₁

  -------------------------
  --- Properties of Sum ---
  -------------------------

  -- Of note here is that I cannot put this in the sum module as it requires knowledge of _+_ as well as its relation with _*_

  *-distribˡ-sum : {xs : Ar (ι N) ℂ} (x : ℂ) → x * (sum xs) ≡ sum (map (x *_) xs)
  *-distribˡ-sum {zero} {xs} x = zeroʳ x
  *-distribˡ-sum {suc N} {xs} x rewrite 
      distribˡ x (xs (ι fzero)) (sum (tail₁ xs)) 
    | *-distribˡ-sum {N} {tail₁ xs} x 
    = cong₂ _+_ refl (sum-cong {N} (λ{(ι i) → refl }))

  *-distribʳ-sum : {xs : Ar (ι N) ℂ} (x : ℂ) → (sum xs) * x ≡ sum (map (_* x) xs)
  *-distribʳ-sum {N} {xs} x rewrite
      *-comm (sum xs) x
    | *-distribˡ-sum {N} {xs} x
    = sum-cong {N} λ i → *-comm x (xs i)

  ------------------------------------
  --- Rearanging of roots of unity ---
  ------------------------------------
  cooley-tukey-derivation : 
    ∀ (r₁ r₂ k₀ k₁ j₀ j₁ : ℕ) 
    → ⦃ nonZero-r₁   : NonZero r₁ ⦄
    → ⦃ nonZero-r₂   : NonZero r₂ ⦄
    → 
              -ω 
                (r₂ *ₙ r₁) 
                ⦃ m*n≢0 r₂ r₁ ⦄
                (
                  (r₂ *ₙ k₁ +ₙ k₀) 
                  *ₙ 
                  (r₁ *ₙ j₁ +ₙ j₀) 
                )
              ≡
                -ω (r₁) (k₁ *ₙ j₀) 
              * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
              * -ω (r₂) (k₀ *ₙ j₁)
  cooley-tukey-derivation r₁ r₂ k₀ k₁ j₀ j₁ ⦃ nonZero-r₁ ⦄ ⦃ nonZero-r₂ ⦄
    = rearrange-ω-power 
    ⊡ split-ω
    ⊡ remove-constant-term
    ⊡ simplify-bases
    where
      instance
        _ : NonZero (r₁ *ₙ r₂)
        _ = m*n≢0 r₁ r₂
        _ : NonZero (r₂ *ₙ r₁)
        _ = m*n≢0 r₂ r₁ 
      simplify-bases :
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
        ≡
            -ω (r₁) (k₁ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂) (k₀ *ₙ j₁)
      simplify-bases = 
          cong₂ 
            _*_ 
            ( cong₂
                  _*_
                  (ω-r₁x-r₁y r₂ r₁ (k₁ *ₙ j₀))
                  refl
            )
            (   -ω-cong₂ (*ₙ-comm r₂ r₁) refl
              ⊡ (ω-r₁x-r₁y r₁ r₂ (k₀ *ₙ j₁))
            )
      remove-constant-term :
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ ((r₂ *ₙ r₁) *ₙ (j₁ *ₙ k₁))
        ≡
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
      remove-constant-term =
          cong₂ _*_ refl (ω-N-mN {r₂ *ₙ r₁} {j₁ *ₙ k₁})
        ⊡ *-identityʳ _
      rearrange-ω-power :
          -ω 
            (r₂ *ₙ r₁) 
            (  (r₂ *ₙ k₁ +ₙ k₀) 
            *ₙ (r₁ *ₙ j₁ +ₙ j₀) 
            )
        
        ≡ 
          -ω 
            (r₂ *ₙ r₁)
            ( r₂ *ₙ (k₁ *ₙ j₀) 
            +ₙ k₀ *ₙ j₀ 
            +ₙ r₁ *ₙ (k₀ *ₙ j₁) 
            +ₙ r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))
            )
      rearrange-ω-power = 
        -ω-cong₂ 
          refl 
          (solve 
            6 
            (λ r₁ℕ r₂ℕ k₀ℕ k₁ℕ j₀ℕ j₁ℕ → (r₂ℕ :* k₁ℕ :+ k₀ℕ) :* (r₁ℕ :* j₁ℕ :+ j₀ℕ) := r₂ℕ :* (k₁ℕ :* j₀ℕ) :+ k₀ℕ :* j₀ℕ :+ r₁ℕ :* (k₀ℕ :* j₁ℕ) :+ r₂ℕ :* (r₁ℕ :* (j₁ℕ :* k₁ℕ))) 
            refl 
            r₁ r₂ k₀ k₁ j₀ j₁
          )
      split-ω :
          -ω 
            (r₂ *ₙ r₁)
            ( r₂ *ₙ (k₁ *ₙ j₀) 
            +ₙ k₀ *ₙ j₀ 
            +ₙ r₁ *ₙ (k₀ *ₙ j₁) 
            +ₙ r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))
            )
          ≡
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ ((r₂ *ₙ r₁) *ₙ (j₁ *ₙ k₁))
      split-ω = 
            (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀ +ₙ r₁ *ₙ (k₀ *ₙ j₁)} {r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))} )
          ⊡ (flip $ cong₂ _*_) (-ω-cong₂ refl $ sym $ *ₙ-assoc r₂ r₁ (j₁ *ₙ k₁)) 
          ( (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀                    } {r₁ *ₙ (k₀ *ₙ j₁)        } )
          ⊡ (flip $ cong₂ _*_) refl 
            (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀)                                } {k₀ *ₙ j₀                } )
          )

  cooley-tukey-derivation-application : ∀
     (j₁   : Position (r₂ ᵗ))
     (j₀   : Position (r₁ ᵗ))
     (k₀   : Position (ι (# r₂ ᵗ)))
     (k₁   : Position (ι (# r₁ ᵗ)))
     → (nz-r₁ : NonZeroₛ r₁)
     → (nz-r₂ : NonZeroₛ r₂)
     → 
          -ω 
            (# r₁ ᵗ) 
            ⦃ nz-# (nzᵗ nz-r₁) ⦄
            (iota k₁ *ₙ iota (j₀ ⟨ rev ♭ ⟩)) 
        * -ω 
            (# r₂ *ₙ # r₁ ᵗ)
            ⦃ m*n≢0 (# r₂) (# r₁ ᵗ) ⦃ nz-# nz-r₂ ⦄ ⦃ nz-# (nzᵗ nz-r₁) ⦄ ⦄
            (iota (((k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) ⟨ ♭ ⟩) ⟨ rev (♭ {r₂}) ⟩) *ₙ iota (j₀ ⟨ rev ♭ ⟩)) 
        * -ω 
            (# r₂ ᵗ) 
            ⦃ nz-# (nzᵗ nz-r₂) ⦄
            (iota k₀ *ₙ iota (j₁ ⟨ rev ♭ ⟩))
        ≡
          -ω 
            (# r₂ ᵗ *ₙ # r₁ ᵗ)
            ⦃ m*n≢0 (# r₂ ᵗ) (# r₁ ᵗ) ⦃ nz-# (nzᵗ nz-r₂) ⦄ ⦃ nz-# (nzᵗ nz-r₁) ⦄ ⦄
            (iota (((k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩) ⊗ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩)) ⟨ split ⟩) *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
  cooley-tukey-derivation-application {r₂} {r₁} j₁ j₀ k₀ k₁ nz-r₁ nz-r₂ =
    let instance
      _ : NonZero (# r₁)
      _ = nz-# nz-r₁
      _ : NonZero (# r₂)
      _ = nz-# nz-r₂
      _ : NonZero (# r₁ ᵗ)
      _ = nz-# (nzᵗ nz-r₁)
      _ : NonZero (# r₂ ᵗ)
      _ = nz-# (nzᵗ nz-r₂)
      _ : NonZero (# r₂ *ₙ # r₁ ᵗ)
      _ = m*n≢0 (# r₂) (# r₁ ᵗ)
      _ : NonZero (# r₂ ᵗ *ₙ # r₁ ᵗ)
      _ = m*n≢0 (# r₂ ᵗ) (# r₁ ᵗ)
    in begin
    _ ≡⟨  cong₂ _*_ 
            ( cong₂ _*_ 
                refl 
                ( -ω-cong₂ 
                    ( cong₂ _*ₙ_ (|s|≡|sᵗ| {r₂}) refl) 
                    ( cong₂ _*ₙ_ 
                        ( (cong 
                              iota 
                              (rev-eq {r₂} ♭ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩))
                          ) 
                        ⊡ (iota-reindex (|s|≡|sᵗ| {r₂}))
                        )
                        refl
                    )
                )
            ) 
            refl 
      ⟩
    _ ≡⟨ sym (cooley-tukey-derivation
          (# r₁ ᵗ) 
          (# r₂ ᵗ) 
          (iota k₀) 
          (iota k₁) 
          (iota (j₀ ⟨ rev ♭ ⟩)) 
          (iota (j₁ ⟨ rev ♭ ⟩)) 
         )
       ⟩
    _ ≡⟨ sym (-ω-cong₂ refl 
            (cong (_*ₙ (# r₁ ᵗ *ₙ iota (j₁ ⟨ rev ♭ ⟩) +ₙ iota (j₀ ⟨ rev ♭ ⟩))) 
              (cong ((# r₂ ᵗ *ₙ iota k₁ +ₙ_))
                (iota-reindex (|s|≡|sᵗ| {r₂}))
              )
            )
           ) 
     ⟩
    _ ≡⟨ sym (-ω-cong₂ refl 
            (cong (_*ₙ (# r₁ ᵗ *ₙ iota (j₁ ⟨ rev ♭ ⟩) +ₙ iota (j₀ ⟨ rev ♭ ⟩))) 
              (cong (_+ₙ iota (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩)) 
                (cong (# r₂ ᵗ *ₙ_) (iota-reindex {# r₁ ᵗ} {# r₁} {k₁} (|s|≡|sᵗ| {r₁})))
              )
            )
           ) 
     ⟩
    _ ≡⟨ sym (-ω-cong₂ refl (cong₂ _*ₙ_ (cong₂ _+ₙ_ (cong₂ _*ₙ_ (|s|≡|sᵗ| {r₂}) refl) refl) refl)) ⟩
    _ ≡⟨ sym (-ω-cong₂ refl 
                (cong₂ _*ₙ_ 
                    (iota-split 
                      {r₂} 
                      {r₁} 
                      (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) 
                      (k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩)
                    ) 
                    (iota-split 
                      {ι (# r₁ ᵗ)} 
                      {ι (# r₂ ᵗ)} 
                      (j₀ ⟨ rev ♭ ⟩) 
                      (j₁ ⟨ rev ♭ ⟩)
                    )
                )
              ) 
        ⟩ 
    _ ∎
    
  -----------------
  --- FFT ≡ DFT ---
  -----------------

  fft′≅dft′ : 
      ⦃ nz-s  : NonZeroₛ s ⦄
    → ∀ (arr : Ar s ℂ) 
    → FFT′ arr 
      ≅ 
      ( (reshape ♯) 
      ∘ (DFT′ ⦃ nz-# (nzᵗ nz-s) ⦄ )
      ∘ (reshape flatten-reindex)) arr
\end{code}
\subsubsection{Inductive Step}
The core of this proof which allows its application to any shape is the inductive step,
this is also the first section of the proof.
\begin{AgdaMultiCode}
\begin{code}[number=code:fft′≡dft′-ιN]
  fft′≅dft′ {ι N} ⦃ ι nz-N ⦄ arr i = refl
\end{code}
\begin{code}[number=code:fft′≡dft′-r₁⊗r₂]
  fft′≅dft′ {r₁ ⊗ r₂} ⦃ nz-r₁ ⊗ nz-r₂ ⦄ arr (j₁ ⊗ j₀) =
\end{code}
\begin{code}[hide]
    let instance
      _ : NonZeroₛ r₁
      _ = nz-r₁
      _ : NonZeroₛ r₂
      _ = nz-r₂
      _ : NonZero (# r₁)
      _ = (nz-# nz-r₁)
      _ : NonZero (# r₂)
      _ = (nz-# nz-r₂)
      _ : NonZero (# r₁ ᵗ)
      _ = (nz-# (nzᵗ nz-r₁))
      _ : NonZero (# r₂ ᵗ)
      _ = (nz-# (nzᵗ nz-r₂))
      _ : NonZero (# r₂   *ₙ # r₁ ᵗ)
      _ = m*n≢0 (# r₂) (# r₁ ᵗ)
      _ : NonZero (# r₂ ᵗ *ₙ # r₁ ᵗ)
      _ = m*n≢0 (# r₂ ᵗ) (# r₁ ᵗ)
    in 
\end{code}
These first two lines of this chain of reasoning split the proof on the shape 
of the input matrix.
\ref{code:fft′≡dft′-ιN} pattern matches the case where the shape is one dimensional, 
as FFT on such a shape is equal by definition to the DFT, no chain of reasoning 
is required to prove this case.
This is the base case of the induction.
\ref{code:fft′≡dft′-r₁⊗r₂} pattern matches on the alternate case, and precedes 
the remainder of the proof, where \AF{r₁} and \AF{r₂} represent the left and right
sub shapes.

\begin{code}
      begin
\end{code}
\begin{code}[number=code:fft′≡dft′-lhs]
        FFT′ {r₂} (λ k₀ → 
            FFT′ {r₁} (λ k₁ → _) j₀ * _
        ) j₁
\end{code}
\begin{code}[number=code:fft′≡dft′-inductive-step-1]
      ≡⟨ fft′≅dft′ _ j₁ ⟩
        DFT′ {# r₂ ᵗ} (λ k₀ →
            FFT′ {r₁} (λ k₁ → _) j₀ * _
        ) (j₁ ⟨ ♯ ⟩)
\end{code}
\begin{code}[number=code:fft′≡dft′-inductive-step-2]
      ≡⟨ DFT′-cong (λ x → cong₂ _*_ (fft′≅dft′ _ j₀) refl) (j₁ ⟨ ♯ ⟩ ) ⟩
        DFT′ {# r₂ ᵗ} (λ k₀ →
            DFT′ {# r₁ ᵗ} (λ k₁ → _) (j₀ ⟨ ♯ ⟩) * _
        ) (j₁ ⟨ ♯ ⟩)
      -- ...
\end{code}
Splitting upon the shape allows the left hand side to take 
the form shown in step \ref{code:fft′≡dft′-lhs}.
Step \ref{code:fft′≡dft′-inductive-step-1} and \ref{code:fft′≡dft′-inductive-step-2}
are then able to apply the proposition currently being proven to the outer and
inner instances of FFT′.
This allows both instances to be represented as DFT′, which in turn allows for
the representation of the left hand side in sum form.
\begin{code}
      ≡⟨⟩
        sum {# r₂ ᵗ} (λ k →                   
            sum {# r₁ ᵗ} (λ k₁ → 
                arr _                         
              * 
                -ω _ _                        -- Inner DFT -ω
            )  
          *
            -ω _ _                            -- Twiddle Factor -ω
          *
            -ω _ _                            -- Outer DFT -ω
        )
\end{code}
\begin{code}[hide]
        ≡⟨  sum-cong {  # r₂ ᵗ } 
              (λ k₀ → 
                  cong₂ _*_ (*-distribʳ-sum {# r₁ ᵗ} _) refl
                ⊡ *-distribʳ-sum {# r₁ ᵗ} _
                ⊡ sum-cong {# r₁ ᵗ }
                    (λ k₁ → 
                        assoc₄ _ _ _ _ 
                      ⊡ cong₂ _*_ 
                          (sym ((rev-eq-applied split (reshape (♭ ⊕ ♭) arr)) (_ ⊗ _))) 
                          refl
                    )
              )
          ⟩
      _ ≡⟨  sum-cong {  # r₂ ᵗ } (λ k₀ → 
              sum-cong {# r₁ ᵗ } (λ k₁ → 
                cong₂ _*_ refl
                  (cooley-tukey-derivation-application j₁ j₀ k₀ k₁ nz-r₁ nz-r₂)
              )
            )
          ⟩
      _ ≡⟨  sum-cong {# r₂ ᵗ} (λ k₀ → sym (sum-reindex (|s|≡|sᵗ| {r₁})))
          ⊡ sym (sum-reindex (|s|≡|sᵗ| {r₂})) 
         ⟩
      _ ≡⟨  sum-swap {# r₂} {# r₁} _ 
          ⊡ merge-sum {# r₁} {# r₂} _
         ⟩
            sum { # (r₁ ⊗ r₂) }
              (λ k →
                   arr (((k) ⟨ flat ⟩) ⟨ ♭ ⊕ ♭ ⟩)
                 *
                   -ω
                     (# r₂ ᵗ *ₙ # r₁ ᵗ)
                     (iota k *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
              )
        ≡⟨ sum-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂}) ⟩
          sum {# (r₁ ⊗ r₂) ᵗ} _
        ≡⟨ sum-cong 
          {# (r₁ ⊗ r₂) ᵗ} 
          (λ k → 
              cong₂ _*_ 
                refl 
                (-ω-cong₂ 
                  refl 
                  (cong₂ _*ₙ_ (iota-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂})) refl)
                )
          ) 
        ⟩
        (reshape ♯ ∘ (DFT′ {length (recursive-transpose (r₁ ⊗ r₂))}) ∘ reshape flatten-reindex) arr (j₁ ⊗ j₀)
      ∎
\end{code}
\end{AgdaMultiCode}
\subsubsection{Cooley Tukey Derivation}
\begin{code}[hide]
module ct-derivation (real : Real) (cplx : Cplx real) where
  open Real.Real real using (_ᵣ; ℝ)
    renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)
  open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

  open AlgebraStructures  {A = ℂ} _≡_
  open AlgebraDefinitions {A = ℂ} _≡_

  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid; distribˡ; *-comm; zeroʳ; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

  open import Data.Nat.Base using (ℕ; zero; suc; NonZero; _≡ᵇ_; nonZero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
  open import Data.Nat.Properties using (suc-injective; m*n≢0; m*n≢0⇒m≢0; m*n≢0⇒n≢0; nonZero?) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
    +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
  open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)
  open import Data.Bool using (Bool; true; false; not)
  open import Data.Bool using (T)
  open import Data.Empty

  open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
  open import Data.Unit using (⊤; tt)

  open import Matrix using (Ar; Shape; _⊗_; ι; Position; mapRows; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; length; splitAr; splitArₗ; splitArᵣ)
  open import Matrix.Equality using (_≅_; reduce-≅; tail₁-cong)
  open import Matrix.Properties using (splitArᵣ-zero; tail₁-const; zipWith-congˡ)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ; nonZeroₛ-s⇒nonZero-sᵗ; ¬nonZeroₛ-s⇒¬nonZero-sᵗ; ¬nonZero-N⇒PosN-irrelevant; ¬nonZero-sᵗ⇒¬nonZero-s)

  import Matrix.Sum as S
  open S _+_ 0ℂ +-isCommutativeMonoid using (merge-sum; sum-reindex; sum-swap)
  sum = S.sum _+_ 0ℂ +-isCommutativeMonoid
  {-# DISPLAY S.sum _+_ 0ℂ +-isCommutativeMonoid = sum #-}
  sum-cong = S.sum-cong _+_ 0ℂ +-isCommutativeMonoid

  open import Matrix.Reshape using (reshape; Reshape; flat; ♭; ♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; reindex; rev-eq; flatten-reindex; |s|≡|sᵗ|; reindex-reindex; recursive-transpose-inv)
  open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

  open import FFT real cplx using (DFT; FFT; DFT′; FFT′; offset-prod; iota; twiddles)

  private
    variable
      s p r₁ r₂ : Shape
      N M : ℕ

  -----------------------------------------
  --- Shorthands to improve readability ---
  -----------------------------------------

  infixl 5 _⊡_
  _⊡_ = trans

  infix 10 #_
  #_ : Shape → ℕ
  #_ = length 

  infix 11 _ᵗ
  _ᵗ : Shape → Shape
  _ᵗ = recursive-transpose

  nz-# : NonZeroₛ s → NonZero (length s)
  nz-# = nonZeroₛ-s⇒nonZero-s

  nz-ι# : NonZeroₛ s → NonZeroₛ (ι (length s))
  nz-ι# (ι x) = ι x
  nz-ι# {s ⊗ p} (nz-s ⊗ nz-p) = ι (m*n≢0 (# s) (# p) ⦃ nz-# nz-s ⦄ ⦃ nz-# nz-p ⦄ )

  -ω-cong₂ : 
    ∀ {n m : ℕ} 
    → ⦃ nonZero-n : NonZero n ⦄
    → ⦃ nonZero-m : NonZero m ⦄
    → ∀ {k j : ℕ} 
    → (prfₗ : n ≡ m)
    → k ≡ j 
    → -ω n ⦃ nonZero-n ⦄ k ≡ -ω m ⦃ nonZero-m ⦄ j
  -ω-cong₂ refl refl = refl

\end{code}
Using the rule that $c\times\sum_{i=0}^n{x_i}\equiv\sum_{i=0}^n{cx_i}$, the two
instances of -ω in the outer sum, can be moved into the inner sum.
With all instances of \AF{-ω} gathered, the rules of the roots of unity can be
used, following the inverse of the initial Cooley Tukey derivation to represent 
all roots of unity as one root of unity.
\todo[color=green]{Written like a six year old with their pen license, reword}
% \ref{sec:complex_numbers}

\begin{code}
  cooley-tukey-derivation : 
    ∀ (r₁ r₂ k₀ k₁ j₀ j₁ : ℕ) 
    → ⦃ nonZero-r₁   : NonZero r₁ ⦄
    → ⦃ nonZero-r₂   : NonZero r₂ ⦄
    → 
              -ω 
                (r₂ *ₙ r₁) 
                ⦃ m*n≢0 r₂ r₁ ⦄
                (
                  (r₂ *ₙ k₁ +ₙ k₀) 
                  *ₙ 
                  (r₁ *ₙ j₁ +ₙ j₀) 
                )
              ≡
                -ω (r₁) (k₁ *ₙ j₀) 
              * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
              * -ω (r₂) (k₀ *ₙ j₁)
  cooley-tukey-derivation r₁ r₂ k₀ k₁ j₀ j₁ ⦃ nonZero-r₁ ⦄ ⦃ nonZero-r₂ ⦄
    = rearrange-ω-power 
    ⊡ split-ω
    ⊡ remove-constant-term
    ⊡ simplify-bases
\end{code}
\begin{code}[hide]
    where
      instance
        _ : NonZero (r₁ *ₙ r₂)
        _ = m*n≢0 r₁ r₂
        _ : NonZero (r₂ *ₙ r₁)
        _ = m*n≢0 r₂ r₁ 
      simplify-bases :
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
        ≡
            -ω (r₁) (k₁ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂) (k₀ *ₙ j₁)
      simplify-bases = 
          cong₂ 
            _*_ 
            ( cong₂
                  _*_
                  (ω-r₁x-r₁y r₂ r₁ (k₁ *ₙ j₀))
                  refl
            )
            (   -ω-cong₂ (*ₙ-comm r₂ r₁) refl
              ⊡ (ω-r₁x-r₁y r₁ r₂ (k₀ *ₙ j₁))
            )
      remove-constant-term :
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ ((r₂ *ₙ r₁) *ₙ (j₁ *ₙ k₁))
        ≡
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
      remove-constant-term =
          cong₂ _*_ refl (ω-N-mN {r₂ *ₙ r₁} {j₁ *ₙ k₁})
        ⊡ *-identityʳ _
      rearrange-ω-power :
          -ω 
            (r₂ *ₙ r₁) 
            (  (r₂ *ₙ k₁ +ₙ k₀) 
            *ₙ (r₁ *ₙ j₁ +ₙ j₀) 
            )
        
        ≡ 
          -ω 
            (r₂ *ₙ r₁)
            ( r₂ *ₙ (k₁ *ₙ j₀) 
            +ₙ k₀ *ₙ j₀ 
            +ₙ r₁ *ₙ (k₀ *ₙ j₁) 
            +ₙ r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))
            )
      rearrange-ω-power = 
        -ω-cong₂ 
          refl 
          (solve 
            6 
            (λ r₁ℕ r₂ℕ k₀ℕ k₁ℕ j₀ℕ j₁ℕ → (r₂ℕ :* k₁ℕ :+ k₀ℕ) :* (r₁ℕ :* j₁ℕ :+ j₀ℕ) := r₂ℕ :* (k₁ℕ :* j₀ℕ) :+ k₀ℕ :* j₀ℕ :+ r₁ℕ :* (k₀ℕ :* j₁ℕ) :+ r₂ℕ :* (r₁ℕ :* (j₁ℕ :* k₁ℕ))) 
            refl 
            r₁ r₂ k₀ k₁ j₀ j₁
          )
      split-ω :
          -ω 
            (r₂ *ₙ r₁)
            ( r₂ *ₙ (k₁ *ₙ j₀) 
            +ₙ k₀ *ₙ j₀ 
            +ₙ r₁ *ₙ (k₀ *ₙ j₁) 
            +ₙ r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))
            )
          ≡
            -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
          * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ ((r₂ *ₙ r₁) *ₙ (j₁ *ₙ k₁))
      split-ω = 
            (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀ +ₙ r₁ *ₙ (k₀ *ₙ j₁)} {r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))} )
          ⊡ (flip $ cong₂ _*_) (-ω-cong₂ refl $ sym $ *ₙ-assoc r₂ r₁ (j₁ *ₙ k₁)) 
          ( (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀                    } {r₁ *ₙ (k₀ *ₙ j₁)        } )
          ⊡ (flip $ cong₂ _*_) refl 
            (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀)                                } {k₀ *ₙ j₀                } )
          )
\end{code}
\subsubsection{Nesting of Sums}

