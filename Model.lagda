%TC:ignore
\begin{code}[hide]

module Model where -- This allows me to use arbitrary module names from here 
                   -- onwards

open import Real using (Real)

open import Data.Nat.Base using (ℕ; NonZero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (m*n≢0)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

import Algebra.Structures as AlgebraStructures
open AlgebraStructures  using (IsCommutativeMonoid)
import Algebra.Definitions as AlgebraDefinitions
open import Algebra.Core 

open import Function.Base using (_$_; _∘_)

open import Data.Product.Base using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
\end{code}
%TC:endignore
% From Equation \ref{eq:DFT_Definition} we have a definition of the DFT which we 
% know to be correct, but this is not yet in a useable form. 
% In order to prove against this definition we must define our DFT in Agda given 
% some definition of Complex numbers, and some definition of Vectors. 
% 
% As we did above, we must then perform a likewise conversion for our FFT 
% definition, Equation \ref{eq:FFT_Definition}.
% Although it would be possible to implement this definition with respect to
% an input Vector, using instead an input Matrix of arbitrary shape will make both
% the definition, and the proofs applicable to any radix or mix of radices.
% 
% Given that Vectors can be considered one dimenti


\section{Implementation}

Before the DFT and FFT can be reasoned on, it is important to define a 
framework which can accurately encode all required data, as well as 
operations on that data. 
For the DFT and FFT, this requires the definition of a number format, and a
structure in which these numbers can be represented.


\subsection{Complex Numbers}
\label{sec:complex_numbers}

The Agda Standard library does not provide definitions for Complex numbers, it
is therefore necessary for us to design and decide upon an encoding.

It is well known \cite{TheDFT}
that the DFT and FFT can be implemented on an arbitrary field-\textit{like}
\footnote{This structure is only field-\textit{like} because it does not require multiplicative inverses}
structure with roots of unity.
Agda allows this this idea to be captured precisely though the creation of a
structure, \AF{Cplx}, which axiomatizes this field and its properties which the FFT
and correctness proof rely on.
This is similar to Java interfaces, defining the carrier and operations, but also
allows for the properties (such as the associativity of addition) of this field to 
be defined.

This isolation means allows the definition of the DFT, FFT and proofs to be instantiated
for any implementation of \AF{Cplx}.
This generality allows the use of any modular field of 
sufficient size which holds the required properties, allowing operations such as 
fast multiplication to be performed upon these fields.
As Agda provides a builtin wrapper around IEEE754 floats\cite{IEEE754}
the examples shown in this paper, use a simple implementation of \AF{Cplx} built 
from pair of floating point numbers.
\begin{AgdaMultiCode}
%TC:ignore
\begin{code}[hide]
module ComplexMini (real : Real) where
  open Real.Real real using (ℝ; 0ℝ; 1ℝ; -1ℝ)

  import Algebra.Structures as AlgebraStructures
  import Algebra.Definitions as AlgebraDefinitions

  private
    variable
      N m r₁ x y k₀ k₁ : ℕ
    postulate  -- I realise how horrendusly cursed postulating an instance is...
      instance -- but it works...
        nonZero-n : NonZero N
        nonZero-r₁ : NonZero r₁
        nonZero-x : NonZero x

\end{code}
%TC:endignore
\begin{code}
  record Cplx : Set₁ where
\end{code}
%TC:ignore
\begin{code}[hide]
    infix  8 -_
    infixl 7 _*_
    infixl 6 _+_ _-_
\end{code}
%TC:endignore
\begin{code}
    field
      ℂ : Set
      _+_ : ℂ → ℂ → ℂ
\end{code}
%TC:ignore
\begin{code}[hide]
      _*_ : ℂ → ℂ → ℂ
      _-_ : ℂ → ℂ → ℂ
      -_  : ℂ → ℂ

      fromℝ : ℝ → ℂ

      e^i_ : ℝ → ℂ
      ℂ-conjugate : ℂ → ℂ

      --+ω : ∀ (N : ℕ) (k : ℕ) → ℂ
      -- Instance arguments seem pretty good https://agda.readthedocs.io/en/v2.5.4/language/instance-arguments.html
      -- ω really goes here

    0ℂ  : ℂ
    0ℂ  = fromℝ (0ℝ)
    -1ℂ : ℂ
    -1ℂ = fromℝ (-1ℝ)
    1ℂ  : ℂ
    1ℂ  = fromℝ (1ℝ)

    open AlgebraStructures  {A = ℂ} _≡_
    open AlgebraDefinitions {A = ℂ} _≡_
    
    field
\end{code}
%TC:endignore
Addition, multiplication and negation must be proven to form a commutative ring,
meaning that a set of properties, such as multiplication distributes over addition
must hold. \cite{CommRingTheory}
\begin{code}
      +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℂ 1ℂ
\end{code}
\paragraph{Roots of unity}\label{para:roots_of_unity} as described for Complex numbers in Equation 
\ref{eq:ComplexRootsOfUnity}, must be defined for some non-zero divisor $N$ 
and some power $K$, along with some properties on them.
To ensure that the divisor $N$ is never zero, a \AF{NonZero} proof argument is 
required on $N$, guaranteeing division by zero to be impossible.
This \AF{NonZero} property is an instance argument, allowing an instance 
resolution algorithm\cite{InstanceArgs}
to perform automatic resolution on it, simplifying further proofs.
\begin{code}
      -ω : (N : ℕ) → .{{ nonZero-n : NonZero N }} → (k : ℕ) → ℂ
      ω-N-0      : -ω N 0                  ≡ 1ℂ
      ω-N-mN     : -ω N (N *ₙ m)           ≡ 1ℂ
      ω-r₁x-r₁y  : -ω (r₁ *ₙ x) (r₁ *ₙ y)  ≡ -ω x y
      ω-N-k₀+k₁  : -ω N (k₀ +ₙ k₁)         ≡ (-ω N k₀) * (-ω N k₁)
\end{code}
\end{AgdaMultiCode}


\subsection{Tensors}
In Equations \ref{eq:DFT_Definition} and \ref{eq:FFTDefinitionFromDFT}, the DFT 
and FFT are both defined for any input vector $x$ of length $N$ and length 
$r_1\times r_2$ respectively. 
This implies that it would be possible to represent the input structure for both 
the DFT and the FFT in vector form, possibly using the Agda standard libraries functional
vector definition, \verb|Data.Vec.Functionals|.

Although this structure is ideal for the DFT, the FFTs relies on index splitting,
as described in Equation \ref{eq:IndexManipulation}, to decompose the input vector
into $r₁$ parts.
For vectors this would require low level index manipulation, for a single layer 
of splitting, this is not unreasonable, but can still complicate any definitions.
For multiple layers however, where the input is split into $n$ factors, this quickly
becomes complex as the multipliers and split position for each factor must be carried
through.
This would make an kind of reasoning on the FFT, as well as generalisation,
where the FFT is called iteratively, difficult as both would be
pulled down to require the same low level of index manipulation.

The need for this low level manipulation can be removed, by creating some
definition for shaped tensors, and allowing the FFT to 
accept these tensors as inputs.
These shaped tensors can also be considered as Multi-dimensional arrays.
As well as removing the need these low level manipulations, using this definition 
will also abstract the splitting of the input vector out of the FFT making any    % This may be better discussed in the FFT section...
definition radix independent.

\begin{AgdaAlign}
%TC:ignore
\begin{code}[hide]
module Matrix where
  open import Data.Nat using (ℕ; suc; zero; NonZero; _+_; _*_)
  open import Data.Fin as F using (Fin; join) renaming (zero to fzero; suc to fsuc)
  open import Data.Product.Base using (_×_) renaming ( _,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (inj₁; inj₂)

  private
    variable
      n m : ℕ
      X Y Z : Set
\end{code}
%TC:endignore
The shape of any given tensor can be described as a full binary tree of natural 
numbers.
Each leaf, \AR{ι n}, is one such natural number, one leaf 
can be considered to add one dimension to the overall shape. 
Each parent note, \AR{s ⊗ p}, joins two subtrees.
A given shape tree encodes the split of $N$ into $m$ many multipliers.

\begin{code}
  data Shape : Set where
    ι   : ℕ → Shape
    _⊗_ : Shape → Shape → Shape
\end{code}

Defining shapes as trees in place of lists allows for more information to be 
encoded about the structure of the shape. 
This data loss can be identified by converting the below tensor shapes into their
list forms, both of which are \AF{s :: p :: r :: q :: []}.
For the FFT, this additional information should allow for the structure of parallelism 
to be defined by the shape of the input tensor for a parallelised implementation.

%TC:ignore
\begin{code}[hide]
  private
    variable
      s p : Shape
  tmp : Shape → Shape → Shape → Shape → Shape 
  tmp s p r q = let
\end{code}
%TC:endignore
\begin{code}
    s₁ = (  s  ⊗  p) ⊗ (r ⊗ q)
    s₂ =    s  ⊗ (p  ⊗ (r ⊗ q))
\end{code}
%TC:ignore
\begin{code}[hide]
    in ι 4
\end{code}
%TC:endignore

Tensors can then be inductively defined as a dependant type on Shapes.
This definition takes the same form as that of shapes and defines the position 
of a non-leaf nodes as being constructed by the positions of its two children 
nodes, while leaf nodes are bound by the length of that leaf.
This binding on the length of the leaf, allows the type checker to require
evidence that a positions index is not greater than the length, removing the possibility
for runtime out of bounds errors.


\begin{code}
  data Position : Shape → Set where
    ι   : Fin n → Position (ι n)
    _⊗_ : Position s → Position p → Position (s ⊗ p)
\end{code}

\AF{Position} can then be used to define the tensor data encoding, such that
tensors form indexed types
accepting a position and returning the value at that position.

\begin{code}
  Ar : Shape → Set → Set
  Ar s X = Position s → X
\end{code}
This means any given tensor of \AF{Shape} \AR{s} and type \AR{X} accepts a
\AF{Position} of shape \AR{s} and returns a value of type \AR{X}.
This is a similar definition to that used in \cite{BlockedSinkarovs}, and
provides a basis on which tensors can be discussed
\end{AgdaAlign}
\subsubsection{Tensor length}
The most simple property which can be extracted from a tensor shape is its length.
This can be easily extracted with a recursive function on the shape.
The shorthand \AF{\#} is often used to indicate the use of length.
\begin{code}
  length : Shape → ℕ
  length (ι x) = x
  length (s ⊗ s₁) = length s * length s₁


  # : Shape → ℕ
  # = length
\end{code}

This property is requrired for the DFT and FFT to determine the base of the
roots of unity.
This base, however, requires a non zero proof argument to be provided.\ref{para:roots_of_unity}.
This can be easily achived by restricting the DFT and FFT to operate only on
tensors where no leaf is zero.
This means that any implementation of the DFT and FFT must be provided, or generate,
a proof argument that no leaf is of zero length.
For the simplicity of this paper we use the notation $Ar∔$ % Judge me how you will for using this symbol here and then changing what it really is in newunicodechar... its cursed, its horrible... but it works
to indicate that a tensor is provided such a proof argument.
This is done more explicitly in the final implementation, however, this 
adds additional arguments which obfuscate the key points.


\subsubsection{Methods on one dimension}
Given the definition of tensors, some basic operations upon them can be described.
The first of these definitions can be restricted to operate only upon the single
dimensional case.
Tensors with only one dimension can also be referred to for succinctness as vectors.

\paragraph{Head and Tail} allow for the deconstruction of any tensor of shape 
\AF{ι (suc n)}. 
\AF{head₁} returns the first element of the tensor, while
\AF{tail₁} returns all following elements in a tensor of shape \AF{ι n}.
These operations allow for recursion over vectors to be defined.

\begin{code}
  head₁ : Ar (ι (suc n)) X → X
  head₁ ar = ar (ι fzero)

  tail₁ : Ar (ι (suc n)) X → Ar (ι n) X
  tail₁ ar (ι x) = ar (ι (fsuc x))
\end{code}

% This wouldn't be good for a paper, but I feel like its useful to observe when
% describing for the thesis
One feature of Agda used regularly is seen here, pattern matching.
This is a feature taken from Haskell \cite{Norell2007}
which allows for the breaking down of some types of input fields to the 
types they are built on. 
In the above example \AR{ι x} is of type \AD{Position (suc n)}, 
which is deconstructed to expose \AR{x} of type \AD{Fin (suc n)}.

\paragraph{Sum} can then be defined over vectors using \AF{head₁} 
and \AF{tail₁}.
This definition is created generally, meaning it can be instantiated for any
commutative monoid \AF{(X, \_⋆\_, ε)} where 
\begin{itemize}
  \item \AF{X} is a set
  \item \AF{\_⋆\_} is some operation \AF{X → X → X}, such that 
  \begin{itemize}
      \item \AF{x ⋆ y ≡ y ⋆ x}
      \item \AF{(x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)}
  \end{itemize}
  \item \AF{ε} is an identity element in \AF{X} such that \AF{ε ⋆ x ≡ x}
\end{itemize}
With the above definition, sum can be defined as below.
\begin{AgdaMultiCode}
\begin{code}
module Sum {A : Set} (_⋆_ : Op₂ A) (ε : A) (isCommutativeMonoid : IsCommutativeMonoid {A = A} _≡_ _⋆_ ε) where
\end{code}
%TC:ignore
\begin{code}[hide]
  open import Data.Product.Base using (proj₁; proj₂)

  open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (*-zeroʳ)
  open import Data.Fin.Base using () renaming (zero to fzero; suc to fsuc)

  open import Matrix using (Ar; Position; ι; _⊗_; head₁; tail₁; splitArₗ; splitArᵣ)
  open import Matrix.Equality using (_≅_; reduce-≅)
  open import Matrix.Properties using (tail₁-const)

  open import Matrix.Reshape using (reshape; reindex; |s|≡|sᵗ|; _⟨_⟩; split; _∙_; eq)


  -----------------------------------------
  --- Pull out properties of the monoid ---
  -----------------------------------------

  open AlgebraDefinitions {A = A} _≡_

  open IsCommutativeMonoid isCommutativeMonoid using (identity; assoc; comm)


  private
    identityˡ : LeftIdentity ε _⋆_
    identityˡ = proj₁ identity

    identityʳ : RightIdentity ε _⋆_
    identityʳ = proj₂ identity

    variable
      n m : ℕ

  ----------------------
  --- Sum Definition ---
  ----------------------

\end{code}
%TC:endignore
\begin{code}
  sum : (xs : Ar (ι n) A) → A
  sum {zero}   xs = ε
  sum {suc n}  xs = (head₁ xs) ⋆ (sum ∘ tail₁) xs
\end{code}
\end{AgdaMultiCode}
For the DFT and FFT in this paper, this is instantiated over complex addition,
described as the monoid \AF{(ℂ, \_+\_, 0ℂ)}.
However, this definition allows for any fold-like operation to be defined for 
any instance of \AF{(X, \_⋆\_, ε)} meaning operations such as $\Pi$ can be 
instantiated with the same definition and general rules.
This is similar to how the DFT and FFT can be instantiated for any definition of
\AF{Cplx}.


%TC:ignore
\begin{code}[hide]
open import Complex using (Cplx)
module FFT (real : Real) (cplx : Cplx real) where
  open Cplx cplx using (ℂ; _*_; -ω; e^i_; _+_; 0ℂ; +-*-isCommutativeRing)

  open AlgebraStructures  {A = ℂ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

  open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Nat.Base using (ℕ; suc; NonZero) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties using (nonZero?)
  open import Relation.Nullary

  open import Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; mapLeft; length)
  open import Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape using (recursive-transpose; reshape; swap; _⟨_⟩; ♯; recursive-transposeᵣ)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ)

  private
    variable
      N : ℕ
      s p : Shape

  Ar∔ : Shape → Set → Set
  Ar∔ = Ar

  ------------------------------------
  --- DFT and FFT helper functions ---
  ------------------------------------
\end{code}
%TC:endignore

\paragraph{Index's in a single dimension}. As defined above, \AF{Position} encodes 
the bounds on a given index, as well as the index itself. 
When calculating the DFT some arithmetic on this index is required,
this arithmetic would be overly complex if performed while the index is 
wrapped in a position, and so
helper functions are required to convert a given position to its index value.
This helper function for the single dimensional case is shown below.

\begin{code}
  iota : Ar (ι N) ℕ
  iota (ι i) = toℕ i
\end{code}

\subsection{DFT}
Given the above definition of the complex numbers, tensors, and methods on one 
dimensional tensors, the formation of the DFT is now trivial.
This is of the same shape as Equation \ref{eq:DFT_Definition}, requiring through 
use of \AF{Ar∔} that the length of any input vector is non zero, as to satisfy 
this same condition on the divisor of \AF{-ω} as defined in \ref{para:roots_of_unity}.

\begin{code}
  DFT : Ar∔ (ι N) ℂ → Ar∔ (ι N) ℂ
  DFT {N} xs j = sum λ k → xs k * -ω N (iota k *ₙ iota j)
\end{code}
%TC:ignore
\begin{code}[hide]
    where
      postulate
        instance
          _ : NonZero N
\end{code}
%TC:endignore


% It is then trivial to form the \AF{DFT} without this restriction, by 
% checking if a given array is of length zero, and returning that same array of
% length zero when this is the case.



\subsection{Reshape}
%TC:ignore
\begin{code}[hide]
module Reshape where

  open import Data.Nat using (ℕ; _*_; NonZero)
  open import Data.Nat.Properties using (*-comm)
  open import Data.Fin as F using (Fin; combine; remQuot; quotRem; toℕ; cast)
  open import Data.Fin.Properties using (remQuot-combine; combine-remQuot; cast-is-id; cast-trans)

  open import Data.Product using (_,_; proj₁; proj₂)
  open import Matrix using (Shape; Position; Ar; ι; _⊗_; length)

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; trans; subst; sym)
  open Eq.≡-Reasoning

  variable
    m n k : ℕ
    s p q r : Shape
    X Y Z : Set

  infixr 5 _∙_
  infixl 10 _⊕_
\end{code}
%TC:endignore

When working with tensors, it is often necessary for elements to be rearranged, 
through operations such as transpose or flatten, without any additions or removals.
The naïve approach to this, would be to define each rearrange as a function of type \AF{Ar s X → Ar p X}.
This approach however, would operate on too large a space, meaning reasoning upon
such functions would be difficult and could not be generalised.
An alternate approach is to define a small language of reshapes.
This language captures a small set of rearrangements, as well as methods to allow
for their composition.
Generalised properties, such as how each reshape is applied to a position, can 
then be defined on this language or reshapes.

For this language, each reshape operations can be considered as a bijective function
from shape \AF{s} to shape \AF{p}. 
As this ensures that no matrix can loose or gain data, creating a strict reshape 
language will strengthen any reasoning in future proofs.
This also means that any reshape operation is reversible which will allow for the
formation of rules which are general to all operations in the reshape language.

The reshape language is defined as a set of operations from shape to shape as follows.
\begin{code}
  data Reshape : Shape → Shape → Set where
    eq     : Reshape s s                      -- Identity
    _∙_    : Reshape p q                      -- Composition of Reshapes
           → Reshape s p 
           → Reshape s q               
    _⊕_    : Reshape s p                      -- Left/ Right application
           → Reshape q r 
           → Reshape (s ⊗ q) (p ⊗ r)   
    split  : Reshape (ι (m * n)) (ι m ⊗ ι n)  -- "Vector" → 2D Tensor
    flat   : Reshape (ι m ⊗ ι n) (ι (m * n))  -- 2D Tensor → "Vector"
    swap   : Reshape (s ⊗ p) (p ⊗ s)          -- Transposition
\end{code}

Using this definition of reshape and some standard library methods on Fin, 
it is then possible do define the application of reshape to positions and tensors.
\begin{code}
  _⟨_⟩ : Position p → Reshape s p → Position s
  i            ⟨ eq      ⟩ = i
  i            ⟨ r ∙ r₁  ⟩ = i ⟨ r ⟩ ⟨ r₁ ⟩
  (i ⊗ j)      ⟨ r ⊕ r₁  ⟩ = (i ⟨ r ⟩) ⊗ (j ⟨ r₁ ⟩)
  (ι i ⊗ ι j)  ⟨ split   ⟩ = ι (combine i j)
  ι i          ⟨ flat    ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b
  (i ⊗ j)      ⟨ swap    ⟩ = j ⊗ i

  reshape : Reshape s p → Ar s X → Ar p X
  reshape r a ix = a (ix ⟨ r ⟩ )
\end{code}
\subsubsection{Reverse}
As each reshape operation is a bijective function, it is trivial to define a reverse
method.
\begin{code}
  rev : Reshape s p → Reshape p s
  rev eq = eq
  rev (r ⊕ r₁) = rev r ⊕ rev r₁
  rev (r ∙ r₁) = rev r₁ ∙ rev r
  rev split = flat
  rev flat = split
  rev swap = swap
\end{code}
From this operation, rules on reshape can be defined, allow for formation of
relations between reshape operations.
This allows for the reduction of the reshape language when operations such as 
\AF{split ∙ flat} occur.
%TC:ignore
\begin{code}[hide]
  postulate
\end{code}
%TC:endignore
\begin{code}
    rev-eq : 
      ∀ (r : Reshape s p) 
        (i : Position p ) 
      ---------------------
      → i ⟨ r ∙ rev r ⟩ ≡ i

    rev-rev : 
      ∀ (r : Reshape s p) 
        (i : Position p )
      -----------------------------
      → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩
\end{code}

\subsubsection{Recursive Reshaping}
While the above operations of reshape can be applied to matrices of a fixed shape
this language of reshapes can be improved with the creation of recursive reshape
operations.

\paragraph{Flatten and Unflatten} enable the recursive application of flat and 
split respectively.
This allows for an $N$-dimensional tensor to be flattened, and for any single dimensional
tensor of size \AF{length s} to be unflattened into a tensor of shape s.
\begin{code}
  ♭ : Reshape s (ι (length s))
  ♭ {ι x   } = eq
  ♭ {s ⊗ s₁} = flat ∙ ♭ ⊕ ♭

  -- Unflatten is free from flatten
  ♯ : Reshape (ι (length s)) s
  ♯ = rev ♭
\end{code}

\paragraph{Transpose} flips a tensor over its diagonal by swapping the left and
right sub-shape at each level.
Transpose applies swap to any non leaf nodes, allowing for any given 
function designed to operate on multi dimensional matrices, such as the FFT, to
do the same swap at each level.
It can be seen below that transpose is defined through use of the postfix operator, 
meaning the input shape goes before \AF{ᵗ}
\begin{code}
  infixl 11 _ᵗ
  _ᵗ : Shape → Shape
  _ᵗ (ι x   ) = ι x
  _ᵗ (s ⊗ s₁) = (s₁ ᵗ) ⊗ (s ᵗ)
\end{code}


\subsection{Multi dimensional tensor operations}
In addition to the above reshape operations, some methods which can operate 
directly on multi dimensional tensors are required.
\paragraph{Zip With}\label{para:zipWith} performs point-wise application of a 
given function \AD{f} over two tensors of the same shape. 
%TC:ignore
\begin{code}[hide]
module Matrix2 where
  open import Matrix using (Ar; Shape; Position; _⊗_)
  private
    variable
      X Y Z : Set
      s p : Shape
\end{code}
%TC:endignore
\begin{code}
  zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
  zipWith f arr₁ arr₂ pos = f (arr₁ pos) (arr₂ pos)
\end{code}
This has many uses, below is shown one example where zipWith is used
over matrices $x$ and $y$, of shape \AF{(ι n ⊗ ι m)},
to add the values at each position.
This two dimensional shape is defined arbitrarily for ease of readability, 
however, \AF{zipWith} is not restricted on the shape meaning a tensor of any shape can
be used.

\begin{displaymath}
  \text{zipWith  \_+\_}
  \begin{bmatrix}
    x_{1,1} & \dots  & x_{1,n} \\
    \vdots  & \ddots & \vdots \\
    x_{m,1} & \dots  & x_{m,n}
  \end{bmatrix}
  \begin{bmatrix}
    y_{1,1} & \dots  & y_{1,n} \\
    \vdots  & \ddots & \vdots \\
    y_{m,1} & \dots  & y_{m,n}
  \end{bmatrix}
  \equiv 
  \begin{bmatrix}
    x_{1,1} + y_{1,1} & \dots  & x_{1,n} + y_{1,n} \\
    \vdots                  & \ddots & \vdots \\
    x_{m,1} + y_{m,1} & \dots  & x_{m,n} + y_{m,n}
  \end{bmatrix}
\end{displaymath}


\paragraph{Map} is similar to \AF{zipWith}, but operates over a singular tensor, 
applying a function \AF{f} to each element.
\begin{code}
  map : (f : X → Y) → Ar s X → Ar s Y
  map f arr i = f (arr i)
\end{code}
The functions \AF{nest} and \AF{unnest} can then be defined to create an 
isomorphism between matrices of the form \AF{Ar (s ⊗ p) X} and nested matrices 
of the form \AF{A s (Ar p X)}.
This allows for the definition of a new function \AF{mapLeft} which can apply a
given function to each \AF{p} shaped sub tensor.

\begin{code}
  nest : Ar (s ⊗ p) X → Ar s (Ar p X)
  nest arr i j = arr (i ⊗ j)

  unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
  unnest arr (i ⊗ j) = arr i j

  mapLeft : ∀ {s p t : Shape} → (Ar p X → Ar t Y) → Ar (s ⊗ p) X → Ar (s ⊗ t) Y
  mapLeft f arr = unnest (map f (nest arr))
\end{code}


\clearpage
\subsection{FFT}
Given the above operations, it is now possible to begin forming a definition for
the FFT.
As the FFT can only operate on tensors with at least one element, \AF{Ar∔} is used again
as the input type to indicate that a given input is paired with a nonZero proof 
argument.
This is done slightly differently in the final proof which can be found in the
attached files.

Looking at the basic derivation of the Cooley Tukey FFT over an input vector
defined in Equation \ref{eq:FFTDefinitionFromDFT}, three distinct sections can
be observed.
\begin{align}
    X_{j_1r_1+j_0}
      &=\underbrace{\sum^{r_2-1}_{k_0=0}{
        \left[
          \underbrace{
            \left(
              \underbrace{
                \sum^{r_1-1}_{k_1=0}x_{k_1r_2+k_0}\omega_{r_1}^{k_1j_0}
              }_{Section A} \right
            ) \omega_{r_1r_2}^{k_0j_1}
          }_{Section B}
        \right]
        \omega_{r_2}^{k_0j_1}
      }}_{Section C}
    \label{eq:FFTDefinitionLabeled}
\end{align}
Section A takes the form of a DFT of length $r_1$.
In vector form, the first element of the input for this DFT is located at index $k₀$, 
each subsequent input is then found taken by making a step of $r_2$, $r_1$ times.
In vector form this is a relatively complex input to reason upon, when we can 
instead consider our input in matrix form, initially, as a matrix of shape \AF{ι r₁ ⊗ ι r₂}.
In this form, Section A can be considered to apply the DFT to each column of the
input matrix.
Similar to Section A, Section C then takes the form of a DFT of length $r_2$.
In our \AF{ι r₁ ⊗ ι r₂} matrix form, this is equivalent to the application of 
the DFT over the rows of the result of section B.

Section B differs to section A and C, and applies what are generally referred to
as, the twiddle factors.
In matrix form this section is equivalent to a point wise multiplication 
over each element from Section A.
This step can be represented in Agda as \AF{zipWith \_*\_}, on a matrix containing 
these "twiddle factors".

%TC:ignore
\begin{code}[hide]
module FFT2 (real : Real) (cplx : Cplx real) where
  open import Matrix using (Ar; Shape; Position; _⊗_; ι; length; mapLeft; zipWith)
  open import Matrix.NonZero
  open import Matrix.Reshape using (_⟨_⟩; ♯; reshape; swap) renaming (recursive-transpose to _ᵗ)
  open import FFT real cplx using (iota) renaming (DFT′ to DFT)
  open import Data.Nat.Base using () renaming (_*_ to _*ₙ_)
  open Cplx cplx using (ℂ; _*_; -ω; e^i_; _+_; 0ℂ; +-*-isCommutativeRing)

  private
    variable
      s p : Shape
      r₁ r₂ : ℕ

  Ar∔ : Shape → Set → Set
  Ar∔ = Ar
\end{code}
%TC:endignore
\begin{code}
  2D-twiddles : Ar∔ (ι r₂ ⊗ ι r₁) ℂ
  2D-twiddles {r₁} {r₂} (k₀ ⊗ j₁) = -ω (r₂ *ₙ r₁) (iota k₀ *ₙ iota j₁ )
\end{code}
%TC:ignore
\begin{code}[hide]
      where
        postulate
          instance
            _ : NonZero (r₂ *ₙ r₁)
\end{code}
%TC:endignore

Using this twiddle matrix, the definition for the two dimensional FFT is generated
by forming each section into its own step.
Of note in the definition below are the three uses of swap.
The first swap allows DFT′ to map over the columns of the input array,
while the next inverts this and allows map to be performed over the rows.
The final swap is performed because, given an input in row major order, the 
result of the FFT is produced in column major order. 
For this to be represented correctly when flatten, \AF{♭}, is applied the output
tensor must be transposed, which can be performed for two dimensions with \AF{swap}.

\begin{code}
  2D-FFT : Ar∔ (ι r₁ ⊗ ι r₂) ℂ → Ar∔ ((ι r₁ ⊗ ι r₂) ᵗ) ℂ
  2D-FFT {r₁} {r₂} arr = 
      let 
          innerDFTapplied        = mapLeft (DFT {r₁}) (reshape swap arr)   
          twiddleFactorsApplied  = zipWith _*_   innerDFTapplied 2D-twiddles
          outerDFTapplied        = mapLeft (DFT {r₂}) (reshape swap twiddleFactorsApplied) 
      in  reshape swap outerDFTapplied
\end{code}
%TC:ignore
\begin{code}[hide]
      where
        postulate
          instance
            _ : NonZero r₁
            _ : NonZero r₂
            _ : NonZeroₛ (ι r₂ ⊗ ι r₁)
\end{code}
%TC:endignore

\begin{AgdaAlign}

Given knowledge that the DFT should be equivalent to the FFT, the two dimensional
definition can then be improved by instead applying the FFT at each step.
This requires the slight modification of the 2D-FFT implementation such that it 
accepts a tensor of any shape \AF{s} as input.

The definition for the twiddle factors must also be redefined, such that twiddles
can be computed for any shape with more than two dimensions.
It is easy to see, that the previous base of the roots of unity, $r₁\times r₂$,
maps directly to the \AF{length} of any given tensor.
To calculate the power of the root of unity, we can define \AF{offset-prod}.
This flattens the values of \AF{k} and \AF{j}, before multiplying them together to
calculate the power.
\begin{code}
  offset-prod : Position (s ⊗ p) → ℕ
  offset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)
   
  twiddles : Ar∔ (s ⊗ p) ℂ
  twiddles {s} {p} i = -ω (length (s ⊗ p)) (offset-prod i)
\end{code}
%TC:ignore
\begin{code}[hide]
      where
        postulate
          instance
            _ : NonZero (length s *ₙ length p)
\end{code}
%TC:endignore
\end{AgdaAlign}

The definition of this general twiddle matrix now allows for FFT to be defined
for an input of any shape.
The same problem of the output shape must then be dealt with again.
As the result of the FFT is in column major order, the result must be transposed
for flatten to represent it correctly.
This can be achieved through the application of \AF{swap} to \AF{outerDFTapplied}
before returning, as each sub tensor is the result of the application of the FFT and
will be transposed.

\begin{AgdaSuppressSpace}
\begin{code}
  FFT : Ar∔ s ℂ → Ar∔ (s ᵗ) ℂ
  FFT {ι N} arr = DFT arr
\end{code}
%TC:ignore
\begin{code}[hide]
    where
      postulate
        instance
          _ : NonZero N
\end{code}
%TC:endignore
\begin{code}
  FFT {r₁ ⊗ r₂} arr = 
      let 
          innerDFTapplied        = mapLeft FFT (reshape swap arr)   
          twiddleFactorsApplied  = zipWith _*_   innerDFTapplied twiddles
          outerDFTapplied        = mapLeft FFT (reshape swap twiddleFactorsApplied) 
      in  reshape swap outerDFTapplied
\end{code}
%TC:ignore
\begin{code}[hide]
      where
        postulate
          instance
            _ : NonZeroₛ r₁
            _ : NonZeroₛ r₂
            _ : NonZeroₛ (r₂ ⊗ (r₁ ᵗ))
\end{code}
%TC:endignore
\end{AgdaSuppressSpace}

As time was invested at the start of the project into a the creation of a language 
on tensors and reshaping, every case of the Cooley Tukey algorithm can be 
represented within the three lines shown above. 
Given a proof of correctness, this generality makes way for further experiments 
into different radix sizes, and combination of radix sizes, to be easily undertaken.

If this was instead written in \verb|C|, or a \verb|C| style language, this level
of generality would be almost impossible.
Any such general, \verb|C| style implementation would require many, low level,
index manipulations.
Without structures such as those defined for here for position, these index manipulations 
become increasingly complex as the radix sizes, and levels of nesting, increase.
This complexity makes it difficult to reason upon any such implementation meaning
garuntees are more challenging to achive.


% Spend some time explaining why expressing the FFT in the way we did is very good - Its a family of cooley tukey algorithms in 3 lines
% - The reason we can do this because we have invsted in these arrays and combinators on them
% - Doing this in C would be hell - we need to spoon feed this to the reader, this FFT definition is very cool!




