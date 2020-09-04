Martin Escardo and Alex Rice, 4th September 2020.

We define the initial binary system as a HIT, in cubical type theory,
and also in pure MLTT, and we show that, in cubical type theory, the
two definitions give equivalent types.

The motivation for this investigation is to know whether the initial
binary system is a set.

\begin{code}

{-# OPTIONS --safe --cubical #-}

module CubicalBinarySystem where

open import Cubical.Foundations.Prelude

\end{code}

The initial binary system as a HIT:

\begin{code}

data 𝔹 : Type₀ where
  L R : 𝔹
  l r : 𝔹 → 𝔹
  eqL : L   ≡ l L
  eqC : l R ≡ r L
  eqR : R   ≡ r R

\end{code}

And now the initial binary system defined in pure MLTT.

We first define an auxiliary data type D, where c is supposed to be
the common point in the images of l and r given by the identification
eqC:

\begin{code}

data D :  Type₀ where
 c : D
 l : D → D
 r : D → D

\end{code}

Then the initial binary system is defined in MLTT by adding left and
right endpoints to D, as 𝟙 + 𝟙 + D, where 𝟙 is the unit type:

\begin{code}

data 𝔹' : Type₀ where
 L : 𝔹'
 R : 𝔹'
 η : D → 𝔹'

\end{code}

Its center:

\begin{code}

C : 𝔹'
C = η c

\end{code}

We now define the left and right constructors l' and r' of 𝔹',
corresponding to the constructors l and r of 𝔹:

\begin{code}

l' : 𝔹' → 𝔹'
l' L     = L
l' R     = C
l' (η x) = η (l x)

r' : 𝔹' → 𝔹'
r' L     = C
r' R     = R
r' (η x) = η (r x)

\end{code}

As opposed to the HIT construction, the binary system equations hold
definitionally in our MLTT construction:

\begin{code}

eqL' : L    ≡ l' L
eqC' : l' R ≡ r' L
eqR' : R    ≡ r' R

eqL' = refl
eqC' = refl
eqR' = refl

\end{code}

Notice that C is the common point in the images of l' and r':

\begin{code}

eqC'l : l' R ≡ C
eqC'l = refl

eqC'r : C ≡ r' L
eqC'r = refl

\end{code}

The equivalence of the two constructions is given by the following
pair of mutually inverse maps ϕ and γ:

\begin{code}

ϕ : 𝔹 → 𝔹'
ϕ L       = L
ϕ R       = R
ϕ (l x)   = l' (ϕ x)
ϕ (r x)   = r' (ϕ x)
ϕ (eqL i) = L
ϕ (eqC i) = C
ϕ (eqR i) = R

γ : 𝔹' → 𝔹
γ L         = L
γ R         = R
γ (η c)     = l R
γ (η (l y)) = l (γ (η y))
γ (η (r y)) = r (γ (η y))

\end{code}

That ϕ is a left inverse of γ is easy, by induction on 𝔹':

\begin{code}

ϕγ : (y : 𝔹') → ϕ (γ y) ≡ y
ϕγ L     = refl
ϕγ R     = refl
ϕγ (η y) = δ y
 where
  δ : (y : D) → ϕ (γ (η y)) ≡ η y
  δ c     = refl
  δ (l y) = cong l' (δ y)
  δ (r y) = cong r' (δ y)

\end{code}

For the less trivial direction, we use that l' and r' correspond to l
and r as in the following two commutative squares:

\begin{code}

square-l : (y : 𝔹') → γ (l' y) ≡ l (γ y)
square-l L     = eqL
square-l R     = refl
square-l (η x) = refl

square-r : (y : 𝔹') → γ (r' y) ≡ r (γ y)
square-r L     = eqC
square-r R     = eqR
square-r (η x) = refl

\end{code}

Given this, the only difficulty of the following proof is in the case
for the path constructors eqL, eqC and eqR, for which hcomp is used:

\begin{code}

γϕ : (x : 𝔹) → γ (ϕ x) ≡ x
γϕ L         = refl
γϕ R         = refl
γϕ (l x)     = square-l (ϕ x) ∙ cong l (γϕ x)
γϕ (r x)     = square-r (ϕ x) ∙ cong r (γϕ x)
γϕ (eqL i) j = hcomp (λ k → λ { (i = i0) → L
                              ; (j = i0) → L
                              ; (j = i1) → eqL i }) (eqL (i ∧ j))
γϕ (eqC i) j = hcomp (λ k → λ { (j = i0) → l R
                              ; (j = i1) → eqC i }) (eqC (i ∧ j))
γϕ (eqR i) j = hcomp (λ k → λ { (i = i0) → R
                              ; (j = i0) → R
                              ; (j = i1) → eqR i }) (eqR (i ∧ j))

\end{code}

The following are immediate consequences of the above:

  * The type 𝔹' is easily seen to have decidable equality and hence is
    a set.

  * Being equivalent to 𝔹', the type 𝔹 also has decidable equality and
    so is a set too.

    (Technically, it is enough for these two conclusions that 𝔹 is a
    retract of 𝔹', which is the harder part γϕ of the invertibility
    condition).

  * So, in particular, the initial binary system is a set.

Given this, it is interesting to ask whether 𝔹' can be shown to have
the initiality property in MLTT (probably in the presence of
extensionality axioms), without invoking the cubical machinery.

Notice that a binary system homomorphism, in this ∞-setting, is a
function that commutes not only with L, R, l, r, but also with eqL,
eqC and eqR.
