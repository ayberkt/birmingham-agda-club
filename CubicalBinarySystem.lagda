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

We first define an auxiliary data type 𝔻, where c is supposed to be
the common point in the images of l and r given by the identification
eqC:

\begin{code}

data 𝔻 :  Type₀ where
 c : 𝔻
 l : 𝔻 → 𝔻
 r : 𝔻 → 𝔻

\end{code}

Then the initial binary system is defined in MLTT by adding left and
right endpoints to 𝔻, as 𝟙 + 𝟙 + 𝔻, where 𝟙 is the unit type:

\begin{code}

data 𝔹' : Type₀ where
 L : 𝔹'
 R : 𝔹'
 η : 𝔻 → 𝔹'

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

φ : 𝔹 → 𝔹'
φ L       = L
φ R       = R
φ (l x)   = l' (φ x)
φ (r x)   = r' (φ x)
φ (eqL i) = eqL' i -- Same as L.
φ (eqC i) = eqC' i -- Same as C.
φ (eqR i) = eqR' i -- Same as R.

γ : 𝔹' → 𝔹
γ L         = L
γ R         = R
γ (η c)     = l R
γ (η (l y)) = l (γ (η y))
γ (η (r y)) = r (γ (η y))

\end{code}

That φ is a left inverse of γ is easy, by induction on 𝔹':

\begin{code}

φγ : (y : 𝔹') → φ (γ y) ≡ y
φγ L     = refl
φγ R     = refl
φγ (η y) = δ y
 where
  δ : (y : 𝔻) → φ (γ (η y)) ≡ η y
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

path-construction : {ℓ : Level} {X : Type ℓ}
                    (x y : X)
                    (p : x ≡ y)
                  → (i : I) → x ≡ p i
path-construction x y p i j = hcomp (λ k → λ { (j = i0) → x
                                             ; (j = i1) → p i })
                                    (p (i ∧ j))

fixed-point-construction : {ℓ : Level} {X : Type ℓ}
                           (x : X)
                           (f : X → X)
                           (p : x ≡ f x)
                         → (i : I) → x ≡ p i
fixed-point-construction x f = path-construction x (f x)

\end{code}

For the purposes of definining γφ below, we need a different
construction of a point of the same type as fixed-point-construction,
that is, a different way to travel from x to p i:

\begin{code}

var-fixed-point-construction : {ℓ : Level} {X : Type ℓ}
                               (x : X)
                               (f : X → X)
                               (p : x ≡ f x)
                             → (i : I) → x ≡ p i
var-fixed-point-construction x f p i j = hcomp (λ k → λ { (i = i0) → x
                                                        ; (j = i0) → x
                                                        ; (j = i1) → p i })
                                               (p (i ∧ j))
\end{code}

These constructions are applied to obtain the following specific
paths, which in turn are used to construct γϕ below:

\begin{code}

eql : (i : I) → L   ≡ eqL i
eqc : (i : I) → l R ≡ eqC i
eqr : (i : I) → R   ≡ eqR i

eql = var-fixed-point-construction L l eqL
eqc = path-construction (l R) (r L) eqC
eqr = var-fixed-point-construction R r eqR

γφ : (x : 𝔹) → γ (φ x) ≡ x
γφ L       = refl
γφ R       = refl
γφ (l x)   = square-l (φ x) ∙ cong l (γφ x)
γφ (r x)   = square-r (φ x) ∙ cong r (γφ x)
γφ (eqL i) = eql i
γφ (eqC i) = eqc i
γφ (eqR i) = eqr i

\end{code}

The following are immediate consequences of the above:

  * The type 𝔹' is easily seen to have decidable equality and hence is
    a set.

  * Being equivalent to 𝔹', the type 𝔹 also has decidable equality and
    so is a set too.

    (Technically, it is enough for these two conclusions that 𝔹 is a
    retract of 𝔹', which is the harder part γφ of the invertibility
    condition.)

  * So, in particular, the initial binary system is a set.

Given this, it is interesting to ask whether 𝔹' can be shown to have
the initiality property in MLTT (probably in the presence of
extensionality axioms), without invoking the cubical machinery.

Notice that a binary system homomorphism, in this ∞-setting, is a
function that commutes not only with L, R, l, r, but also with eqL,
eqC and eqR.

We now consider recursion and then, more generally, induction.

\begin{code}

module _  {ℓ    : Level}
          {X    : Type ℓ}
          (x y  : X)
          (f g  : X → X)
          (eqf  : x ≡ f x)
          (eqfg : f y ≡ g x)
          (eqg  : y ≡ g y)
       where

 𝔹-rec : 𝔹 → X
 𝔹-rec L       = x
 𝔹-rec R       = y
 𝔹-rec (l b)   = f (𝔹-rec b)
 𝔹-rec (r b)   = g (𝔹-rec b)
 𝔹-rec (eqL i) = eqf i
 𝔹-rec (eqC i) = eqfg i
 𝔹-rec (eqR i) = eqg i

 𝔹'-rec : 𝔹' → X
 𝔹'-rec L = x
 𝔹'-rec R = y
 𝔹'-rec (η c) = f y -- Or g x, but then we need to adapt the definitions below.
 𝔹'-rec (η (l x)) = f (𝔹'-rec (η x))
 𝔹'-rec (η (r x)) = g (𝔹'-rec (η x))

\end{code}

The desired equations for 𝔹'-rec hold, but not definitionally:

\begin{code}

 𝔹'-rec-l : (x : 𝔹') → 𝔹'-rec (l' x) ≡ f (𝔹'-rec x)
 𝔹'-rec-r : (x : 𝔹') → 𝔹'-rec (r' x) ≡ g (𝔹'-rec x)

 𝔹'-rec-L : ∀ i → 𝔹'-rec (eqL' i) ≡ eqf i
 𝔹'-rec-C : ∀ i → 𝔹'-rec (eqC' i) ≡ eqfg i
 𝔹'-rec-R : ∀ i → 𝔹'-rec (eqR' i) ≡ eqg i

 𝔹'-rec-l L     = eqf
 𝔹'-rec-l R     = refl
 𝔹'-rec-l (η x) = refl

 𝔹'-rec-r L     = eqfg
 𝔹'-rec-r R     = eqg
 𝔹'-rec-r (η x) = refl

 𝔹'-rec-L = var-fixed-point-construction x f eqf
 𝔹'-rec-C = path-construction (f y) (g x) eqfg
 𝔹'-rec-R = var-fixed-point-construction y g eqg

\end{code}

Induction:

\begin{code}

module _ {ℓ    : Level}
         (P    : 𝔹 → Type ℓ)
         (x    : P L)
         (y    : P R)
         (f    : (b : 𝔹) → P b → P (l b))
         (g    : (b : 𝔹) → P b → P (r b))
         (eqf  : subst P eqL x       ≡ f L x) -- Not sure if this is the most
         (eqfg : subst P eqC (f R y) ≡ g L x) -- suitable cubical formulation.
         (eqg  : subst P eqR y       ≡ g R y) --
       where

 𝔹-ind : (b : 𝔹) → P b
 𝔹-ind L = x
 𝔹-ind R = y
 𝔹-ind (l b) = f b (𝔹-ind b)
 𝔹-ind (r b) = g b (𝔹-ind b)
 𝔹-ind (eqL i) = {!!}
 𝔹-ind (eqC i) = {!!}
 𝔹-ind (eqR i) = {!!}

\end{code}

Induction for the MLTT construction of the initial binary system:

\begin{code}

module _ {ℓ    : Level}
         (P    : 𝔹' → Type ℓ)
         (x    : P L)
         (y    : P R)
         (f    : (b : 𝔹') → P b → P (l' b))
         (g    : (b : 𝔹') → P b → P (r' b))
         (eqf  : x ≡ f L x)       -- This is possible only because
         (eqfg : f R y ≡ g L x)   -- the equations L ≡ l' L and r' L ≡ l' R
         (eqg  : y ≡ g R y)       -- and R ≡ r' R hold definitionally.
       where

 𝔹'-ind : (b : 𝔹') → P b
 𝔹'-ind L = x
 𝔹'-ind R = y
 𝔹'-ind (η c) = f R y
 𝔹'-ind (η (l x)) = f (η x) (𝔹'-ind (η x))
 𝔹'-ind (η (r x)) = g (η x) (𝔹'-ind (η x))

 𝔹'-ind-l : (x : 𝔹') → 𝔹'-ind (l' x) ≡ f x (𝔹'-ind x)
 𝔹'-ind-r : (x : 𝔹') → 𝔹'-ind (r' x) ≡ g x (𝔹'-ind x)

 𝔹'-ind-L : ∀ i → 𝔹'-ind (eqL' i) ≡ eqf i
 𝔹'-ind-C : ∀ i → 𝔹'-ind (eqC' i) ≡ eqfg i
 𝔹'-ind-R : ∀ i → 𝔹'-ind (eqR' i) ≡ eqg i

 𝔹'-ind-l L     = eqf
 𝔹'-ind-l R     = refl
 𝔹'-ind-l (η x) = refl

 𝔹'-ind-r L     = eqfg
 𝔹'-ind-r R     = eqg
 𝔹'-ind-r (η x) = refl

 𝔹'-ind-L = var-fixed-point-construction x (f L) eqf
 𝔹'-ind-C = path-construction (f R y) (g L x) eqfg
 𝔹'-ind-R = var-fixed-point-construction y (g R) eqg

\end{code}
