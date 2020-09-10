Martin Escardo and Alex Rice, 4th September 2020.

Produced in the Birmingham Agda Club. We benefited from the company
and discussions with the other members, Todd Ambridge, Tom De Jong,
George Kaye, Owen Milner and Ayberk Tosun.

See the file https://www.cs.bham.ac.uk/~mhe/TypeTopology/InitialBinarySystem.html
for background.

The initial binary system gives the closed interval of dyadic
rationals, and also gives the free midpoint algebra over two
generators (this second point still needs to be coded in Agda).

We define the initial binary system as a HIT, in cubical type theory,
and also in pure MLTT, and we show that, in cubical type theory, the
two definitions give equivalent types.

The main motivation for the investigation in this file is to know
whether the initial binary system is a set, as in𝔹-prop ? ? ? ? ? ?which is
indeed the case, as shown below, using the equivalence of the cubical
and MLTT definitions of the initial binary system.

\begin{code}

{-# OPTIONS --safe --cubical #-}

module CubicalBinarySystem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to *)
open import Cubical.Foundations.GroupoidLaws

\end{code}

Our preamble:

\begin{code}

variable
 ℓ ℓ' ℓ₀ ℓ₁ ℓ₂ : Level

id : {X : Type ℓ} → X → X
id = idfun _

Sigma : (X : Type ℓ) (A : X → Type ℓ') → Type (ℓ-max ℓ ℓ')
Sigma = Σ

syntax Sigma X (λ x → a) = Σ x ꞉ X , a
infixr -1 Sigma


_∼_ : {X : Type ℓ} {A : X → Type ℓ'}
    → ((x : X) → A x)
    → ((x : X) → A x)
    → Type (ℓ-max ℓ ℓ')
f ∼ g = ∀ x → f x ≡ g x

infix  4  _∼_

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

We first define an auxiliary data type 𝔻, where center is supposed to
be the common point in the images of l and r given by the
identification eqC:

\begin{code}

data 𝔻 :  Type₀ where
 center : 𝔻
 left   : 𝔻 → 𝔻
 right  : 𝔻 → 𝔻

\end{code}

Then the initial binary system is defined in MLTT by adding left and
right endpoints to 𝔻, as 𝟙 + 𝟙 + 𝔻, where 𝟙 is the unit type:

\begin{code}

data 𝔹' : Type₀ where
 L' : 𝔹'
 R' : 𝔹'
 η  : 𝔻 → 𝔹'

\end{code}

We now define the left and right constructors l' and r' of 𝔹',
corresponding to the constructors l and r of 𝔹:

\begin{code}

l' : 𝔹' → 𝔹'
l' L'    = L'
l' R'    = η center
l' (η x) = η (left x)

r' : 𝔹' → 𝔹'
r' L'    = η center
r' R'    = R'
r' (η x) = η (right x)

\end{code}

As opposed to the HIT construction, the binary system equations hold
definitionally in our MLTT construction (but then other things that
hold definitionally for the cubical HIT only hold up to a path in the
MLTT construction):

\begin{code}

eqL' : L'    ≡ l' L'
eqC' : l' R' ≡ r' L'
eqR' : R'    ≡ r' R'

eqL' = refl
eqC' = refl
eqR' = refl

\end{code}

We also have:

\begin{code}

eql' : (i : I) → L'    ≡ eqL' i
eqc' : (i : I) → l' R' ≡ eqC' i
eqr' : (i : I) → R'    ≡ eqR' i

eql' i = refl
eqc' i = refl
eqr' i = refl

\end{code}

Notice that, by construction, the common point in the images of the
functions l' and r' is η center.

The equivalence of the two constructions is given by the following
pair of mutually inverse maps φ and γ:

\begin{code}

φ : 𝔹 → 𝔹'
φ L       = L'
φ R       = R'
φ (l x)   = l' (φ x)
φ (r x)   = r' (φ x)
φ (eqL i) = eqL' i
φ (eqC i) = eqC' i
φ (eqR i) = eqR' i

γ : 𝔹' → 𝔹
γ L'            = L
γ R'            = R
γ (η center)    = l R
γ (η (left y))  = l (γ (η y))
γ (η (right y)) = r (γ (η y))

\end{code}

That φ is a left inverse of γ is easy, by induction on 𝔹' and 𝔻:

\begin{code}

φγ : (y : 𝔹') → φ (γ y) ≡ y
φγ L'    = refl
φγ R'    = refl
φγ (η y) = δ y
 where
  δ : (y : 𝔻) → φ (γ (η y)) ≡ η y
  δ center    = refl
  δ (left y)  = cong l' (δ y)
  δ (right y) = cong r' (δ y)

\end{code}

For the less trivial direction, we use that l' and r' correspond to l
and r as in the following two commutative squares:

\begin{code}

square-l : (y : 𝔹') → γ (l' y) ≡ l (γ y)
square-l L'    = eqL
square-l R'    = refl
square-l (η x) = refl

square-r : (y : 𝔹') → γ (r' y) ≡ r (γ y)
square-r L'    = eqC
square-r R'    = eqR
square-r (η x) = refl

\end{code}

Given this, the only difficulty of the following proof is in the case
for the path constructors eqL, eqC and eqR, for which hcomp is used:

\begin{code}

path-construction : {X : Type ℓ}
                    (x y : X)
                    (p : x ≡ y)
                  → PathP (λ i → x ≡ p i) (refl ∙ refl) (p ∙ refl)
path-construction x y p i j = hcomp (λ k → λ { (j = i0) → x
                                             ; (j = i1) → p i })
                                    (p (i ∧ j))

fixed-point-construction : {X : Type ℓ}
                           (x : X)
                           (f : X → X)
                           (p : x ≡ f x)
                         → PathP (λ i → x ≡ p i) refl (p ∙ refl)
fixed-point-construction x f p i j = hcomp (λ k → λ { (i = i0) → x
                                                    ; (j = i0) → x
                                                    ; (j = i1) → p i })
                                           (p (i ∧ j))
\end{code}

These constructions are applied to obtain the following specific
paths, which in turn are used to construct γϕ below:

\begin{code}

eql : PathP (λ i → L   ≡ eqL i) refl          (eqL ∙ refl)
eqc : PathP (λ i → l R ≡ eqC i) (refl ∙ refl) (eqC ∙ refl)
eqr : PathP (λ i → R   ≡ eqR i) refl          (eqR ∙ refl)

eql = fixed-point-construction L l eqL
eqc = path-construction (l R) (r L) eqC
eqr = fixed-point-construction R r eqR

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

We now prove that 𝔹 is a set as explained above.

\begin{code}

private
 cancellr : 𝔻 → 𝔻
 cancellr center    = center -- arbitrary choice
 cancellr (left x)  = x
 cancellr (right x) = x

 cancelη : 𝔹' → 𝔻
 cancelη L'    = center -- arbitrary choice
 cancelη R'    = center -- arbitrary choice
 cancelη (η x) = x

left-lc : {x y : 𝔻} → left x ≡ left y → x ≡ y
left-lc = cong cancellr

right-lc : {x y : 𝔻} → right x ≡ right y → x ≡ y
right-lc = cong cancellr

isLeft : 𝔻 → Type₀
isLeft center    = 𝟘
isLeft (left x)  = 𝟙
isLeft (right x) = 𝟘

isCenter : 𝔻 → Type₀
isCenter center    = 𝟙
isCenter (left x)  = 𝟘
isCenter (right x) = 𝟘

left-is-not-right : {x y : 𝔻} → ¬ left x ≡ right y
left-is-not-right p = transport (cong isLeft p) *

center-is-not-left : {x : 𝔻} → ¬ center ≡ left x
center-is-not-left p = transport (cong isCenter p) *

center-is-not-right : {x : 𝔻} → ¬ center ≡ right x
center-is-not-right p = transport (cong isCenter p) *

𝔻-is-discrete : Discrete 𝔻
𝔻-is-discrete center    center    = yes refl
𝔻-is-discrete center    (left y)  = no center-is-not-left
𝔻-is-discrete center    (right y) = no center-is-not-right
𝔻-is-discrete (left x)  center    = no (center-is-not-left ∘ sym)
𝔻-is-discrete (left x)  (left y)  = mapDec (cong left) (λ ν p → ν (left-lc p)) (𝔻-is-discrete x y)
𝔻-is-discrete (left x)  (right y) = no left-is-not-right
𝔻-is-discrete (right x) center    = no (center-is-not-right ∘ sym)
𝔻-is-discrete (right x) (left y)  = no (left-is-not-right ∘ sym)
𝔻-is-discrete (right x) (right y) = mapDec (cong right) (λ ν p → ν (right-lc p)) (𝔻-is-discrete x y)

η-lc : {x y : 𝔻} → η x ≡ η y → x ≡ y
η-lc = cong cancelη

is-L' : 𝔹' → Type₀
is-L' L'    = 𝟙
is-L' R'    = 𝟘
is-L' (η x) = 𝟘

is-η : 𝔹' → Type₀
is-η L'    = 𝟘
is-η R'    = 𝟘
is-η (η x) = 𝟙

L'-is-not-R' : ¬ L' ≡ R'
L'-is-not-R' p = transport (cong is-L' p) *

L'-is-not-η : {x : 𝔻} → ¬ L' ≡ η x
L'-is-not-η p = transport (cong is-L' p) *

η-is-not-R' : {x : 𝔻} → ¬ η x ≡ R'
η-is-not-R' p = transport (cong is-η p) *

𝔹'-is-discrete : Discrete 𝔹'
𝔹'-is-discrete L'    L'    = yes refl
𝔹'-is-discrete L'    R'    = no L'-is-not-R'
𝔹'-is-discrete L'    (η x) = no L'-is-not-η
𝔹'-is-discrete R'    L'    = no (L'-is-not-R' ∘ sym)
𝔹'-is-discrete R'    R'    = yes refl
𝔹'-is-discrete R'    (η x) = no (η-is-not-R' ∘ sym)
𝔹'-is-discrete (η x) L'    = no (L'-is-not-η ∘ sym)
𝔹'-is-discrete (η x) R'    = no η-is-not-R'
𝔹'-is-discrete (η x) (η y) = mapDec (cong η) (λ ν p → ν (η-lc p)) (𝔻-is-discrete x y)

𝔹'-is-set : isSet 𝔹'
𝔹'-is-set = Discrete→isSet 𝔹'-is-discrete

𝔹'-is-equiv-to-𝔹 : 𝔹' ≃ 𝔹
𝔹'-is-equiv-to-𝔹 = isoToEquiv (iso γ φ γφ φγ)

𝔹-is-set : isSet 𝔹
𝔹-is-set = isOfHLevelRespectEquiv 2 𝔹'-is-equiv-to-𝔹 𝔹'-is-set

\end{code}

We now consider recursion and then, more generally, induction.  For
both conceptual and practical reasons, we consider various forms of
induction.

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
 𝔹'-rec L'            = x
 𝔹'-rec R'            = y
 𝔹'-rec (η center)    = f y -- Or g x, but then we need to adapt the definitions below.
 𝔹'-rec (η (left x))  = f (𝔹'-rec (η x))
 𝔹'-rec (η (right x)) = g (𝔹'-rec (η x))

\end{code}

The desired equations for 𝔹'-rec hold, but not definitionally:

\begin{code}

 𝔹'-rec-l : (x : 𝔹') → 𝔹'-rec (l' x) ≡ f (𝔹'-rec x)
 𝔹'-rec-r : (x : 𝔹') → 𝔹'-rec (r' x) ≡ g (𝔹'-rec x)

 𝔹'-rec-L : ∀ i → 𝔹'-rec (eqL' i) ≡ eqf i
 𝔹'-rec-C : ∀ i → 𝔹'-rec (eqC' i) ≡ eqfg i
 𝔹'-rec-R : ∀ i → 𝔹'-rec (eqR' i) ≡ eqg i

 𝔹'-rec-l L'    = eqf
 𝔹'-rec-l R'    = refl
 𝔹'-rec-l (η x) = refl

 𝔹'-rec-r L'    = eqfg
 𝔹'-rec-r R'    = eqg
 𝔹'-rec-r (η x) = refl

 𝔹'-rec-L i = fixed-point-construction x f eqf i
 𝔹'-rec-C i = path-construction (f y) (g x) eqfg i
 𝔹'-rec-R i = fixed-point-construction y g eqg i

\end{code}

Induction:

\begin{code}

module _ {ℓ    : Level}
         (P    : 𝔹 → Type ℓ)
         (x    : P L)
         (y    : P R)
         (f    : (b : 𝔹) → P b → P (l b))
         (g    : (b : 𝔹) → P b → P (r b))
         (eqf  : PathP (λ i → P (eqL i)) x (f L x))        -- Cubical-style
         (eqfg : PathP (λ i → P (eqC i)) (f R y) (g L x))  -- formulation.
         (eqg  : PathP (λ i → P (eqR i)) y (g R y))        --
       where

 𝔹-ind : (b : 𝔹) → P b
 𝔹-ind L       = x
 𝔹-ind R       = y
 𝔹-ind (l b)   = f b (𝔹-ind b)
 𝔹-ind (r b)   = g b (𝔹-ind b)
 𝔹-ind (eqL i) = eqf i
 𝔹-ind (eqC i) = eqfg i
 𝔹-ind (eqR i) = eqg i

module _ {ℓ    : Level}
         (P    : 𝔹 → Type ℓ)
         (x    : P L)
         (y    : P R)
         (f    : (b : 𝔹) → P b → P (l b))
         (g    : (b : 𝔹) → P b → P (r b))
         (eqf  : subst P eqL x       ≡ f L x) -- HoTT/UF style
         (eqfg : subst P eqC (f R y) ≡ g L x) -- fomulation.
         (eqg  : subst P eqR y       ≡ g R y) --
       where

 𝔹-ind' : (b : 𝔹) → P b
 𝔹-ind' = 𝔹-ind P x y f g (λ i → toPathP {A = λ j → P (eqL j)} eqf i)
                           (λ i → toPathP {A = λ j → P (eqC j)} eqfg i)
                           (λ i → toPathP {A = λ j → P (eqR j)} eqg i)

\end{code}

If P is proposition valued, then the compatibility conditions hold
automatically and hence don't need to be supplied:

\begin{code}

module _ {ℓ  : Level}
         (P : 𝔹 → Type ℓ)
         (p : (x : 𝔹) → isProp (P x))
         (x : P L)
         (y : P R)
         (f : (b : 𝔹) → P b → P (l b))
         (g : (b : 𝔹) → P b → P (r b))
       where

 𝔹-ind-prop : (b : 𝔹) → P b
 𝔹-ind-prop = 𝔹-ind' P x y f g (p (l L) (subst P eqL x) (f L x))
                                (p (r L) (subst P eqC (f R y)) (g L x))
                                (p (r R) (subst P eqR y) (g R y))

module _ (f g : 𝔹 → 𝔹)
         (p : f L ≡ g L)
         (q : f R ≡ g R)
         (u : (b : 𝔹) → f b ≡ g b → f (l b) ≡ g (l b))
         (v : (b : 𝔹) → f b ≡ g b → f (r b) ≡ g (r b))
       where

 𝔹-ind-eq : (b : 𝔹) → f b ≡ g b
 𝔹-ind-eq = 𝔹-ind-prop (λ b → f b ≡ g b)
                        (λ b → 𝔹-is-set (f b) (g b))
                        p q u v

module _ {ℓ  : Level}
         (P : 𝔹 → Type ℓ)
         (p : (x : 𝔹) → isProp (P x))
         (f : (b : 𝔹) → P (l b))
         (g : (b : 𝔹) → P (r b))
       where

 𝔹-cases : (b : 𝔹) → P b
 𝔹-cases = 𝔹-ind-prop P p (subst P (sym eqL) (f L))
                           (subst P (sym eqR) (g R))
                           (λ b _ → f b)
                           (λ b _ → g b)

module _ (f g : 𝔹 → 𝔹)
         (u : (b : 𝔹) → f (l b) ≡ g (l b))
         (v : (b : 𝔹) → f (r b) ≡ g (r b))
       where

 𝔹-cases-eq : (b : 𝔹) → f b ≡ g b
 𝔹-cases-eq = 𝔹-cases (λ b → f b ≡ g b) (λ b → 𝔹-is-set (f b) (g b)) u v

module _ (f g : 𝔹 → 𝔹 → 𝔹)
         (ll : (b c : 𝔹) → f (l b) (l c) ≡ g (l b) (l c))
         (lr : (b c : 𝔹) → f (l b) (r c) ≡ g (l b) (r c))
         (rl : (b c : 𝔹) → f (r b) (l c) ≡ g (r b) (l c))
         (rr : (b c : 𝔹) → f (r b) (r c) ≡ g (r b) (r c))
       where

 𝔹-cases-eq₂ : (b c : 𝔹) → f b c ≡ g b c
 𝔹-cases-eq₂ = 𝔹-cases (λ b → ∀ c → f b c ≡ g b c)
                        (λ b → isPropΠ (λ x → 𝔹-is-set _ _))
                        (λ b → 𝔹-cases-eq (f (l b)) (g (l b)) (ll b) (lr b))
                        (λ b → 𝔹-cases-eq (f (r b)) (g (r b)) (rl b) (rr b))

\end{code}

Induction for the MLTT construction of the initial binary system:

\begin{code}

module _ {ℓ    : Level}
         (P    : 𝔹' → Type ℓ)
         (x    : P L')
         (y    : P R')
         (f    : (b : 𝔹') → P b → P (l' b))
         (g    : (b : 𝔹') → P b → P (r' b))
         (eqf  : x ≡ f L' x)      -- This is possible only because
         (eqfg : f R' y ≡ g L' x) -- the equations L' ≡ l' L' and l' R' ≡ r' L'
         (eqg  : y ≡ g R' y)      -- and R' ≡ r' R' hold definitionally.
       where

 𝔹'-ind : (b : 𝔹') → P b
 𝔹'-ind L'            = x
 𝔹'-ind R'            = y
 𝔹'-ind (η center)    = f R' y
 𝔹'-ind (η (left x))  = f (η x) (𝔹'-ind (η x))
 𝔹'-ind (η (right x)) = g (η x) (𝔹'-ind (η x))

\end{code}

This satisfies the following equations, but not definitionally:

\begin{code}

 𝔹'-ind-l : (b : 𝔹') → 𝔹'-ind (l' b) ≡ f b (𝔹'-ind b)
 𝔹'-ind-r : (b : 𝔹') → 𝔹'-ind (r' b) ≡ g b (𝔹'-ind b)

 𝔹'-ind-L : ∀ i → 𝔹'-ind (eqL' i) ≡ eqf i
 𝔹'-ind-C : ∀ i → 𝔹'-ind (eqC' i) ≡ eqfg i
 𝔹'-ind-R : ∀ i → 𝔹'-ind (eqR' i) ≡ eqg i

\end{code}

With the following proofs:

\begin{code}

 𝔹'-ind-l L'    = eqf
 𝔹'-ind-l R'    = refl
 𝔹'-ind-l (η x) = refl

 𝔹'-ind-r L'    = eqfg
 𝔹'-ind-r R'    = eqg
 𝔹'-ind-r (η x) = refl

 𝔹'-ind-L i = fixed-point-construction x (f L') eqf i
 𝔹'-ind-C i = path-construction (f R' y) (g L' x) eqfg i
 𝔹'-ind-R i = fixed-point-construction y (g R') eqg i

\end{code}

For definition by cases, we get a simplification of the compatibility
condition:

\begin{code}

compatible : {X : Type ℓ} (f g : 𝔹 → X) → Type ℓ
compatible f g = f R ≡ g L

cases : {X : Type ℓ} (f g : 𝔹 → X) → compatible f g → (𝔹 → X)
cases f g p L       = f L
cases f g p R       = g R
cases f g p (l b)   = f b
cases f g p (r b)   = g b
cases f g p (eqL i) = f L
cases f g p (eqC i) = p i
cases f g p (eqR i) = g R

\end{code}

NB. The function cases is a particular case of 𝔹-ind:

\begin{code}

NB-cases : {X : Type ℓ} (f g : 𝔹 → X) (p : compatible f g)
         → cases f g p ∼ 𝔹-ind (λ _ → X) (f L) (g R) (λ b _ → f b) (λ b _ → g b) (λ _ → f L) p (λ _ → g R)
NB-cases f g p L       = refl
NB-cases f g p R       = refl
NB-cases f g p (l b)   = refl
NB-cases f g p (r b)   = refl
NB-cases f g p (eqL i) = λ _ → f L
NB-cases f g p (eqC i) = λ _ → p i
NB-cases f g p (eqR i) = λ _ → g R

\end{code}

Uniqueness of functions defined by cases.

Preparation for that:

\begin{code}

path-lemma : {X : Type ℓ}
             (h : 𝔹 → X)
             {x y : 𝔹}
             {a : X}
             (p : x ≡ y)
             (q : h y ≡ a)
           → PathP (λ i → h (p i) ≡ a) (cong h p ∙ q) q
path-lemma h p q i j = hcomp (λ k → λ { (i = i1) → q (j ∧ k)
                                      ; (j = i0) → h (p i)
                                      ; (j = i1) → q k })
                             (h (p (i ∨ j)))

compatible-higher : {X : Type ℓ}
                    (f g : 𝔹 → X)
                    (p : compatible f g)
                    (h : 𝔹 → X)
                    (u : h ∘ l ∼ f)
                    (v : h ∘ r ∼ g)
                  → Type ℓ
compatible-higher f g p h u v = Square (u R) (v L) (cong h eqC) p

\end{code}

We first consider an ∞-version:

\begin{code}

cases-uniqueness : {X : Type ℓ}
                   (f g : 𝔹 → X)
                   (p : compatible f g)
                   (h : 𝔹 → X)
                   (u : h ∘ l ∼ f)
                   (v : h ∘ r ∼ g)
                 → compatible-higher f g p h u v
                 → h ∼ cases f g p
cases-uniqueness f g p h u v c L       = cong h eqL ∙ u L
cases-uniqueness f g p h u v c R       = cong h eqR ∙ v R
cases-uniqueness f g p h u v c (l x)   = u x
cases-uniqueness f g p h u v c (r x)   = v x
cases-uniqueness f g p h u v c (eqL i) = path-lemma h eqL (u L) i
cases-uniqueness f g p h u v c (eqC i) = c i
cases-uniqueness f g p h u v c (eqR i) = path-lemma h eqR (v R) i

\end{code}

When X is a set, the higher compatibility condition holds
automatically and hence doesn't need to be supplied:

\begin{code}

cases-uniqueness-set : {X : Type ℓ}
                       (f g : 𝔹 → X)
                       (p : compatible f g)
                       (h : 𝔹 → X)
                       (u : h ∘ l ∼ f)
                       (v : h ∘ r ∼ g)
                     → isSet X
                     → h ∼ cases f g p
cases-uniqueness-set f g p h u v isSetX = cases-uniqueness f g p h u v c
  where
   c : Square (u R) (v L) (λ i → h (eqC i)) p
   c = isSet→isSet' isSetX (u R) (v L) (cong h eqC) p

\end{code}

We now prove some fundamental properties of 𝔹.

\begin{code}

mirror : 𝔹 → 𝔹
mirror = 𝔹-rec R L r l eqR (sym eqC) eqL

mirror-involutive : (x : 𝔹) → mirror (mirror x) ≡ x
mirror-involutive = 𝔹-ind-eq (mirror ∘ mirror) id
                       refl
                       refl
                       (λ x → cong l)
                       (λ y → cong r)

linv : 𝔹 → 𝔹
linv = cases id (λ _ → R) refl

linv-defining-equations :
     (linv L   ≡ L)
   × (linv R   ≡ R)
   × (linv ∘ l ≡ id )
   × (linv ∘ r ≡ λ _ → R)
linv-defining-equations = refl , refl , refl , refl

rinv : 𝔹 → 𝔹
rinv = cases (λ _ → L) id refl

rinv-defining-equations :
     (rinv L   ≡ L)
   × (rinv R   ≡ R)
   × (rinv ∘ l ≡ λ _ → L)
   × (rinv ∘ r ≡ id)
rinv-defining-equations = refl , refl , refl , refl

l-lc : {x y : 𝔹} → l x ≡ l y → x ≡ y
l-lc = cong linv

r-lc : {x y : 𝔹} → r x ≡ r y → x ≡ y
r-lc = cong rinv

M : 𝔹
M = l R

the-only-point-mapped-to-M-by-l-is-R : {x : 𝔹} → l x ≡ M → x ≡ R
the-only-point-mapped-to-M-by-l-is-R = l-lc

the-only-point-mapped-to-M-by-r-is-L : {x : 𝔹} → r x ≡ M → x ≡ L
the-only-point-mapped-to-M-by-r-is-L p = r-lc (p ∙ eqC)

lr-common-image : {x y : 𝔹} → l x ≡ r y → (x ≡ R) × (y ≡ L)
lr-common-image p = cong linv p , cong rinv (sym p)

the-only-fixed-point-of-l-is-L : (x : 𝔹) → l x ≡ x → x ≡ L
the-only-fixed-point-of-l-is-L = 𝔹-ind-prop
                                   (λ x → l x ≡ x → x ≡ L )
                                   (λ x → isPropΠ (λ _ → 𝔹-is-set _ _))
                                   a b f g
 where
  a : l L ≡ L → L ≡ L
  a _ = refl

  b : l R ≡ R → R ≡ L
  b p = snd s
   where
    q : l R ≡ r R
    q = p ∙ eqR
    s : (R ≡ R) × (R ≡ L)
    s = lr-common-image q

  f : (x : 𝔹) → (l x ≡ x → x ≡ L) → l (l x) ≡ l x → l x ≡ L
  f x ϕ p = cong l s ∙ sym eqL
   where
    q : l x ≡ x
    q = l-lc p
    s : x ≡ L
    s = ϕ q

  g : (x : 𝔹) → (l x ≡ x → x ≡ L) → l (r x) ≡ r x → r x ≡ L
  g x _ p = r x ≡⟨ fst q ⟩
            R   ≡⟨ s ⟩
            x   ≡⟨ snd q ⟩
            L   ∎
   where
    q : (r x ≡ R) × (x ≡ L)
    q = lr-common-image p
    s : R ≡ x
    s = sym (r-lc (fst q ∙ eqR))


the-only-fixed-point-of-r-is-R : (x : 𝔹) → r x ≡ x → x ≡ R
the-only-fixed-point-of-r-is-R x p = sym (mirror-involutive x) ∙ t
 where
  q : l (mirror x) ≡ mirror x
  q = cong mirror p

  s : mirror x ≡ L
  s = the-only-fixed-point-of-l-is-L (mirror x) q

  t : mirror (mirror x) ≡ R
  t = cong mirror s

is-L : 𝔹 → Type₀
is-L = 𝔹-rec 𝟙 𝟘 id (λ X → 𝟘) refl refl refl

is-L-defining-equations :
     (is-L   L ≡ 𝟙)
   × (is-L   R ≡ 𝟘)
   × (is-L ∘ l ≡ is-L)
   × (is-L ∘ r ≡ λ _ → 𝟘)
is-L-defining-equations = refl , refl , refl , refl

L-is-not-R : ¬ L ≡ R
L-is-not-R p = transport (cong is-L p) *

is-R : 𝔹 → Type₀
is-R = 𝔹-rec 𝟘 𝟙 (λ X → 𝟘) id refl refl refl

is-R-defining-equations :
     (is-R   L ≡ 𝟘)
   × (is-R   R ≡ 𝟙)
   × (is-R ∘ l ≡ λ _ → 𝟘)
   × (is-R ∘ r ≡ is-R)
is-R-defining-equations = refl , refl , refl , refl

\end{code}

Preparation for the definition of the midpoint operation _⊕_.

The idea is to endow a subtype F of the function type 𝔹 → 𝔹 with a
binary-system structure (𝐿 , 𝑅 , 𝑙 , 𝑟 , eq𝐿 , eq𝐶 , eq𝑅) so that we
get, by recursion, a function 𝔹 → F, and, hence, by projection, a
function _⊕_ : 𝔹 → 𝔹 → B, which is our desired midpoint operation.

\begin{code}

m-compatibility : l (r R) ≡ r (l L)
m-compatibility = cong l (sym eqR) ∙∙ eqC ∙∙ cong r eqL

m : 𝔹 → 𝔹
m = cases (l ∘ r) (r ∘ l) m-compatibility

m-defining-equations : (m L   ≡ l (r L))
                     × (m R   ≡ r (l R))
                     × (m ∘ l ≡ l ∘ r)
                     × (m ∘ r ≡ r ∘ l)
m-defining-equations = refl , refl , refl , refl

l-by-cases : l ∼ cases (l ∘ l) (m ∘ l) (cong l eqC)
l-by-cases = cases-uniqueness (l ∘ l) (m ∘ l) (cong l eqC) l (λ x → refl) (λ x → refl) (λ i → refl)

r-by-cases : r ∼ cases (m ∘ r) (r ∘ r) (cong r eqC)
r-by-cases = cases-uniqueness (r ∘ l) (r ∘ r) (cong r eqC) r (λ x → refl) (λ x → refl) (λ i → refl)

is-𝓛-function : (𝔹 → 𝔹) → Type₀
is-𝓛-function f = compatible (l ∘ f) (m ∘ f)

is-𝓡-function : (𝔹 → 𝔹) → Type₀
is-𝓡-function f = compatible (m ∘ f) (r ∘ f)

𝓛 : (f : 𝔹 → 𝔹) → is-𝓛-function f → (𝔹 → 𝔹)
𝓛 f = cases (l ∘ f) (m ∘ f)

𝓡 : (f : 𝔹 → 𝔹) → is-𝓡-function f → (𝔹 → 𝔹)
𝓡 f = cases (m ∘ f) (r ∘ f)

preservation-𝓛𝓛 : (f : 𝔹 → 𝔹) (a : is-𝓛-function f) (b : is-𝓡-function f) → is-𝓛-function (𝓛 f a)
preservation-𝓛𝓛 f a b = cong l b

preservation-𝓛𝓡 : (f : 𝔹 → 𝔹) (a : is-𝓛-function f) (b : is-𝓡-function f) → is-𝓡-function (𝓛 f a)
preservation-𝓛𝓡 f a b = cong m b

preservation-𝓡𝓛 : (f : 𝔹 → 𝔹) (a : is-𝓛-function f) (b : is-𝓡-function f) → is-𝓛-function (𝓡 f b)
preservation-𝓡𝓛 f a b = cong m a

preservation-𝓡𝓡 : (f : 𝔹 → 𝔹) (a : is-𝓛-function f) (b : is-𝓡-function f) → is-𝓡-function (𝓡 f b)
preservation-𝓡𝓡 f a b = cong r a

is-𝓛𝓡-function : (𝔹 → 𝔹) → Type₀
is-𝓛𝓡-function f = is-𝓛-function f × is-𝓡-function f

being-𝓛𝓡-function-is-prop : (f : 𝔹 → 𝔹) → isProp (is-𝓛𝓡-function f)
being-𝓛𝓡-function-is-prop f = isProp× (𝔹-is-set _ _) (𝔹-is-set _ _)

F : Type₀
F = Σ f ꞉ (𝔹 → 𝔹) , is-𝓛𝓡-function f

𝐿 𝑅 : F
𝐿 = l , cong l eqC , m-compatibility
𝑅 = r , m-compatibility , cong r eqC

𝑙 𝑟 : F → F
𝑙 (f , a , b) = 𝓛 f a , preservation-𝓛𝓛 f a b , preservation-𝓛𝓡 f a b
𝑟 (f , a , b) = 𝓡 f b , preservation-𝓡𝓛 f a b , preservation-𝓡𝓡 f a b

eq𝐿 : 𝐿 ≡ 𝑙 𝐿
eq𝐿 = ΣProp≡ being-𝓛𝓡-function-is-prop (funExt a)
 where
  a : l ∼ 𝓛 l (cong l eqC)
  a = l-by-cases

eq𝐶 : 𝑙 𝑅 ≡ 𝑟 𝐿
eq𝐶 = ΣProp≡ being-𝓛𝓡-function-is-prop a
 where
  a : cases (l ∘ r) (m ∘ r) m-compatibility
    ≡ cases (m ∘ l) (r ∘ l) m-compatibility
  a = refl

eq𝑅 : 𝑅 ≡ 𝑟 𝑅
eq𝑅 = ΣProp≡ being-𝓛𝓡-function-is-prop (funExt a)
 where
  a : r ∼ 𝓡 r (cong r eqC)
  a = r-by-cases

\end{code}

After the above preparation, our definition of the midpoint operation
_⊕_ is as follows:

\begin{code}

mid : 𝔹 → F
mid = 𝔹-rec 𝐿 𝑅 𝑙 𝑟 eq𝐿 eq𝐶 eq𝑅
_⊕_ : 𝔹 → 𝔹 → 𝔹
x ⊕ y = fst (mid x) y

\end{code}

By construction, the following equations hold:

\begin{code}

⊕-property : (x : 𝔹)
           → (l (x ⊕ R) ≡ m (x ⊕ L))
           × (m (x ⊕ R) ≡ r (x ⊕ L))
⊕-property x = snd (mid x)

⊕-defining-equations : (x y : 𝔹)
   → (  L   ⊕ y   ≡ l y        )
   × (  R   ⊕ y   ≡ r y        )
   × (  l x ⊕ L   ≡ l (x ⊕ L)  )
   × (  l x ⊕ R   ≡ m (x ⊕ R)  )
   × (  l x ⊕ l y ≡ l (x ⊕ y)  )
   × (  l x ⊕ r y ≡ m (x ⊕ y)  )
   × (  r x ⊕ R   ≡ r (x ⊕ R)  )
   × (  r x ⊕ L   ≡ m (x ⊕ L)  )
   × (  r x ⊕ l y ≡ m (x ⊕ y)  )
   × (  r x ⊕ r y ≡ r (x ⊕ y)  )
⊕-defining-equations x y = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl

\end{code}

Digression:

\begin{code}

minv : 𝔹 → 𝔹
minv = cases
        (cases (λ _ → L) l eqL)
        (cases r (λ _ → R) (sym eqR))
        eqC

minv-is-left-inv : (x : 𝔹) → minv (m x) ≡ x
minv-is-left-inv = 𝔹-cases-eq _ _ (λ b → refl) λ b → refl

\end{code}

The function minv satisfies the ES-axioms for a double function:

\begin{code}

minv-C : (x : 𝔹) → minv ((L ⊕ R) ⊕ x) ≡ x
minv-C = 𝔹-cases-eq _ _ (λ x → refl) (λ x → refl)

minv-L : (x : 𝔹) → minv (L ⊕ (L ⊕ x)) ≡ L
minv-L x = refl

minv-R : (x : 𝔹) → minv (R ⊕ (R ⊕ x)) ≡ R
minv-R x = refl

⊕-idemp : (x : 𝔹) → x ≡ x ⊕ x
⊕-idemp = 𝔹-ind-eq _ _
            eqL
            eqR
            (λ x → cong l)
            (λ x → cong r)

⊕-comm : (x y : 𝔹) → x ⊕ y ≡ y ⊕ x
⊕-comm = 𝔹-ind-prop (λ x → ∀ y → x ⊕ y ≡ y ⊕ x)
                     (λ x → isPropΠ (λ y → 𝔹-is-set (x ⊕ y) (y ⊕ x)))
                     L-⊕-comm
                     R-⊕-comm
                     f
                     g
 where
  L-⊕-comm : (y : 𝔹) → L ⊕ y ≡ y ⊕ L
  L-⊕-comm = 𝔹-ind-eq _ _
              refl
              eqC
              (λ y → cong l)
              (λ y → cong m)

  R-⊕-comm : (y : 𝔹) → R ⊕ y ≡ y ⊕ R
  R-⊕-comm = 𝔹-ind-eq _ _
              (sym eqC)
              refl
              (λ y p → cong m p)
              (λ y p → cong r p)

  f : (x : 𝔹) → ((y : 𝔹) → x ⊕ y ≡ y ⊕ x) → (y : 𝔹) → l x ⊕ y ≡ y ⊕ l x
  f x h = 𝔹-cases-eq _ _
           (λ y → cong l (h y))
           (λ y → cong m (h y))

  g : (x : 𝔹) → ((y : 𝔹) → x ⊕ y ≡ y ⊕ x) → (y : 𝔹) → r x ⊕ y ≡ y ⊕ r x
  g x h = 𝔹-cases-eq _ _
           (λ y → cong m (h y))
           (λ y → cong r (h y))

mirror-m : (x : 𝔹) → mirror (m x) ≡ m (mirror x)
mirror-m = 𝔹-cases-eq _ _ (λ b → refl) (λ b → refl)

mirror-⊕ : (x y : 𝔹) → mirror (x ⊕ y) ≡ mirror x ⊕ mirror y
mirror-⊕ = 𝔹-ind-prop
             (λ x → ∀ y → mirror (x ⊕ y) ≡ mirror x ⊕ mirror y)
             (λ x → isPropΠ (λ y → 𝔹-is-set _ _))
             (λ y → refl)
             (λ y → refl)
             (λ x f → 𝔹-cases-eq _ _
                        (λ y → cong r (f y))
                        (λ y → mirror (l x ⊕ r y)          ≡⟨ mirror-m (x ⊕ y) ⟩
                               m (mirror (x ⊕ y))          ≡⟨ cong m (f y) ⟩
                               mirror (l x) ⊕ mirror (r y) ∎))
             (λ x f → 𝔹-cases-eq _ _
                        (λ y → mirror (r x ⊕ l y)          ≡⟨ mirror-m (x ⊕ y) ⟩
                               m (mirror (x ⊕ y))          ≡⟨ cong m (f y) ⟩
                               mirror (r x) ⊕ mirror (l y) ∎)
                        (λ y → cong l (f y)))

M-charac : M ≡ L ⊕ R
M-charac = refl

m-charac : m ∼ M ⊕_
m-charac = 𝔹-cases-eq _ _
             (λ x → refl)
             (λ x → refl)

\end{code}

Hence we shouldn't use m from now on, and we should also avoid l and r
in favour of L ⊕_ and R ⊕_.

\begin{code}

mirror-M : M ≡ mirror M
mirror-M = eqC

LM-lemma : (x : 𝔹) → (L ⊕ M) ⊕ (M ⊕ x) ≡ L ⊕ (R ⊕ x)
LM-lemma = 𝔹-cases-eq _ _ (λ b → refl) (λ b → refl)

LM-transp : (x y : 𝔹) → (L ⊕ M) ⊕ (x ⊕ y) ≡ (L ⊕ x) ⊕ (M ⊕ y)
LM-transp = 𝔹-cases-eq₂ _ _
              (λ x y → refl)
              (λ x y → LM-lemma (x ⊕ y))
              (λ x y → LM-lemma (x ⊕ y))
              (λ x y → refl)

RM-lemma : (x : 𝔹) → (R ⊕ M) ⊕ (M ⊕ x) ≡ R ⊕ (L ⊕ x)
RM-lemma = 𝔹-cases-eq _ _ (λ b → refl) (λ b → refl)

RM-transp : (x y : 𝔹) → (R ⊕ M) ⊕ (x ⊕ y) ≡ (R ⊕ x) ⊕ (M ⊕ y)
RM-transp = 𝔹-cases-eq₂ _ _
              (λ x y → refl)
              (λ x y → RM-lemma (x ⊕ y))
              (λ x y → RM-lemma (x ⊕ y))
              (λ x y → refl)

LL-transp : (x y : 𝔹) → (L ⊕ L) ⊕ (x ⊕ y) ≡ (L ⊕ x) ⊕ (L ⊕ y)
LL-transp x y = cong (_⊕ (x ⊕ y)) (sym (⊕-idemp L))

LR-transp : (x y : 𝔹) → (L ⊕ R) ⊕ (x ⊕ y) ≡ (L ⊕ x) ⊕ (R ⊕ y)
LR-transp x y = refl

RL-transp : (x y : 𝔹) → (R ⊕ L) ⊕ (x ⊕ y) ≡ (R ⊕ x) ⊕ (L ⊕ y)
RL-transp x y = refl

RR-transp : (x y : 𝔹) → (R ⊕ R) ⊕ (x ⊕ y) ≡ (R ⊕ x) ⊕ (R ⊕ y)
RR-transp x y = cong (_⊕ (x ⊕ y)) (sym (⊕-idemp R))

\end{code}

TODO. The transposition axiom (a ⊕ b) ⊕ (x ⊕ y) ≡ (a ⊕ x) ⊕ (b ⊕ y).

A second approach to define midpoint:

\begin{code}

coherence-lem : Square eqC (cong m eqC) (cong l eqR) (cong r eqL)
coherence-lem = doubleCompPath-filler (cong l (sym eqR)) eqC (cong r eqL)

mid2 : 𝔹 → 𝔹 → 𝔹
mid2L : ∀ x → l x ≡ mid2 x L
mid2R : ∀ x → r x ≡ mid2 x R

mid2 L y = l y
mid2 R y = r y
mid2 (l x) L = l (l x)
mid2 (l x) R = r (l x)
mid2 (l x) (l y) = l (mid2 x y)
mid2 (l x) (r y) = m (mid2 x y)
mid2 (l x) (eqL i) = l (mid2L x i)
mid2 (l x) (eqC i) = (cong l (sym (mid2R x)) ∙ cong m (mid2L x)) i
mid2 (l x) (eqR i) = m (mid2R x i)
mid2 (r x) L = l (r x)
mid2 (r x) R = r (r x)
mid2 (r x) (l y) = m (mid2 x y)
mid2 (r x) (r y) = r (mid2 x y)
mid2 (r x) (eqL i) = m (mid2L x i)
mid2 (r x) (eqC i) = (cong m (sym (mid2R x)) ∙ cong r (mid2L x)) i
mid2 (r x) (eqR i) = r (mid2R x i)
mid2 (eqL i) L = l (eqL i)
mid2 (eqL i) R = (eqC ∙ cong r eqL) i
mid2 (eqL i) (l y) = l (l y)
mid2 (eqL i) (r y) = l (r y)
mid2 (eqL i) (eqL j) = l (eqL (i ∨ j))
mid2 (eqL i) (eqC j) = rUnit (cong l eqC) i j
mid2 (eqL i) (eqR j) = hcomp (λ k → λ { (i = i0) → l (eqR (j ∧ k))
                                      ; (i = i1) → coherence-lem k (~ j)
                                      ; (j = i1) → l (eqR k)})
                             (eqC (i ∧ ~ j))
mid2 (eqC i) L = l (eqC i)
mid2 (eqC i) R = r (eqC i)
mid2 (eqC i) (l y) = l (r y)
mid2 (eqC i) (r y) = r (l y)
mid2 (eqC i) (eqL j) = l (eqC (i ∨ j))
mid2 (eqC i) (eqC j) = hcomp (λ k → λ { (j = i0) → l (r R)
                                      ; (j = i1) → m (eqC (i ∨ k))})
                             (m (eqC (i ∧ j)))
mid2 (eqC i) (eqR j) = r (eqC (i ∧ ~ j ))
mid2 (eqR i) L = (sym eqC ∙ cong l eqR) i
mid2 (eqR i) R = r (eqR i)
mid2 (eqR i) (l y) = r (l y)
mid2 (eqR i) (r y) = r (r y)
mid2 (eqR i) (eqL j) = hcomp (λ k → λ { (i = i0) → r (eqL (j ∧ k))
                                      ; (i = i1) → coherence-lem k j
                                      ; (j = i1) → r (eqL k)})
                             (eqC (~ i ∨ j))
mid2 (eqR i) (eqC j) = lUnit (cong r eqC) i j
mid2 (eqR i) (eqR j) = r (eqR (i ∨ j))

mid2L L = refl
mid2L R = eqC
mid2L (l x) = refl
mid2L (r x) = refl
mid2L (eqL i) = refl
mid2L (eqC i) = refl
mid2L (eqR i) = isSet→isSet' 𝔹-is-set eqC (λ _ → l (r R)) (cong l eqR) (sym eqC ∙ cong l eqR) i

mid2R L = sym eqC
mid2R R = refl
mid2R (l x) = refl
mid2R (r x) = refl
mid2R (eqL i) = isSet→isSet' 𝔹-is-set (sym eqC) (λ _ → r (l L)) (cong r eqL) (eqC ∙ cong r eqL) i
mid2R (eqC i) = refl
mid2R (eqR i) = refl

\end{code}

A third approach to define midpoint, which is a combination of the
first and second approaches:

\begin{code}

mid3 : 𝔹 → 𝔹 → 𝔹
mid3L : ∀ x → l (mid3 x R) ≡ m (mid3 x L)
mid3R : ∀ x → m (mid3 x R) ≡ r (mid3 x L)

mid3 L y = l y
mid3 R y = r y
mid3 (l x) L = l (mid3 x L)
mid3 (l x) R = m (mid3 x R)
mid3 (l x) (l y) = l (mid3 x y)
mid3 (l x) (r y) = m (mid3 x y)
mid3 (l x) (eqL i) = l (mid3 x L)
mid3 (l x) (eqC i) = mid3L x i
mid3 (l x) (eqR i) = m (mid3 x R)
mid3 (r x) L = m (mid3 x L)
mid3 (r x) R = r (mid3 x R)
mid3 (r x) (l y) = m (mid3 x y)
mid3 (r x) (r y) = r (mid3 x y)
mid3 (r x) (eqL i) = m (mid3 x L)
mid3 (r x) (eqC i) = mid3R x i
mid3 (r x) (eqR i) = r (mid3 x R)
mid3 (eqL i) L = l (eqL i)
mid3 (eqL i) R = l (eqR i)
mid3 (eqL i) (l y) = l (l y)
mid3 (eqL i) (r y) = l (r y)
mid3 (eqL i) (eqL j) = l (eqL (i ∨ j))
mid3 (eqL i) (eqC j) = l (eqC j)
mid3 (eqL i) (eqR j) = l (eqR (i ∨ j))
mid3 (eqC i) L = l (r L)
mid3 (eqC i) R = r (l R)
mid3 (eqC i) (l y) = l (r y)
mid3 (eqC i) (r y) = r (l y)
mid3 (eqC i) (eqL j) = l (r L)
mid3 (eqC i) (eqC j) = m (eqC j)
mid3 (eqC i) (eqR j) = r (l R)
mid3 (eqR i) L = r (eqL i)
mid3 (eqR i) R = r (eqR i)
mid3 (eqR i) (l y) = r (l y)
mid3 (eqR i) (r y) = r (r y)
mid3 (eqR i) (eqL j) = r (eqL (i ∨ j))
mid3 (eqR i) (eqC j) = r (eqC j)
mid3 (eqR i) (eqR j) = r (eqR (i ∨ j))

mid3L L = cong l eqC
mid3L R = (cong l (sym eqR)) ∙∙ eqC ∙∙ (cong r eqL)
mid3L (l x) = cong l (mid3R x)
mid3L (r x) = cong m (mid3L x)
mid3L (eqL i) = cong l (coherence-lem i)
mid3L (eqC i) = cong (l ∘ r) eqC
mid3L (eqR i) = cong m (coherence-lem i)

mid3R L = cong m eqC
mid3R R = cong r eqC
mid3R (l x) = cong m (mid3R x)
mid3R (r x) = cong r (mid3L x)
mid3R (eqL i) = cong m (coherence-lem i)
mid3R (eqC i) = cong (r ∘ l) eqC
mid3R (eqR i) j = r (doubleCompPath-filler (cong l (sym eqR)) eqC (cong r eqL) i j)

lem : (f : 𝔹 → 𝔹) → {x : 𝔹} → (p : x ≡ f x) → Square p (cong f p) p (cong f p)
lem f p i j = hcomp (λ k → λ { (i = i0) → p j
                             ; (i = i1) → f (p (j ∧ k))
                             ; (j = i0) → p i
                             ; (j = i1) → f (p (i ∧ k))})
                    (p (i ∨ j))

eqLNat : Square eqL (cong l eqL) eqL (cong l eqL)
eqLNat = lem l eqL

eqRNat : Square eqR (cong r eqR) eqR (cong r eqR)
eqRNat = lem r eqR

mid3idem : ∀ x → x ≡ mid3 x x
mid3idem L = eqL
mid3idem R = eqR
mid3idem (l x) = cong l (mid3idem x)
mid3idem (r x) = cong r (mid3idem x)
mid3idem (eqL i) = eqLNat i
mid3idem (eqC i) j = coherence-lem j i
mid3idem (eqR i) = eqRNat i

{-
mid3comm : ∀ x y → mid3 x y ≡ mid3 y x
mid3comm L L = refl
mid3comm L R = eqC
mid3comm L (l y) = cong l (mid3comm L y)
mid3comm L (r y) = cong m (mid3comm L y)
mid3comm L (eqL i) = refl
mid3comm L (eqC i) j = l (eqC (i ∨ j))
mid3comm L (eqR i) = coherence-lem i
mid3comm R L = sym eqC
mid3comm R R = refl
mid3comm R (l y) = cong m (mid3comm R y)
mid3comm R (r y) = cong r (mid3comm R y)
mid3comm R (eqL i) j = coherence-lem i (~ j)
mid3comm R (eqC i) j = r (eqC (i ∧ ~ j))
mid3comm R (eqR i) = refl
mid3comm (l x) L = cong l (mid3comm x L)
mid3comm (l x) R = cong m (mid3comm x R)
mid3comm (l x) (l y) = cong l (mid3comm x y)
mid3comm (l x) (r y) = cong m (mid3comm x y)
mid3comm (l x) (eqL i) = cong l (mid3comm x L)
mid3comm (l x) (eqC i) = {!!}
mid3comm (l x) (eqR i) = cong m (mid3comm x R)
mid3comm (r x) L = cong m (mid3comm x L)
mid3comm (r x) R = cong r (mid3comm x R)
mid3comm (r x) (l y) = cong m (mid3comm x y)
mid3comm (r x) (r y) = cong r (mid3comm x y)
mid3comm (r x) (eqL i) = cong m (mid3comm x L)
mid3comm (r x) (eqC i) = {!!}
mid3comm (r x) (eqR i) = cong r (mid3comm x R)
mid3comm (eqL i) y = {!!}
mid3comm (eqC i) y = {!!}
mid3comm (eqR i) y = {!!}
-}

\end{code}
