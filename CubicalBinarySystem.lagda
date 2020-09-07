Martin Escardo and Alex Rice, 4th September 2020.

Produced in the Birmingham Agda Club. We benefited from the company
and discussions with the other members, Todd Ambridge, Tom De Jong,
George Kaye, Owen Milner and Ayberk Tosun.

See the file https://www.cs.bham.ac.uk/~mhe/TypeTopology/InitialBinarySystem.html
for background.

The initial binary system gives the closed interval of dyadic numbers,
and also gives the free midpoint algebra over two generators (this
still needs to be coded in Agda).

We define the initial binary system as a HIT, in cubical type theory,
and also in pure MLTT, and we show that, in cubical type theory, the
two definitions give equivalent types.

The motivation for the investigation in this file is to know whether
the initial binary system is a set, as intended.

\begin{code}

{-# OPTIONS --safe --cubical #-}

module CubicalBinarySystem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to *)
open import Cubical.Foundations.GroupoidLaws


variable
 ℓ ℓ' ℓ₀ ℓ₁ ℓ₂ : Level

idp : {X : Type ℓ} (x : X) → x ≡ x
idp x = refl

Sigma : (X : Type ℓ) (A : X → Type ℓ') → Type (ℓ-max ℓ ℓ')
Sigma = Σ

syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infixr -1 Sigma

_∘_ : {X : Type ℓ₀} {Y : Type ℓ₁} {Z : Y → Type ℓ₂}
    → ((y : Y) → Z y)
    → (f : X → Y) (x : X) → Z (f x)
g ∘ f = λ x → g(f x)

infixl 5 _∘_

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

We first define an auxiliary data type 𝔻, where c is supposed to be
the common point in the images of l and r given by the identification
eqC:

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
 L : 𝔹'
 R : 𝔹'
 η : 𝔻 → 𝔹'

\end{code}

We now define the left and right constructors l' and r' of 𝔹',
corresponding to the constructors l and r of 𝔹:

\begin{code}

l' : 𝔹' → 𝔹'
l' L     = L
l' R     = η center
l' (η x) = η (left x)

r' : 𝔹' → 𝔹'
r' L     = η center
r' R     = R
r' (η x) = η (right x)

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

We also have:

\begin{code}

eql' : (i : I) → L    ≡ eqL' i
eqc' : (i : I) → l' R ≡ eqC' i
eqr' : (i : I) → R    ≡ eqR' i

eql' i = refl
eqc' i = refl
eqr' i = refl

\end{code}

Notice that, by construction, η center is the common point in the
images of l' and r'.

The equivalence of the two constructions is given by the following
pair of mutually inverse maps φ and γ:

\begin{code}

φ : 𝔹 → 𝔹'
φ L       = L
φ R       = R
φ (l x)   = l' (φ x)
φ (r x)   = r' (φ x)
φ (eqL i) = eqL' i
φ (eqC i) = eqC' i
φ (eqR i) = eqR' i

γ : 𝔹' → 𝔹
γ L             = L
γ R             = R
γ (η center)    = l R
γ (η (left y))  = l (γ (η y))
γ (η (right y)) = r (γ (η y))

\end{code}

That φ is a left inverse of γ is easy, by induction on 𝔹':

\begin{code}

φγ : (y : 𝔹') → φ (γ y) ≡ y
φγ L     = refl
φγ R     = refl
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

We now prove that 𝔹 is a set.

\begin{code}

private
 cancellr : 𝔻 → 𝔻
 cancellr center = center -- arbitrary
 cancellr (left x) = x
 cancellr (right x) = x

 cancelη : 𝔹' → 𝔻
 cancelη L = center -- arbitrary
 cancelη R = center -- arbitrary
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
𝔻-is-discrete center center = yes refl
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

is-L : 𝔹' → Type₀
is-L L     = 𝟙
is-L R     = 𝟘
is-L (η x) = 𝟘

is-η : 𝔹' → Type₀
is-η L     = 𝟘
is-η R     = 𝟘
is-η (η x) = 𝟙

L-is-not-R : ¬ L ≡ R
L-is-not-R p = transport (cong is-L p) *

L-is-not-η : {x : 𝔻} → ¬ L ≡ η x
L-is-not-η p = transport (cong is-L p) *

η-is-not-R : {x : 𝔻} → ¬ η x ≡ R
η-is-not-R p = transport (cong is-η p) *

𝔹'-is-discrete : Discrete 𝔹'
𝔹'-is-discrete L     L     = yes refl
𝔹'-is-discrete L     R     = no L-is-not-R
𝔹'-is-discrete L     (η x) = no L-is-not-η
𝔹'-is-discrete R     L     = no (L-is-not-R ∘ sym)
𝔹'-is-discrete R     R     = yes refl
𝔹'-is-discrete R     (η x) = no (η-is-not-R ∘ sym)
𝔹'-is-discrete (η x) L     = no (L-is-not-η ∘ sym)
𝔹'-is-discrete (η x) R     = no η-is-not-R
𝔹'-is-discrete (η x) (η y) = mapDec (cong η) (λ ν p → ν (η-lc p)) (𝔻-is-discrete x y)

𝔹'-is-set : isSet 𝔹'
𝔹'-is-set = Discrete→isSet 𝔹'-is-discrete

𝔹'-is-equiv-to-𝔹 : 𝔹' ≃ 𝔹
𝔹'-is-equiv-to-𝔹 = isoToEquiv (iso γ φ γφ φγ)

𝔹-is-set : isSet 𝔹
𝔹-is-set = isOfHLevelRespectEquiv 2 𝔹'-is-equiv-to-𝔹 𝔹'-is-set

\end{code}

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
 𝔹'-rec L             = x
 𝔹'-rec R             = y
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

 𝔹'-rec-l L     = eqf
 𝔹'-rec-l R     = refl
 𝔹'-rec-l (η x) = refl

 𝔹'-rec-r L     = eqfg
 𝔹'-rec-r R     = eqg
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
 𝔹'-ind L             = x
 𝔹'-ind R             = y
 𝔹'-ind (η center)    = f R y
 𝔹'-ind (η (left x))  = f (η x) (𝔹'-ind (η x))
 𝔹'-ind (η (right x)) = g (η x) (𝔹'-ind (η x))

\end{code}

This satisfies the following equations:

\begin{code}

 𝔹'-ind-l : (x : 𝔹') → 𝔹'-ind (l' x) ≡ f x (𝔹'-ind x)
 𝔹'-ind-r : (x : 𝔹') → 𝔹'-ind (r' x) ≡ g x (𝔹'-ind x)

 𝔹'-ind-L : ∀ i → 𝔹'-ind (eqL' i) ≡ eqf i
 𝔹'-ind-C : ∀ i → 𝔹'-ind (eqC' i) ≡ eqfg i
 𝔹'-ind-R : ∀ i → 𝔹'-ind (eqR' i) ≡ eqg i

\end{code}

With the following proofs:

\begin{code}

 𝔹'-ind-l L     = eqf
 𝔹'-ind-l R     = refl
 𝔹'-ind-l (η x) = refl

 𝔹'-ind-r L     = eqfg
 𝔹'-ind-r R     = eqg
 𝔹'-ind-r (η x) = refl

 𝔹'-ind-L i = fixed-point-construction x (f L) eqf i
 𝔹'-ind-C i = path-construction (f R y) (g L x) eqfg i
 𝔹'-ind-R i = fixed-point-construction y (g R) eqg i

\end{code}

Preparation for the midpoint operation.

\begin{code}

open import Cubical.Data.Sigma

compatible : {X : Type ℓ} (f g : 𝔹 → X) → Type ℓ
compatible f g = f R ≡ g L

cases : {X : Type ℓ} (f g : 𝔹 → X) → compatible f g → (𝔹 → X)
cases f g p L       = f L
cases f g p R       = g R
cases f g p (l x)   = f x
cases f g p (r x)   = g x
cases f g p (eqL i) = f L
cases f g p (eqC i) = p i
cases f g p (eqR i) = g R

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

cases-uniqueness : {X : Type ℓ}
                   (f g : 𝔹 → X)
                   (p : compatible f g)
                   (h : 𝔹 → X)
                   (u : h ∘ l ∼ f)
                   (v : h ∘ r ∼ g)
                 → compatible-higher f g p h u v
                 → h ∼ cases f g p
cases-uniqueness f g p h u v c L = q
 where
  q : h L ≡ f L
  q = cong h eqL ∙ u L
cases-uniqueness f g p h u v c R = q
 where
  q : h R ≡ g R
  q = cong h eqR ∙ v R
cases-uniqueness f g p h u v c (l x) = u x
cases-uniqueness f g p h u v c (r x) = v x
cases-uniqueness f g p h u v c (eqL i) = path-lemma h eqL (u L) i
cases-uniqueness f g p h u v c (eqC i) = c i
cases-uniqueness f g p h u v c (eqR i) = path-lemma h eqR (v R) i

cases-uniqueness-set : {X : Type ℓ}
                       (f g : 𝔹 → X)
                       (p : compatible f g)
                       (h : 𝔹 → X)
                       (u : h ∘ l ∼ f)
                       (v : h ∘ r ∼ g)
                     → isSet X
                     → h ∼ cases f g p
cases-uniqueness-set f g p h u v isSetX =
  cases-uniqueness f g p h u v (isSet→isSet' isSetX (u R) (v L) (cong h eqC) p)


m : 𝔹 → 𝔹
m = cases (l ∘ r) (r ∘ l) p
 where
  p : l (r R) ≡ r (l L)
  p = cong l (sym eqR) ∙ eqC ∙ cong r eqL

left-by-cases : l ∼ cases (l ∘ l) (m ∘ l) (cong l eqC)
left-by-cases = cases-uniqueness (l ∘ l) (m ∘ l) (cong l eqC) l (λ x → refl) (λ x → refl) (λ i → refl)

right-by-cases : r ∼ cases (m ∘ r) (r ∘ r) (cong r eqC)
right-by-cases = cases-uniqueness (r ∘ l) (r ∘ r) (cong r eqC) r (λ x → refl) (λ x → refl) (λ i → refl)

is-𝓛-function : (𝔹 → 𝔹) → Type ℓ-zero
is-𝓛-function f = compatible (l ∘ f) (m ∘ f)

is-𝓡-function : (𝔹 → 𝔹) → Type ℓ-zero
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

is-𝓛𝓡-function : (𝔹 → 𝔹) → Type ℓ-zero
is-𝓛𝓡-function f = is-𝓛-function f × is-𝓡-function f

being-𝓛𝓡-function-is-prop : (f : 𝔹 → 𝔹) → isProp (is-𝓛𝓡-function f)
being-𝓛𝓡-function-is-prop f = isProp× (𝔹-is-set (l (f R)) (m (f L))) (𝔹-is-set (m (f R)) (r (f L)))

F : Type ℓ-zero
F = Σ f ꞉ (𝔹 → 𝔹) , is-𝓛𝓡-function f

𝑙 𝑟 : F → F
𝑙 (f , (a , b)) = 𝓛 f a , preservation-𝓛𝓛 f a b , preservation-𝓛𝓡 f a b
𝑟 (f , (a , b)) = 𝓡 f b , preservation-𝓡𝓛 f a b , preservation-𝓡𝓡 f a b

eqm : l (r R) ≡ r (l L)
eqm = cong l (sym eqR) ∙ eqC ∙ cong r eqL

𝐿 𝑅 : F
𝐿 = l , cong l eqC , eqm
𝑅 = r , eqm , cong r eqC

F-eq-l : 𝐿 ≡ 𝑙 𝐿
F-eq-l = ΣProp≡ being-𝓛𝓡-function-is-prop b
 where
  a : l ∼ 𝓛 l (cong l eqC)
  a = left-by-cases

  b : l ≡ 𝓛 l (cong l eqC)
  b = funExt a


F-eq-lr : 𝑙 𝑅 ≡ 𝑟 𝐿
F-eq-lr = ΣProp≡ being-𝓛𝓡-function-is-prop v
 where
  iii : cases (l ∘ r) (m ∘ r) eqm ∼ cases (m ∘ l) (r ∘ l) eqm
  iii = cases-uniqueness (m ∘ l) (r ∘ l) eqm (cases (l ∘ r) (m ∘ r) eqm) (λ _ → refl) (λ _ → refl) λ _ → refl

  iv : 𝓛 r eqm ∼ 𝓡 l eqm
  iv = iii

  v : 𝓛 r eqm ≡ 𝓡 l eqm
  v = funExt iv


F-eq-r : 𝑅 ≡ 𝑟 𝑅
F-eq-r = ΣProp≡ being-𝓛𝓡-function-is-prop b
 where
  a : r ∼ 𝓡 r (cong r eqC)
  a = right-by-cases

  b : r ≡ 𝓡 r (cong r eqC)
  b = funExt a


mid : 𝔹 → F
mid = 𝔹-rec 𝐿 𝑅 𝑙 𝑟 F-eq-l F-eq-lr F-eq-r

_⊕_ : 𝔹 → 𝔹 → 𝔹
x ⊕ y = fst (mid x) y

⊕-property : (x : 𝔹)
           → (l (x ⊕ R) ≡ m (x ⊕ L))
           × (m (x ⊕ R) ≡ r (x ⊕ L))
⊕-property x = snd (mid x)

mid-equations : (x y : 𝔹)
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
mid-equations x y = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl

coherence-lem : Square eqC (cong m eqC) (cong l eqR) (cong r eqL)
coherence-lem = isSet→isSet' 𝔹-is-set eqC (cong m eqC) (cong l eqR) (cong r eqL)

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
