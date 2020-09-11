Attempt as directly implementing the dyadics as a HIT

\begin{code}

{-# OPTIONS --cubical --safe --exact-split #-}

module CubicalDyadics where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Divisibility
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Data.Maybe
open import Cubical.HITs.PropositionalTruncation as PropTrunc
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.Logic

≤≡ : ∀ {n m l} → n ≤ m → m ≡ l → n ≤ l
≤≡ (k , p) q = k , (p ∙ q)

2^_ : ℕ → ℕ
2^ zero = 1
2^ suc m = 2^ m + (2^ m)

exp-law : ∀ n m → 2^ n * 2^ m ≡ 2^ (n + m)
exp-law zero m = +-zero (2^ m)
exp-law (suc n) m = sym (*-distribʳ (2^ n) (2^ n) (2^ m)) ∙ cong₂ _+_ (exp-law n m) (exp-law n m)

Fin : ℕ → Type₀
Fin n = Σ[ k ∈ ℕ ] k ≤ n

Fin≡ : ∀ {n} → {x y : Fin n} → fst x ≡ fst y → x ≡ y
Fin≡ = ΣProp≡ λ x → m≤n-isProp

FinPath : ∀ {n m} (p : n ≡ m) (x : Fin n) (y : Fin m) → fst x ≡ fst y → PathP (λ i → Fin (p i)) x y
FinPath p x y q = toPathP (Fin≡ q)

lem : ∀ {a b c d} → a ≤ c → b ≤ d → a + b ≤ c + d
lem p q = ≤-trans (≤-+k p) (≤-k+ q)

_+F_ : ∀ {n m} → Fin n → Fin m → Fin (n + m)
(x , px) +F (y , py) = (x + y) , lem px py

≤-k* : ∀ {m n k} → m ≤ n → k * m ≤ k * n
≤-k* {m} {n} {zero} p = ≤-refl
≤-k* {m} {n} {suc k} p = lem p (≤-k* {k = k} p)

≤-*k : ∀ {m n k} → m ≤ n → m * k ≤ n * k
≤-*k {m} {n} {k} =
    subst (_≤ n * k) (*-comm k m)
  ∘ subst (k * m ≤_) (*-comm k n)
  ∘ ≤-k* {m} {n} {k}

lem* : ∀ {a b c d} → a ≤ c → b ≤ d → a * b ≤ c * d
lem* {c = c} p q = ≤-trans (≤-*k p) (≤-k* {k = c} q)

*F : ∀ n m → Fin (2^ n) → Fin (2^ m) → Fin (2^ (n + m))
*F n m (x , px) (y , py) = (x * y) , ≤≡ (lem* px py) (exp-law n m)

full : ∀ n → Fin n
full n = n , ≤-refl

fzero : ∀ n → Fin n
fzero n = zero , zero-≤

data Dyadic : Type₀ where
  Num : (n : ℕ) → Fin (2^ n) → Dyadic
  Reduce : (n : ℕ) → (x : Fin (2^ n)) → Num n x ≡ Num (suc n) (x +F x)
  Squash : isSet Dyadic

Num≡ : ∀ {n m} → (n ≡ m) → (x : Fin (2^ n)) → (y : Fin (2^ m)) → (fst x ≡ fst y) → Num n x ≡ Num m y
Num≡ p x y q i = Num (p i) (FinPath (cong 2^_ p) x y q i)

expand : (k n : ℕ) → (x : Fin (2^ n)) → Num n x ≡ Num (k + n) (*F k n (full (2^ k)) x)
expand zero n x = Num≡ refl x (*F zero n (full (2^ zero)) x) (sym (+-zero (fst x)))
expand (suc k) n x = expand k n x ∙∙ Reduce _ _ ∙∙ Num≡ refl _ _ (*-distribʳ (2^ k) (2^ k) (fst x))

Num≡* : ∀ {n m} → (x : Fin (2^ n)) → (y : Fin (2^ m)) → 2^ m * fst x ≡ 2^ n * fst y → Num n x ≡ Num m y
Num≡* {n} {m} x y p = (expand m n x) ∙∙ Num≡ (+-comm m n) _ _ p ∙∙ sym (expand n m y)

propExt : {A B : Type₀} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B
propExt {A} {B} pA pB f g i = [ (⇔toPath {P = A , pA} {Q = B , pB} f g i) ]

interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
interchange a b c d =
  a + b + (c + d) ≡⟨ +-assoc (a + b) c d ⟩
  a + b + c + d ≡⟨ cong (_+ d) (sym (+-assoc a b c)) ⟩
  a + (b + c) + d ≡⟨ cong (λ x → a + x + d) (+-comm b c) ⟩
  a + (c + b) + d ≡⟨ cong (_+ d) (+-assoc a c b) ⟩
  a + c + b + d ≡⟨ sym (+-assoc (a + c) b d) ⟩
  a + c + (b + d) ∎

*-distribˡ : ∀ m n o → (m * n) + (m * o) ≡ m * (n + o)
*-distribˡ zero _ _ = refl
*-distribˡ (suc m) n o =
  n + m * n + (o + m * o) ≡⟨ interchange n (m * n) o (m * o) ⟩
  n + o + (m * n + m * o) ≡⟨ cong (n + o +_) (*-distribˡ m n o) ⟩
  n + o + m * (n + o) ∎

div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

div2lem : (n : ℕ) → div2 (n + n) ≡ n
div2lem zero = refl
div2lem (suc n) =
  div2 (suc n + suc n) ≡⟨ cong div2 (+-suc (suc n) n) ⟩
  suc (div2 (n + n)) ≡⟨ cong suc (div2lem n) ⟩
  suc n ∎

lem1 : ∀ a b c d → d * a ≡ c * b → (d + d) * a ≡ c * (b + b)
lem1 a b c d p = (d + d) * a ≡⟨ sym (*-distribʳ d d a) ⟩
                 d * a + d * a ≡⟨ cong₂ _+_ p p ⟩
                 c * b + c * b ≡⟨ *-distribˡ c b b ⟩
                 c * (b + b) ∎

lem2 : ∀ a b c d → (d + d) * a ≡ c * (b + b) → d * a ≡ c * b
lem2 a b c d p = d * a ≡⟨ sym (div2lem (d * a)) ⟩
                 div2 (d * a + d * a) ≡⟨ cong div2 (*-distribʳ d d a) ⟩
                 div2 ((d + d) * a) ≡⟨ cong div2 p ⟩
                 div2 (c * (b + b)) ≡⟨ cong div2 (sym (*-distribˡ c b b)) ⟩
                 div2 (c * b + c * b) ≡⟨ div2lem (c * b) ⟩
                 c * b ∎

_≡D'_ : Dyadic → Dyadic → hProp ℓ-zero
Num n (a , _) ≡D' Num m (b , _) = (2^ m * a ≡ 2^ n * b) , isSetℕ (2^ m * a) ((2^ n) * b)
Num n x@(a , _) ≡D' Reduce m y@(b , _) i =
  ⇔toPath {P = Num n x ≡D' Num m y}
          {Q = Num n x ≡D' Num (suc m) (y +F y)}
          (λ p → lem1 a b (2^ n) (2^ m) p)
          (λ p → lem2 a b (2^ n) (2^ m) p)
          i

Num n x ≡D' Squash b b₁ x₁ y i i₁ = {!!}
Reduce n x@(a , _) i ≡D' Num m y@(b , _) =
  ⇔toPath {P = Num n x ≡D' Num m y}
          {Q = Num (suc n) (x +F x) ≡D' Num m y}
          (λ p → sym (lem1 b a (2^ m) (2^ n) (sym p)))
          (λ p → sym (lem2 b a (2^ m) (2^ n) (sym p)))
          i
Reduce n x i ≡D' Reduce m y j =
  isSet→isSet' isSetHProp
               {Num n x ≡D' Num m y}
               {Num n x ≡D' Num (suc m) (y +F y)}
               (λ j → Num n x ≡D' Reduce m y j)
               {Num (suc n) (x +F x) ≡D' Num m y}
               {Num (suc n) (x +F x) ≡D' Num (suc m) (y +F y)}
               (λ j → Num (suc n) (x +F x) ≡D' Reduce m y j)
               (λ i → Reduce n x i ≡D' Num m y)
               (λ i → Reduce n x i ≡D' Num (suc m) (y +F y))
               i
               j
Reduce n x i ≡D' Squash b b₁ x₁ y i₁ i₂ = {!!}
Squash a a₁ x y i i₁ ≡D' b = {!!}

-- _≡D_ : Dyadic → Dyadic → Type₀
-- Num n (a , _) ≡D Num m (b , _) = 2^ m * a ≡ 2^ n * b
-- Num n (a , _) ≡D Reduce m (b , _) i =
--   propExt (isSetℕ (2^ m * a) (2^ n * b))
--           (isSetℕ (((2^ m) + (2^ m)) * a) ((2^ n) * (b + b)))
--           (λ p → ((2^ m) + (2^ m)) * a ≡⟨ sym (*-distribʳ (2^ m) (2^ m) a) ⟩
--                  2^ m * a + 2^ m * a ≡⟨ cong₂ _+_ p p ⟩
--                  2^ n * b + 2^ n * b ≡⟨ *-distribˡ (2^ n) b b ⟩
--                  (2^ n) * (b + b) ∎)
--           (λ p → (2^ m) * a ≡⟨ sym (div2lem ((2^ m) * a)) ⟩
--                  div2 (2^ m * a + 2^ m * a) ≡⟨ cong div2 (*-distribʳ (2^ m) (2^ m) a) ⟩
--                  div2 ((2^ m + 2^ m) * a) ≡⟨ cong div2 p ⟩
--                  div2 ((2^ n) * (b + b)) ≡⟨ cong div2 (sym (*-distribˡ (2^ n) b b)) ⟩
--                  div2 ((2^ n) * b + (2^ n) * b) ≡⟨ div2lem ((2^ n) * b) ⟩
--                  (2^ n) * b ∎)
--           i
-- Num n x ≡D Squash b b₁ x₁ y i i₁ = {!!}
-- Reduce n x i ≡D Num m y = {!!}
-- Reduce n x i ≡D Reduce m y j = {!!}
-- Reduce n x i ≡D Squash b b₁ x₁ y i₁ i₂ = {!!}
-- Squash a a₁ x y i i₁ ≡D b = {!!}

sq-set : (A : I → I → Type₀) → (∀ i j → isSet (A i j)) →
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
sq-set A isSetA a₀₋ a₁₋ a₋₀ a₋₁ = toPathP (helper (λ i → isSetA i1 i) (transp (λ i → PathP (A i) (a₋₀ i) (a₋₁ i)) i0 a₀₋) a₁₋)
  where

    test3 : {A B : Type₀} → (p : A ≡ B) → (x : A) → transport (sym p) (transport p x) ≡ x
    test3 p x j = transp (λ i → p (~ i ∧ ~ j)) j (transp (λ i → p (i ∧ ~ j)) j x)

    test : {A B : Type₀} → (p : A ≡ B) → (x y : A) → transport p x ≡ transport p y → x ≡ y
    test p x y q = sym (test3 p x) ∙∙ cong (transport (sym p)) q ∙∙ test3 p y

    helper : {B : I → Type₀} → ((i : I) → isSet (B i)) → {a : B i0} {b : B i1} (p q : PathP (λ i → B i) a b) → p ≡ q
    helper {B} isSetB {a} {b} p q = test (PathP≡Path B a b) p q (isSetB i1 (transport (λ i → B i) a) b (transport (PathP≡Path B a b) p) (transport (PathP≡Path B a b) q))




Dyadic-ind : {X : Dyadic → Set}
           → ((d : Dyadic) → isSet (X d))
           → (f : (n : ℕ) → (x : Fin (2^ n)) → X (Num n x))
           → ((n : ℕ) → (x : Fin (2^ n)) → PathP (λ i → X (Reduce n x i)) (f n x) (f (suc n) (x +F x)))
           → (d : Dyadic) → X d
Dyadic-ind isSet f e (Num n x) = f n x
Dyadic-ind isSet f e (Reduce n x i) = e n x i
Dyadic-ind {X} isSet f e (Squash x y p q i j) = sq-set (λ i j → X (Squash x y p q i j))
                                                       (λ i j → isSet (Squash x y p q i j))
                                                       (λ j → Dyadic-ind isSet f e (p j))
                                                       (λ j → Dyadic-ind isSet f e (q j))
                                                       (λ i → Dyadic-ind isSet f e x)
                                                       (λ i → Dyadic-ind isSet f e y)
                                                       i
                                                       j

Dyadic-rec : {X : Set}
           → isSet X
           → (f : (n : ℕ) → Fin (2^ n) → X)
           → ((n : ℕ) → (x : Fin (2^ n)) → f n x ≡ f (suc n) (x +F x))
           → Dyadic
           → X
Dyadic-rec isSetX f e (Num n x) = f n x
Dyadic-rec isSetX f e (Reduce n x i) = e n x i
Dyadic-rec isSetX f e (Squash x y p q i j) = isSet→isSet' isSetX
                                                          (λ j → Dyadic-rec isSetX f e (p j))
                                                          (λ j → Dyadic-rec isSetX f e (q j))
                                                          (λ i → Dyadic-rec isSetX f e x)
                                                          (λ i → Dyadic-rec isSetX f e y)
                                                          i
                                                          j

Dyadic-rec-2 : {X : Set}
             → isSet X
             → (f : (n m : ℕ) → Fin (2^ n) → Fin (2^ m) → X)
             → ((n m : ℕ) → (x : Fin (2^ n)) → (y : Fin (2^ m)) → f n m x y ≡ f (suc n) m (x +F x) y)
             → ((n m : ℕ) → (x : Fin (2^ n)) → (y : Fin (2^ m)) → f n m x y ≡ f n (suc m) x (y +F y))
             → Dyadic → Dyadic → X
Dyadic-rec-2 isSetX f e₁ e₂ = Dyadic-rec (isSetΠ λ _ → isSetX) rest coh
  where
    rest : (n : ℕ) → Fin (2^ n) → Dyadic → _
    rest n x = Dyadic-rec isSetX (λ m y → f n m x y) λ m y → e₂ n m x y

    coh : (n : ℕ) (x : Fin (2^ n)) → rest n x ≡ rest (suc n) (x +F x)
    coh n x i (Num m y) = e₁ n m x y i
    coh n x i (Reduce m y j) = isSet→isSet' isSetX
                                            (λ j → e₂ n m x y j)
                                            (λ j → e₂ (suc n) m (x +F x) y j)
                                            (λ i → e₁ n m x y i)
                                            (λ i → e₁ n (suc m) x (y +F y) i)
                                            i
                                            j
    coh n x i (Squash y z p q j k) = isSet→isSet' isSetX
                                                  (λ k → coh n x i (p k))
                                                  (λ k → coh n x i (q k))
                                                  (λ j → coh n x i y)
                                                  (λ j → coh n x i z)
                                                  j
                                                  k

Dyadic≡ : {X : Set}
        → isSet X
        → (f g : Dyadic → X)
        → ((n : ℕ) → (x : Fin (2^ n)) → f (Num n x) ≡ g (Num n x))
        → (d : Dyadic) → f d ≡ g d
Dyadic≡ isSetX f g e = Dyadic-ind (λ d → isProp→isSet (isSetX (f d) (g d)))
                                  (λ n x → e n x)
                                  (λ n x → isSet→isSet' isSetX (e n x) (e (suc n) (x +F x)) (cong f (Reduce _ _)) (cong g (Reduce _ _)))


Dyadic≡2 : {X : Set}
         → isSet X
         → (f g : (x y : Dyadic) → X)
         → ((n m : ℕ) → (x : Fin (2^ n)) → (y : Fin (2^ m)) → f (Num n x) (Num m y) ≡ g (Num n x) (Num m y))
         → (x y : Dyadic) → f x y ≡ g x y
Dyadic≡2 isSetX f g e x = Dyadic≡ isSetX (f x) (g x) pf
  where
    pf : (m : ℕ) (y : Fin (2^ m)) → f x (Num m y) ≡ g x (Num m y)
    pf m y = Dyadic≡ isSetX (λ d → f d (Num m y)) (λ d → g d (Num m y)) (λ n x → e n m x y) x

Dyadic≡3 : {X : Set}
         → isSet X
         → (f g : (x y z : Dyadic) → X)
         → ((n m l : ℕ) → (x : Fin (2^ n)) → (y : Fin (2^ m)) → (z : Fin (2^ l)) → f (Num n x) (Num m y) (Num l z) ≡ g (Num n x) (Num m y) (Num l z))
         → (x y z : Dyadic) → f x y z ≡ g x y z
Dyadic≡3 isSetX f g e x = Dyadic≡2 isSetX (f x) (g x) pf
  where
    pf : (m l : ℕ) (y : Fin (2^ m)) (z : Fin (2^ l)) → f x (Num m y) (Num l z) ≡ g x (Num m y) (Num l z)
    pf m l y z = Dyadic≡ isSetX (λ d → f d (Num m y) (Num l z)) (λ d → g d (Num m y) (Num l z)) (λ n x → e n m l x y z) x

Dyadic≡4 : {X : Set}
         → isSet X
         → (f g : (x y z w : Dyadic) → X)
         → ((n m l o : ℕ) → (x : Fin (2^ n)) → (y : Fin (2^ m)) → (z : Fin (2^ l)) → (w : Fin (2^ o)) → f (Num n x) (Num m y) (Num l z) (Num o w) ≡ g (Num n x) (Num m y) (Num l z) (Num o w))
         → (x y z w : Dyadic) → f x y z w ≡ g x y z w
Dyadic≡4 isSetX f g e x = Dyadic≡3 isSetX (f x) (g x) pf
  where
    pf : (m l o : ℕ) (y : Fin (2^ m)) (z : Fin (2^ l)) (w : Fin (2^ o)) → f x (Num m y) (Num l z) (Num o w) ≡ g x (Num m y) (Num l z) (Num o w)
    pf m l o y z w = Dyadic≡ isSetX (λ d → f d (Num m y) (Num l z) (Num o w)) (λ d → g d (Num m y) (Num l z) (Num o w)) (λ n x → e n m l o x y z w) x


_⊕_ : Dyadic → Dyadic → Dyadic
_⊕_ = Dyadic-rec-2 Squash f e₁ e₂
  where
    f : (n m : ℕ) → Fin (2^ n) → Fin (2^ m) → Dyadic
    f n m x y = Num (suc (n + m)) ((*F n m x (full (2^ m))) +F (*F n m (full (2^ n)) y))

    e₁ : (n m : ℕ) (x : Fin (2^ n)) (y : Fin (2^ m)) →
           f n m x y ≡ f (suc n) m (x +F x) y
    e₁ n m x@(a , _) y@(b , _) = (Reduce _ _) ∙ Num≡ refl _ _
      (a * (2^ m) + (2^ n) * b + (a * (2^ m) + (2^ n) * b) ≡⟨ interchange (a * (2^ m)) ((2^ n) * b) (a * (2^ m)) ((2^ n) * b) ⟩
       a * (2^ m) + a * (2^ m) + ((2^ n) * b + (2^ n) * b) ≡⟨ cong₂ _+_ (*-distribʳ a a (2^ m)) (*-distribʳ (2^ n) (2^ n) b) ⟩
       (a + a) * (2^ m) + ((2^ n) + (2^ n)) * b ∎)

    e₂ : (n m : ℕ) (x : Fin (2^ n)) (y : Fin (2^ m)) →
           f n m x y ≡ f n (suc m) x (y +F y)
    e₂ n m x@(a , _) y@(b , _) = (Reduce _ _) ∙ Num≡ (cong suc (sym (+-suc n m))) _ _
      (a * (2^ m) + (2^ n) * b + (a * (2^ m) + (2^ n) * b) ≡⟨ interchange (a * (2^ m)) ((2^ n) * b) (a * (2^ m)) ((2^ n) * b) ⟩
       a * (2^ m) + a * (2^ m) + ((2^ n) * b + (2^ n) * b) ≡⟨ cong₂ _+_ (*-distribˡ a (2^ m) (2^ m)) (*-distribˡ (2^ n) b b) ⟩
       a * ((2^ m) + (2^ m)) + (2^ n) * (b + b) ∎)

L R : Dyadic
L = Num 0 (0 , zero-≤)
R = Num 0 (1 , ≤-refl)

l r : Dyadic → Dyadic

l = Dyadic-rec Squash (λ n x → Num (suc n) (fzero (2^ n) +F x))
     λ n x → (Reduce _ _) ∙ (Num≡ refl _ _ refl)

r = Dyadic-rec Squash (λ n x → Num (suc n) (full (2^ n) +F x))
     λ n x → (Reduce _ _) ∙ (Num≡ refl _ _ (interchange (2^ n) (fst x) (2^ n) (fst x)))

⊕-idem : ∀ d → d ⊕ d ≡ d
⊕-idem = Dyadic≡ Squash (λ d → d ⊕ d) (λ d → d) pf
  where
    pf : (n : ℕ) (x : Fin (2^ n)) → (Num n x ⊕ Num n x) ≡ Num n x
    pf n (a , _) = Num≡* _ _ e
      where
        e : (2^ n) * (a * (2^ n) + (2^ n) * a) ≡
            ((2^ (n + n)) + (2^ (n + n))) * a
        e = (2^ n) * (a * (2^ n) + (2^ n) * a) ≡⟨ cong (λ b → (2^ n) * (b + (2^ n) * a)) (*-comm a (2^ n)) ⟩
            (2^ n) * ((2^ n) * a + (2^ n) * a) ≡⟨ cong ((2^ n) *_) (*-distribʳ (2^ n) (2^ n) a) ⟩
            (2^ n) * (((2^ n) + (2^ n)) * a) ≡⟨ *-assoc (2^ n) ((2^ n) + (2^ n)) a ⟩
            (2^ n) * ((2^ n) + (2^ n)) * a ≡⟨ cong (_* a) (sym (*-distribˡ (2^ n) (2^ n) (2^ n))) ⟩
            ((2^ n) * (2^ n) + (2^ n) * (2^ n)) * a ≡⟨ cong₂ (λ b c → (b + c) * a) (exp-law n n) (exp-law n n) ⟩
            ((2^ (n + n)) + (2^ (n + n))) * a ∎

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm = Dyadic≡2 Squash _⊕_ (λ x y → y ⊕ x) pf
  where
    pf : (n m : ℕ) (x : Fin (2^ n)) (y : Fin (2^ m)) →
           (Num n x ⊕ Num m y) ≡ (Num m y ⊕ Num n x)
    pf n m (a , _) (b , _) = Num≡ (cong suc (+-comm n m)) _ _ e
      where
        e : a * (2^ m) + (2^ n) * b ≡ b * (2^ n) + (2^ m) * a
        e = a * (2^ m) + (2^ n) * b ≡⟨ cong₂ _+_ (*-comm a (2^ m)) (*-comm (2^ n) b) ⟩
            (2^ m) * a + b * (2^ n) ≡⟨ +-comm ((2^ m) * a) (b * (2^ n)) ⟩
            b * (2^ n) + (2^ m) * a ∎

⊕-trans : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-trans = Dyadic≡4 Squash (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d)) (λ a b c d → (a ⊕ c) ⊕ (b ⊕ d)) pf
  where
    pf : (n m l o : ℕ) (x : Fin (2^ n)) (y : Fin (2^ m)) (z : Fin (2^ l))
           (w : Fin (2^ o)) →
           ((Num n x ⊕ Num m y) ⊕ (Num l z ⊕ Num o w)) ≡
           ((Num n x ⊕ Num l z) ⊕ (Num m y ⊕ Num o w))
    pf n m l o (a , _) (b , _) (c , _) (d , _) =
      Num≡ (cong (suc ∘ suc) e1) _ _ e2
        where
          e1 : n + m + suc (l + o) ≡ n + l + suc (m + o)
          e1 = n + m + suc (l + o) ≡⟨ +-suc (n + m) (l + o) ⟩
               suc (n + m + (l + o)) ≡⟨ cong suc (interchange n m l o) ⟩
               suc (n + l + (m + o)) ≡⟨ sym (+-suc (n + l) (m + o)) ⟩
               n + l + suc (m + o) ∎

          lema' : m + suc (l + o) ≡ l + suc (m + o)
          lema' = m + suc (l + o) ≡⟨ +-suc m (l + o) ⟩
                  1 + m + (l + o) ≡⟨ interchange 1 m l o ⟩
                  1 + l + (m + o) ≡⟨ sym (+-suc l (m + o)) ⟩
                  l + suc (m + o) ∎

          lema : (2^ m) * (2^ suc (l + o)) ≡ (2^ l) * (2^ suc (m + o))
          lema = (2^ m) * (2^ suc (l + o)) ≡⟨ exp-law m (suc (l + o)) ⟩
                 (2^ (m + suc (l + o))) ≡⟨ cong 2^_ lema' ⟩
                 (2^ (l + suc (m + o))) ≡⟨ sym (exp-law l (suc (m + o))) ⟩
                 (2^ l) * (2^ suc (m + o)) ∎

          aproof : a * (2^ m) * (2^ suc (l + o)) ≡ a * (2^ l) * (2^ suc (m + o))
          aproof = a * (2^ m) * (2^ suc (l + o)) ≡⟨ sym (*-assoc a (2^ m) (2^ suc (l + o))) ⟩
                   a * ((2^ m) * (2^ suc (l + o))) ≡⟨ cong (a *_) lema ⟩
                   a * ((2^ l) * (2^ suc (m + o))) ≡⟨ *-assoc a (2^ l) (2^ suc (m + o)) ⟩
                   a * (2^ l) * (2^ suc (m + o)) ∎


          cproof : (2^ suc (n + m)) * (c * (2^ o)) ≡ (2^ n) * c * (2^ suc (m + o))
          cproof = {!!}

          bproof : (2^ n) * b * (2^ suc (l + o)) ≡ (2^ suc (n + l)) * (b * (2^ o))
          bproof = {!!}

          dproof : (2^ suc (n + m)) * ((2^ l) * d) ≡ (2^ suc (n + l)) * ((2^ m) * d)
          dproof = {!!}

          e2 : (a * (2^ m) + (2^ n) * b) * ((2^ (l + o)) + (2^ (l + o))) +
               ((2^ (n + m)) + (2^ (n + m))) * (c * (2^ o) + (2^ l) * d)
               ≡
               (a * (2^ l) + (2^ n) * c) * ((2^ (m + o)) + (2^ (m + o))) +
               ((2^ (n + l)) + (2^ (n + l))) * (b * (2^ o) + (2^ m) * d)
          e2 = (a * (2^ m) + (2^ n) * b) * (2^ (suc (l + o))) +
                 (2^ (suc (n + m))) * (c * (2^ o) + (2^ l) * d)
                   ≡⟨ sym (cong₂ _+_ (*-distribʳ (a * 2^ m) ((2^ n) * b) (2^ suc (l + o))) (*-distribˡ (2^ (suc (n + m))) (c * (2^ o)) ((2^ l) * d))) ⟩
               a * (2^ m) * (2^ suc (l + o)) + (2^ n) * b * (2^ suc (l + o)) +
                 ((2^ suc (n + m)) * (c * (2^ o)) + (2^ suc (n + m)) * ((2^ l) * d)) ≡⟨ interchange (a * (2^ m) * (2^ suc (l + o))) ((2^ n) * b * (2^ suc (l + o))) ((2^ suc (n + m)) * (c * (2^ o))) ((2^ suc (n + m)) * ((2^ l) * d)) ⟩
               a * (2^ m) * (2^ suc (l + o)) + (2^ suc (n + m)) * (c * (2^ o)) +
                 ((2^ n) * b * (2^ suc (l + o)) + (2^ suc (n + m)) * ((2^ l) * d)) ≡⟨ cong₂ _+_ (cong₂ _+_ aproof cproof) (cong₂ _+_ bproof dproof) ⟩
               a * (2^ l) * (2^ suc (m + o)) + (2^ n) * c * (2^ suc (m + o)) +
                 ((2^ suc (n + l)) * (b * (2^ o)) + (2^ suc (n + l)) * ((2^ m) * d)) ≡⟨ cong₂ _+_ (*-distribʳ (a * (2^ l)) ((2^ n) * c) (2^ suc (m + o))) (*-distribˡ (2^ suc (n + l)) (b * (2^ o)) ((2^ m) * d)) ⟩
               (a * (2^ l) + (2^ n) * c) * (2^ suc (m + o)) +
                 (2^ suc (n + l)) * (b * (2^ o) + (2^ m) * d) ∎


\end{code}
