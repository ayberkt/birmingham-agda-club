(Extremely relevant) exercise, based on CubicalBinarySystem.lagda.

Define the initial binary system twice, as a HIT, and prove that the
two constructions give equivalent types.

\begin{code}

{-# OPTIONS --safe --cubical #-}

module CubicalBinarySystem-exercise-solution where

open import Cubical.Foundations.Prelude

data 𝔹 : Type₀ where
  L R : 𝔹
  l r : 𝔹 → 𝔹
  eqL : L   ≡ l L
  eqC : l R ≡ r L
  eqR : R   ≡ r R

data 𝔹' : Type₀ where
  L R : 𝔹'
  l r : 𝔹' → 𝔹'
  eqL : L   ≡ l L
  eqC : l R ≡ r L
  eqR : R   ≡ r R

φ : 𝔹 → 𝔹'
φ L       = L
φ R       = R
φ (l x)   = l (φ x)
φ (r x)   = r (φ x)
φ (eqL i) = eqL i
φ (eqC i) = eqC i
φ (eqR i) = eqR i

γ : 𝔹' → 𝔹
γ L       = L
γ R       = R
γ (l y)   = l (γ y)
γ (r y)   = r (γ y)
γ (eqL i) = eqL i
γ (eqC i) = eqC i
γ (eqR i) = eqR i

φγ : (y : 𝔹') → φ (γ y) ≡ y
φγ L       = refl
φγ R       = refl
φγ (l y)   = cong l (φγ y)
φγ (r y)   = cong r (φγ y)
φγ (eqL i) = refl
φγ (eqC i) = refl
φγ (eqR i) = refl

γφ : (x : 𝔹) → γ (φ x) ≡ x
γφ L       = refl
γφ R       = refl
γφ (l x)   = cong l (γφ x)
γφ (r x)   = cong r (γφ x)
γφ (eqL i) = refl
γφ (eqC i) = refl
γφ (eqR i) = refl

\end{code}
