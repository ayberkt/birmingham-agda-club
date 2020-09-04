(Extremely relevant) exercise, based on CubicalBinarySystem.lagda.

Define the initial binary system twice, as a HIT, and prove that the
two constructions give equivalent types.

\begin{code}

{-# OPTIONS --safe --cubical #-}

module CubicalBinarySystem-exercise where

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
φ x = {!!}

γ : 𝔹' → 𝔹
γ y = {!!}

φγ : (y : 𝔹') → φ (γ y) ≡ y
φγ x = {!!}

γφ : (x : 𝔹) → γ (φ x) ≡ x
γφ x = {!!}

\end{code}
