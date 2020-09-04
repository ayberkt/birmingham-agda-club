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

ϕ : 𝔹 → 𝔹'
ϕ x = {!!}

γ : 𝔹' → 𝔹
γ y = {!!}

ϕγ : (y : 𝔹') → ϕ (γ y) ≡ y
ϕγ x = {!!}

γϕ : (x : 𝔹) → γ (ϕ x) ≡ x
γϕ x = {!!}

\end{code}
