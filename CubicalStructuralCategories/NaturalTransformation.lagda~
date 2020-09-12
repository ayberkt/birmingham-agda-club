\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.NaturalTransformation where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.CategoriesTwo.Category
open import Cubical.CategoriesTwo.Functor

NatTrans : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
           (F G : Functor 𝓒 𝓓) → Type (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟')
NatTrans 𝓒 𝓓 F G =
 Σ ((x : 𝒪𝒷 ⟪ 𝓒 ⟫) → 𝒽 ⟪ 𝓓 ⟫ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x))
   λ γ → (x y : 𝒪𝒷 ⟪ 𝓒 ⟫) (f : 𝒽 ⟪ 𝓒 ⟫ x y)
           → 𝑆⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) (γ y) ≡ 𝑆⟦ 𝓓 ⟧ (γ x) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] f)
\end{code}

Useful projections

\begin{code}
γ-ob[⟦_⟧⟦_⟧⟨_⟩⟨_⟩_] : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level}
                       (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟') (F G : Functor 𝓒 𝓓)
                    → (NatTrans 𝓒 𝓓 F G) → (x : 𝒪𝒷 ⟪ 𝓒 ⟫)
                    → 𝒽 ⟪ 𝓓 ⟫ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)
γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] = fst γ

γ-nat[⟦_⟧⟦_⟧⟨_⟩⟨_⟩_] : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level}
                        (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟') (F G : Functor 𝓒 𝓓)
                        (γ : NatTrans 𝓒 𝓓 F G)
                     → ∀ x y (f : 𝒽 ⟪ 𝓒 ⟫ x y)
                     → 𝑆⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] y)
                      ≡ 𝑆⟦ 𝓓 ⟧ (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] f)
γ-nat[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] = snd γ
\end{code}

Material for the Functor preCategory

\begin{code}
id-trans : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
           (F : Functor 𝓒 𝓓) → NatTrans 𝓒 𝓓 F F
id-trans 𝓒 𝓓 F = (λ x → 𝒾𝒹⟦ 𝓓 ⟧ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x)) ,
                    λ x y f → (𝑆-ρ⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f)) ∙
                      (sym (𝑆-λ⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f)))

seq-trans : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
            {F G H : Functor 𝓒 𝓓} (α : NatTrans 𝓒 𝓓 F G) (β : NatTrans 𝓒 𝓓 G H)
         → NatTrans 𝓒 𝓓 F H
seq-trans 𝓒 𝓓 {F} {G} {H} α β =
 (λ x → 𝑆⟦ 𝓓 ⟧ (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] x) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ β ] x)) ,
 λ x y f → (sym (𝑆-α⟦ 𝓓 ⟧
 (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] _) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ β ] _)))
 ∙ (cong (λ - → 𝑆⟦ 𝓓 ⟧ - (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ β ] _))
   (γ-nat[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] x y f)) ∙
 (𝑆-α⟦ 𝓓 ⟧
  (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] _) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] f) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ β ] _))
 ∙ (cong (𝑆⟦ 𝓓 ⟧ (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] _))
    (γ-nat[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ β ] x y f)) ∙
 sym (𝑆-α⟦ 𝓓 ⟧
 (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] _) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ β ] _) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ H ] f))
\end{code}

 A useful equality lemma

\begin{code}
make-nat-trans-path : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level}
                      (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟') (F G : Functor 𝓒 𝓓)
                      (α β : NatTrans 𝓒 𝓓 F G)
                   → γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ α ] ≡ γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ β ] → α ≡ β
make-nat-trans-path 𝓒 𝓓 F G α β p =
 ΣPathP (p , funExt (λ x → funExt (λ y → funExt (λ f → toPathP (𝒽-sets⟦ 𝓓 ⟧ _ _ _ _)))))
\end{code}

A lemma about setness

\begin{code}
NatTransSets : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
             → ∀ F G → isSet (NatTrans 𝓒 𝓓 F G)
NatTransSets 𝓒 𝓓 F G = isSetΣ (isSetΠ (λ x → 𝒽-sets⟦ 𝓓 ⟧))
 λ γ → isSetΠ (λ x → isSetΠ (λ y → isSetΠ (λ f
 → isProp→isSet (𝒽-sets⟦ 𝓓 ⟧
                (𝑆⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) (γ y)) (𝑆⟦ 𝓓 ⟧ (γ x) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] f))))))
\end{code}

The functor preCategory!

\begin{code}
FUNCTOR : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
       → PreCategory (ℓ-max (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟) ℓ𝒟') (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') ℓ𝒟')
FUNCTOR 𝓒 𝓓 = (Functor 𝓒 𝓓) , (((λ F G → NatTrans 𝓒 𝓓 F G) , (id-trans 𝓒 𝓓) ,
 λ {F} {G} {H} α β → seq-trans 𝓒 𝓓 {F} {G} {H} α β) ,
 (λ {F} {G} → NatTransSets 𝓒 𝓓 F G) ,
 ((λ {F} {G} γ → make-nat-trans-path 𝓒 𝓓 F G
                  (seq-trans 𝓒 𝓓 {F} {F} {G} (id-trans 𝓒 𝓓 F) γ) γ
                  (λ i x → 𝑆-λ⟦ 𝓓 ⟧ (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x) i)) ,
  λ {F} {G} γ → make-nat-trans-path 𝓒 𝓓 F G
                 (seq-trans 𝓒 𝓓 {F} {G} {G} γ (id-trans 𝓒 𝓓 G)) γ
                 λ i x → 𝑆-ρ⟦ 𝓓 ⟧ (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x) i) ,
  λ {F} {G} {H} {I} γ δ ε → make-nat-trans-path 𝓒 𝓓 F I (seq-trans 𝓒 𝓓 {F} {H} {I}
  (seq-trans 𝓒 𝓓 {F} {G} {H} γ δ) ε) (seq-trans 𝓒 𝓓 {F} {G} {I} γ
  (seq-trans 𝓒 𝓓 {G} {H} {I} δ ε))
  (funExt (λ x → 𝑆-α⟦ 𝓓 ⟧ (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x)
  (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ H ⟩ δ ] x) (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ H ⟩⟨ I ⟩ ε ] x))))
\end{code}
