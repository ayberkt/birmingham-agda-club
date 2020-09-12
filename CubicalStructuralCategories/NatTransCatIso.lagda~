File Contains a Proof that, if a category 𝓒 is univalent, then all functor precategories where 𝓒
is the target of the functors are univalent as well.

\begin{code}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.CategoriesTwo.NatTransCatIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.CategoriesTwo.Category
open import Cubical.CategoriesTwo.Functor
open import Cubical.CategoriesTwo.NaturalTransformation

isotoidLemma : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
               (F G : 𝒪𝒷 ⟪ FUNCTOR 𝓒 𝓓 ⟫) (p : F ≡ G) (x : 𝒪𝒷 ⟪ 𝓒 ⟫)
            → fst (fst (idtoiso (FUNCTOR 𝓒 𝓓) F G p)) x ≡
               fst (idtoiso 𝓓 (fst F x) (fst G x) (λ i → fst (p i) x)) 
isotoidLemma 𝓒 𝓓 F G p x = J (λ G' p' →
                                 fst (fst (idtoiso (FUNCTOR 𝓒 𝓓) F G' p')) x ≡
                                 fst (idtoiso 𝓓 (fst F x) (fst G' x) (λ i → fst (p' i) x)))
                               (fst (fst (idtoiso (FUNCTOR 𝓒 𝓓) F F refl)) x
                                ≡⟨ cong (λ - → fst (fst -) x)
                                   (idtoiso (FUNCTOR 𝓒 𝓓) F F refl
                                    ≡⟨ transportRefl (CanCatIso (FUNCTOR 𝓒 𝓓) F) ⟩
                                   CanCatIso (FUNCTOR 𝓒 𝓓) F ∎) ⟩
                               fst (fst (CanCatIso (FUNCTOR 𝓒 𝓓) F)) x ≡⟨ refl ⟩
                               fst (𝒾𝒹⟦ FUNCTOR 𝓒 𝓓 ⟧ F) x ≡⟨ refl ⟩
                               𝒾𝒹⟦ 𝓓 ⟧ (fst F x) ≡⟨ refl ⟩
                               fst (CanCatIso 𝓓 (fst F x)) ≡⟨ cong fst
                                (CanCatIso 𝓓 (fst F x)
                                    ≡⟨ sym (transportRefl (CanCatIso 𝓓 (fst F x))) ⟩
                                 idtoiso 𝓓 (fst F x) (fst F x) refl ∎) ⟩
                               fst (idtoiso 𝓓 (fst F x) (fst F x) refl) ∎) p


NatTransIsoLeft : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
                  (F G : 𝒪𝒷 ⟪ FUNCTOR 𝓒 𝓓 ⟫) (x : 𝒪𝒷 ⟪ 𝓒 ⟫)
               → CatIso ⟪ FUNCTOR 𝓒 𝓓 ⟫ F G
               → CatIso ⟪ 𝓓 ⟫ (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)
NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , sec , ret) =
 (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x) , (γ-ob[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ G ⟩⟨ F ⟩ δ ] x) ,
 (funExt⁻ (λ i → fst (sec i)) x) , funExt⁻ (λ i → fst (ret i)) x

NatTransIsoLeftLemma : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞')
                       (𝓓 : PreCategory ℓ𝒟 ℓ𝒟') (F G : 𝒪𝒷 ⟪ FUNCTOR 𝓒 𝓓 ⟫) (p : F ≡ G)
                       (x : 𝒪𝒷 ⟪ 𝓒 ⟫)
                    → NatTransIsoLeft 𝓒 𝓓 F G x (idtoiso (FUNCTOR 𝓒 𝓓) F G p)
                     ≡ idtoiso 𝓓 (fst F x) (fst G x) (λ i → fst (p i) x)
NatTransIsoLeftLemma 𝓒 𝓓 F G p x =
 J (λ G' p' → NatTransIsoLeft 𝓒 𝓓 F G' x (idtoiso (FUNCTOR 𝓒 𝓓) F G' p')
             ≡ idtoiso 𝓓 (fst F x) (fst G' x) (λ i → fst (p' i) x))
   (CatIsoIden 𝓓 (fst F x) (fst F x)
                  (NatTransIsoLeft 𝓒 𝓓 F F x (idtoiso (FUNCTOR 𝓒 𝓓) F F refl))
                  (idtoiso 𝓓 (fst F x) (fst F x) refl)
                  (fst (NatTransIsoLeft 𝓒 𝓓 F F x (idtoiso (FUNCTOR 𝓒 𝓓) F F refl))
                   ≡⟨ cong (λ - → fst (NatTransIsoLeft 𝓒 𝓓 F F x -))
                      (idtoiso (FUNCTOR 𝓒 𝓓) F F refl
                        ≡⟨ transportRefl (CanCatIso (FUNCTOR 𝓒 𝓓) F) ⟩
                      CanCatIso (FUNCTOR 𝓒 𝓓) F ∎) ⟩
                  fst (NatTransIsoLeft 𝓒 𝓓 F F x (CanCatIso (FUNCTOR 𝓒 𝓓) F)) ≡⟨ refl ⟩
                  𝒾𝒹⟦ 𝓓 ⟧ (fst F x) ≡⟨ refl ⟩
                  fst (CanCatIso 𝓓 (fst F x))
                   ≡⟨ cong fst (CanCatIso 𝓓 (fst F x)
                                 ≡⟨ sym (transportRefl (CanCatIso 𝓓 (fst F x))) ⟩
                               idtoiso 𝓓 (fst F x) (fst F x) refl ∎) ⟩
                  fst (idtoiso 𝓓 (fst F x) (fst F x) refl) ∎)) p

isotoid : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
       → isUniv 𝓓 → (F G : 𝒪𝒷 ⟪ (FUNCTOR 𝓒 𝓓) ⟫) → CatIso ⟪ FUNCTOR 𝓒 𝓓 ⟫ F G → F ≡ G
isotoid 𝓒 𝓓 isUniv-𝓓 F G (γ , δ , p , q) =
 ΣPathP ((funExt λ x →
  Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
  (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q))) ,
 ΣPathP
  (implicitFunExt (λ {x} → implicitFunExt (λ {y} → funExt (λ f →
   toPathP ((transIsoNeutral 𝓓 _ _ _ _
            (Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
  (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)))
  (Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)))
  (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q))) (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f)) ∙
  (cong (λ - → 𝑆⟦ 𝓓 ⟧ ←[⟦ 𝓓 ⟧⟨ 𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x ⟩⟨ 𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x ⟩
    idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)
    (Iso.inv
     (equivToIso
      (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
       isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
     (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)))
    ] (𝑆⟦ 𝓓 ⟧ (𝑭[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] f) -))
    (λ i → fst (Iso.rightInv (equivToIso (idtoiso 𝓓 (fst F y) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)))
    (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q)) i1) , isUniv-𝓓 (fst F y) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] y) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] y)))
    (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q)) i1)))
    (NatTransIsoLeft 𝓒 𝓓 F G y (γ , δ , p , q)) i)) ∙
    cong (λ - → 𝑆⟦ 𝓓 ⟧ - (𝑆⟦ 𝓓 ⟧ (fst (snd F) f) (fst γ y)))
    λ i → fst (snd (Iso.rightInv (equivToIso (idtoiso 𝓓 (fst F x) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
    (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)) i1) , isUniv-𝓓 (fst F x) (Iso.inv
    (equivToIso
    (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
     isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
    (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)) i1)))
    (NatTransIsoLeft 𝓒 𝓓 F G x (γ , δ , p , q)) i))) ∙
    (cong (𝑆⟦ 𝓓 ⟧ (fst δ x)) (γ-nat[⟦ 𝓒 ⟧⟦ 𝓓 ⟧⟨ F ⟩⟨ G ⟩ γ ] x y f)) ∙
    (sym (𝑆-α⟦ 𝓓 ⟧ (fst δ x) (fst γ x) (fst (snd G) f))) ∙
    (cong (λ - → 𝑆⟦ 𝓓 ⟧ - (fst (snd G) f)) (funExt⁻ (λ i → fst (p i)) x)) ∙
    𝑆-λ⟦ 𝓓 ⟧ (fst (snd G) f))))) ,
    toPathP (isProp×
    (isPropImplicitΠ (λ x → 𝒽-sets⟦ 𝓓 ⟧ _ _))
    (isPropImplicitΠ (λ x →
     isPropImplicitΠ (λ y → isPropImplicitΠ (λ z →
     isPropΠ (λ f → isPropΠ (λ g → 𝒽-sets⟦ 𝓓 ⟧ _ _)))))) _ _)))
 

UnivEquiv : {ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level} (𝓒 : PreCategory ℓ𝒞 ℓ𝒞') (𝓓 : PreCategory ℓ𝒟 ℓ𝒟')
         → isUniv 𝓓 → isUniv (FUNCTOR 𝓒 𝓓)
UnivEquiv {ℓ𝒞} {ℓ𝒞'} {ℓ𝒟} {ℓ𝒟'} 𝓒 𝓓 isUniv-𝓓 F G =
 isoToIsEquiv (iso (idtoiso (FUNCTOR 𝓒 𝓓) F G) (isotoid 𝓒 𝓓 isUniv-𝓓 F G)
 (λ b → CatIsoIden (FUNCTOR 𝓒 𝓓) F G
         (idtoiso (FUNCTOR 𝓒 𝓓) F G (isotoid 𝓒 𝓓 isUniv-𝓓 F G b))
         b (ΣPathP
  (funExt (λ x → isotoidLemma 𝓒 𝓓 F G (isotoid 𝓒 𝓓 isUniv-𝓓 F G b) x ∙
          λ i → fst (Iso.rightInv (equivToIso (idtoiso 𝓓 (fst F x) (fst G x) ,
                 isUniv-𝓓 (fst F x) (fst G x))) (NatTransIsoLeft 𝓒 𝓓 F G x b) i)) ,
  toPathP (isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ f → 𝒽-sets⟦ 𝓓 ⟧ _ _))) _ _))))
  λ a → FunctorIdenLemma 𝓒 𝓓 F G a ((funExt λ x →
  Iso.inv (equivToIso ((idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)) ,
  isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
  (NatTransIsoLeft 𝓒 𝓓 F G x (idtoiso (FUNCTOR 𝓒 𝓓) F G a))))
   ( funExt
    (λ x →
       Iso.inv
       (equivToIso
        (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
         isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
       (NatTransIsoLeft 𝓒 𝓓 F G x (idtoiso (FUNCTOR 𝓒 𝓓) F G a)))
       ≡⟨ cong (λ - → funExt
    (λ x →
       Iso.inv
       (equivToIso
        (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
         isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
       (- x))) ((λ x → NatTransIsoLeft 𝓒 𝓓 F G x (idtoiso (FUNCTOR 𝓒 𝓓) F G a))
                ≡⟨ funExt (λ x → NatTransIsoLeftLemma 𝓒 𝓓 F G a x) ⟩
                (λ x → idtoiso 𝓓 (fst F x) (fst G x) (λ i → (fst (a i) x))) ∎) ⟩
     funExt
    (λ x →
       Iso.inv
       (equivToIso
        (idtoiso 𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x) ,
         isUniv-𝓓 (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ F ] x) (𝐹[⟦ 𝓒 ⟧⟦ 𝓓 ⟧ G ] x)))
       (idtoiso 𝓓 (fst F x) (fst G x) (λ i → (fst (a i) x)))) ≡⟨ cong (λ - → funExt (λ x → (- x))) (funExt (λ x → Iso.leftInv (equivToIso ((idtoiso 𝓓 (fst F x) (fst G x)) , (isUniv-𝓓 (fst F x) (fst G x)))) λ i → fst (a i) x)) ⟩
      funExt (λ x → (λ i → (fst (a i) x))) ≡⟨ refl ⟩
      (λ i → fst (a i)) ∎) λ i → snd (isotoid 𝓒 𝓓 isUniv-𝓓 F G (idtoiso (FUNCTOR 𝓒 𝓓) F G a) i))

\end{code}
