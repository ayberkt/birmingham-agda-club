\begin{code}

⊕-unique-fixed-point : (a x : 𝔹) → a ⊕ x ≡ x → x ≡ a
⊕-unique-fixed-point = 𝔹-ind-prop (λ a → ∀ x → a ⊕ x ≡ x → x ≡ a )
                   {!!}
                   the-only-fixed-point-of-l-is-L
                   the-only-fixed-point-of-r-is-R
                   (λ a f → 𝔹-cases (λ x → (l a ⊕ x) ≡ x → x ≡ l a)
                                    {!!}
                                    (λ x p → cong l (let
                                                      q : a ⊕ x ≡ x
                                                      q = l-lc p
                                                     in
                                                      f x q))
                                    (λ x p → let
                                              p' : l a ⊕ r x ≡ r x
                                              p' = p
                                              u : rinv (l a ⊕ r x) ≡ x
                                              u = cong rinv p
                                              q : r x ≡ l a
                                              q = {!!}
                                              s : R ≡ a
                                              s = cong linv q
                                              t : x ≡ L
                                              t = cong rinv q
                                             in q))
                   λ a f → 𝔹-cases {!!}
                                   {!!}
                                   (λ x p → {!!})
                                   (λ x p → cong r (f x (r-lc p)))

L-b-transp : (b x y : 𝔹) → (L ⊕ b) ⊕ (x ⊕ y) ≡ (L ⊕ x) ⊕ (b ⊕ y)
L-b-transp = 𝔹-ind-prop (λ b → (x y : 𝔹) → (L ⊕ b) ⊕ (x ⊕ y) ≡ (L ⊕ x) ⊕ (b ⊕ y))
               {!!}
               LL-transp
               LR-transp
               (λ b f → 𝔹-cases-eq₂ _ _
                         (λ x y → cong l (f x y))

                         (λ x y → (L ⊕ l b) ⊕ (l x ⊕ r y)         ≡⟨ refl ⟩
                                  (L ⊕ l b) ⊕ m (x ⊕ y)           ≡⟨ cong ((L ⊕ l b) ⊕_) (m-charac (x ⊕ y)) ⟩
                                  (L ⊕ l b) ⊕ (M ⊕ (x ⊕ y))       ≡⟨ sym (LM-transp (l b) (x ⊕ y)) ⟩
                                  ((L ⊕ M) ⊕ (l b ⊕ (x ⊕ y)))     ≡⟨ refl ⟩
                                  ((L ⊕ M) ⊕ ((L ⊕ b) ⊕ (x ⊕ y))) ≡⟨ cong ((L ⊕ M) ⊕_) (f x y) ⟩
                                  ((L ⊕ M) ⊕ ((L ⊕ x) ⊕ (b ⊕ y))) ≡⟨ LM-transp (L ⊕ x) (b ⊕ y) ⟩
                                  ((L ⊕ (L ⊕ x)) ⊕ (M ⊕ (b ⊕ y))) ≡⟨ refl ⟩
                                  (L ⊕ l x) ⊕ (l b ⊕ r y)         ∎)

                         (λ x y → (L ⊕ l b) ⊕ (r x ⊕ l y)       ≡⟨ cong ((L ⊕ l b) ⊕_) (m-charac (x ⊕ y)) ⟩
                                  (L ⊕ l b) ⊕ (M ⊕ (x ⊕ y))     ≡⟨ cong (λ - → (L ⊕ l b) ⊕ (M ⊕ -)) (⊕-comm x y)  ⟩
                                  (L ⊕ l b) ⊕ (M ⊕ (y ⊕ x))   ≡⟨ sym (LM-transp (l b) (y ⊕ x)) ⟩
                                  (L ⊕ M) ⊕ (l b ⊕ (y ⊕ x)) ≡⟨ cong ((L ⊕ M) ⊕_) (f y x) ⟩
                                  (L ⊕ M) ⊕ ((L ⊕ y) ⊕ (b ⊕ x)) ≡⟨ LM-transp (L ⊕ y) (b ⊕ x) ⟩
                                  (L ⊕ (L ⊕ y)) ⊕ (M ⊕ (b ⊕ x)) ≡⟨ {!!} ⟩
                                  {!!} ≡⟨ {!!} ⟩
                                  m ( ≡⟨ refl ⟩
                                  (L ⊕ r x) ⊕ (l b ⊕ l y)         ∎)

                         (λ x y → (L ⊕ l b) ⊕ (r x ⊕ r y) ≡⟨ {!!} ⟩
                                  (L ⊕ r x) ⊕ (l b ⊕ r y) ∎))
               {!!}


lr-equation  : (x : 𝔹) → l (r x) ≡ m (m x) ⊕ l (m x)
rl-equation  : (x : 𝔹) → r (l x) ≡ m (m x) ⊕ r (m x)
lr-equation' : (x : 𝔹) → l (r x) ≡ m x ⊕ l M
rl-equation' : (x : 𝔹) → r (l x) ≡ m x ⊕ r M

lr-equation  = 𝔹-cases-eq _ _
                 (λ x → cong (l ∘ r ∘ l) (⊕-idemp x))
                 (λ x → cong (l ∘ r ∘ r) (⊕-idemp x))

rl-equation  = 𝔹-cases-eq _ _
                 (λ x → cong (r ∘ l ∘ l) (⊕-idemp x))
                 (λ x → cong (r ∘ l ∘ r) (⊕-idemp x))


lr-equation' = 𝔹-cases-eq _ _
                 (λ x → ⊕-comm (l M) (l (r x)))
                 (λ x → ⊕-comm (l M) (r (l x)))

rl-equation' = 𝔹-cases-eq _ _
               (λ x → ⊕-comm (r M) (l (r x)))
               (λ x → ⊕-comm (r M) (r (l x)))


l-m-transp : (a b : 𝔹) → l a ⊕ m b ≡ m (a ⊕ b) ⊕ l (a ⊕ b)
l-m-transp = 𝔹-cases-eq₂ _ _
              (λ a b → cong (l ∘ m) (⊕-idemp (a ⊕ b)))
              (λ a b → lr-equation (a ⊕ b))
              (λ a b → lr-equation (a ⊕ b))
              (λ a b → cong (m ∘ m) (⊕-idemp (a ⊕ b)))

l-m-transp' : (a b x y : 𝔹) → a ⊕ b ≡ x ⊕ y → l a ⊕ m b ≡ l x ⊕ m y
l-m-transp' a b x y p = l a ⊕ m b             ≡⟨ l-m-transp a b ⟩
                        m (a ⊕ b) ⊕ l (a ⊕ b) ≡⟨ cong₂ (λ x y → ((m x)) ⊕ l y) p p ⟩
                        m (x ⊕ y) ⊕ l (x ⊕ y) ≡⟨ (l-m-transp x y)⁻¹ ⟩
                        l x ⊕ m y             ∎

r-m-transp : (a b : 𝔹) → r a ⊕ m b ≡ m (a ⊕ b) ⊕ r (a ⊕ b)
r-m-transp = 𝔹-cases-eq₂ _ _
              (λ a b → cong (m ∘ m) (⊕-idemp (a ⊕ b)))
              (λ a b → rl-equation (a ⊕ b))
              (λ a b → rl-equation (a ⊕ b))
              (λ a b → cong (r ∘ m) (⊕-idemp (a ⊕ b)))

r-m-transp' : (a b x y : 𝔹) → a ⊕ b ≡ x ⊕ y → r a ⊕ m b ≡ r x ⊕ m y
r-m-transp' a b x y p = r a ⊕ m b             ≡⟨ r-m-transp a b ⟩
                        m (a ⊕ b) ⊕ r (a ⊕ b) ≡⟨ cong₂ (λ x y → ((m x)) ⊕ r y) p p ⟩
                        m (x ⊕ y) ⊕ r (x ⊕ y) ≡⟨ (r-m-transp x y)⁻¹ ⟩
                        r x ⊕ m y             ∎


l-assoc : (x y z : 𝔹) → l x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ l z
r-assoc : (x y z : 𝔹) → r x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ r z

l-assoc = 𝔹-ind-prop (λ x → ∀ y z → l x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ l z)
           {!!}
           (𝔹-cases-eq₂ _ _ (λ y z → refl)
                            (λ y z → cong (_⊕ (l y ⊕ r z)) (sym eqL))
                            (λ y z → cong (_⊕ (r y ⊕ l z)) (sym eqL))
                            (λ y z → refl))
           (𝔹-cases-eq₂ _ _ (λ y z → refl)
                            (λ y z → cong (_⊕ (l y ⊕ r z)) eqC)
                            (λ y z → cong (_⊕ (r y ⊕ l z)) eqC)
                            (λ y z → refl))
           {!!}
           {!!}
r-assoc = {!!}

⊕-transp : (a b x y : 𝔹) → (a ⊕ b) ⊕ (x ⊕ y) ≡ (a ⊕ x) ⊕ (b ⊕ y)
⊕-transp = 𝔹-ind-prop
            (λ a → (b x y : 𝔹) → (a ⊕ b) ⊕ (x ⊕ y) ≡ (a ⊕ x) ⊕ (b ⊕ y))
            (λ a → isPropΠ3 (λ b x y → 𝔹-is-set _ _))
            (𝔹-ind-prop (λ b → (x y : 𝔹) → (L ⊕ b) ⊕ (x ⊕ y) ≡ (L ⊕ x) ⊕ (b ⊕ y))
               (λ b → isPropΠ2 (λ x y → 𝔹-is-set _ _))
               (λ x y → (L ⊕ L) ⊕ (x ⊕ y) ≡⟨ cong (_⊕ (x ⊕ y)) (sym (⊕-idemp L)) ⟩
                        L ⊕ (x ⊕ y)       ≡⟨ refl ⟩
                        (L ⊕ x) ⊕ (L ⊕ y) ∎)
               (λ x y → (L ⊕ R) ⊕ (x ⊕ y) ≡⟨ refl ⟩
                        (L ⊕ x) ⊕ (R ⊕ y) ∎)
               {!!}
               {!!})
            {!!}
            {!!}
            {!!}

⊕-lemma : (a b x : 𝔹) → (a ⊕ b) ⊕ x ≡ (a ⊕ x) ⊕ (b ⊕ x)
⊕-lemma L L x = p
 where
  p : l L ⊕ x ≡ l x ⊕ l x
  p = {!!} easy using idempotency.
⊕-lemma L R x = p
 where
  p : l R ⊕ x ≡ l x ⊕ r x
  p = {!refl!}
⊕-lemma L (l b) x = p
 where
  p : l (l b) ⊕ x ≡ l x ⊕ (l b ⊕ x)
  p = {!!}
⊕-lemma L (r b) x = p
 where
  p : (l (r b)) ⊕ x ≡ l x ⊕ (r b ⊕ x)
  p = {!!}
⊕-lemma L (eqL i) x = {!!}
⊕-lemma L (eqC i) x = {!!}
⊕-lemma L (eqR i) x = {!!}
⊕-lemma R L x = {!!} by symmetry
⊕-lemma R R x = p
 where
  p : r R ⊕ x ≡ r x ⊕ r x
  p = {!!} easy
⊕-lemma R (l b) x = {!!}
 where
  p : r (l b) ⊕ x ≡ r x ⊕ (l b ⊕ x)
  p = {!!}
⊕-lemma R (r b) x = {!!}
⊕-lemma R (eqL i) x = {!!}
⊕-lemma R (eqC i) x = {!!}
⊕-lemma R (eqR i) x = {!!}
⊕-lemma (l a) L x = {!!}
⊕-lemma (l a) R x = {!!}
⊕-lemma (l a) (l b) x = {!!}
⊕-lemma (l a) (r b) x = {!!}
⊕-lemma (l a) (eqL i) x = {!!}
⊕-lemma (l a) (eqC i) x = {!!}
⊕-lemma (l a) (eqR i) x = {!!}
⊕-lemma (r a) L x = {!!}
⊕-lemma (r a) R x = {!!}
⊕-lemma (r a) (l b) x = {!!}
⊕-lemma (r a) (r b) x = {!!}
⊕-lemma (r a) (eqL i) x = {!!}
⊕-lemma (r a) (eqC i) x = {!!}
⊕-lemma (r a) (eqR i) x = {!!}
⊕-lemma (eqL i) L x = {!!}
⊕-lemma (eqL i) R x = {!!}
⊕-lemma (eqL i) (l b) x = {!!}
⊕-lemma (eqL i) (r b) x = {!!}
⊕-lemma (eqL i) (eqL i₁) x = {!!}
⊕-lemma (eqL i) (eqC i₁) x = {!!}
⊕-lemma (eqL i) (eqR i₁) x = {!!}
⊕-lemma (eqC i) L x = {!!}
⊕-lemma (eqC i) R x = {!!}
⊕-lemma (eqC i) (l b) x = {!!}
⊕-lemma (eqC i) (r b) x = {!!}
⊕-lemma (eqC i) (eqL i₁) x = {!!}
⊕-lemma (eqC i) (eqC i₁) x = {!!}
⊕-lemma (eqC i) (eqR i₁) x = {!!}
⊕-lemma (eqR i) L x = {!!}
⊕-lemma (eqR i) R x = {!!}
⊕-lemma (eqR i) (l b) x = {!!}
⊕-lemma (eqR i) (r b) x = {!!}
⊕-lemma (eqR i) (eqL i₁) x = {!!}
⊕-lemma (eqR i) (eqC i₁) x = {!!}
⊕-lemma (eqR i) (eqR i₁) x = {!!}

\end{code}


switch-l-m : (a b : 𝔹) → l a ⊕ m b ≡ m a ⊕ l b
switch-r-m : (a b : 𝔹) → r a ⊕ m b ≡ m a ⊕ r b

switch-l-m = 𝔹-cases-eq₂ _ _
               (λ a b → refl)
               (λ a b → refl)
               (λ a b → refl)
               (λ a b → refl)

switch-r-m = 𝔹-cases-eq₂ _ _
               (λ a b → refl)
               (λ a b → refl)
               (λ a b → refl)
               (λ a b → refl)

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


\end{code}

Minimum and maximum for the natural ordering with L < M < R (which we
haven't defined) and with l and r preserving ≤:

\begin{code}

mmax : 𝔹 → 𝔹 → 𝔹
mmax L L = L
mmax L R = R
mmax L (l y) = l y
mmax L (r y) = r y
mmax L (eqL i) = eqL i
mmax L (eqC i) = eqC i
mmax L (eqR i) = eqR i
mmax R L = R
mmax R R = R
mmax R (l y) = R
mmax R (r y) = R
mmax R (eqL i) = R
mmax R (eqC i) = R
mmax R (eqR i) = R
mmax (l x) L = l x
mmax (l x) R = R
mmax (l x) (l y) = l (mmax x y)
mmax (l x) (r y) = r y
mmax (l L) (eqL i) = l L
mmax (l R) (eqL i) = M
mmax (l (l x)) (eqL i) = l (l x)
mmax (l (r x)) (eqL i) = l (r x)
mmax (l (eqL i)) (eqL j) = cong l eqL {!i ∨ j!}
mmax (l (eqC i)) (eqL j) = {!!}
mmax (l (eqR i)) (eqL j) = {!!}
mmax (l L) (eqC i) = eqC i
mmax (l R) (eqC i) = eqC i
mmax (l (l x)) (eqC i) = eqC i
mmax (l (r x)) (eqC i) = eqC i
mmax (l (eqL i)) (eqC j) = eqC j
mmax (l (eqC i)) (eqC j) = eqC j
mmax (l (eqR i)) (eqC j) = eqC j
mmax (l x) (eqR i) = eqR i
mmax (r x) L = r x
mmax (r x) R = R
mmax (r x) (l y) = r x
mmax (r x) (r y) = r (mmax x y)
mmax (r x) (eqL i) = r x
mmax (r x) (eqC i) = {!!}
mmax (r x) (eqR i) = {!!}
mmax (eqL i) y = {!mmax (eqL i) y!}
mmax (eqC i) y = {!!}
mmax (eqR i) y = {!!}
