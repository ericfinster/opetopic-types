{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module LowDims where

  module _ (A : Set) where

    UnaryRel : Set₁
    UnaryRel = A → A → Set 

    is-fib-unary : UnaryRel → Set
    is-fib-unary Q = (a₀ : A) → is-contr (Σ A (λ a₁ → Q a₀ a₁))

    data seq (Q : UnaryRel) : A → A → Set where
      emp : {a : A} → seq Q a a
      ext : {a₀ a₁ a₂ : A}
        → (s : seq Q a₀ a₁) (r : Q a₁ a₂) 
        → seq Q a₀ a₂

    SeqRel : UnaryRel → Set₁
    SeqRel Q = {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁ → Set 

    is-fib-seq : {Q : UnaryRel} → SeqRel Q → Set
    is-fib-seq {Q} V = {a₀ a₁ : A} (σ : seq Q a₀ a₁)
      → is-contr (Σ (Q a₀ a₁) (V σ)) 

    --  Showing that a fibrant, unital relation admits a composition
    module _ (Q : UnaryRel) (refl-Q : (a : A) → Q a a) (is-fib-Q : is-fib-unary Q) where

      Q-elim : (a₀ : A) (P : Σ A (Q a₀) → Set)
        → (r : P (a₀ , refl-Q a₀))
        → (x : Σ A (Q a₀)) → P x
      Q-elim a₀ P r x = transport P (contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₀ , refl-Q a₀) x) r 

      Q-elim-β : (a₀ : A) (P : Σ A (Q a₀) → Set)
        → (r : P (a₀ , refl-Q a₀))
        → Q-elim a₀ P r (a₀ , refl-Q a₀) == r
      Q-elim-β a₀ P r = {!!} 

      comp : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
      comp (emp {a₀}) = refl-Q a₀
      comp (ext {a₀} {a₁} {a₂} s r) = Q-elim a₁ P (idf (Q a₀ a₁)) (a₂ , r) (comp s)

        where P : Σ A (Q a₁) → Set
              P (a , _) = Q a₀ a₁ → Q a₀ a

              ih : Q a₀ a₁
              ih = comp s

    module Lcl (Q : UnaryRel) (is-fib-Q : is-fib-unary Q)
             (R : SeqRel Q) (is-fib-R : is-fib-seq R) where
             
      refl-Q : (a : A) → Q a a
      refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

      comp-Q : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
      comp-Q = comp Q refl-Q is-fib-Q

      -- Yeah, so it's clear you can in fact finish this, though
      -- it needs the fibrancy of T.
      R-is-comp : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
      R-is-comp {a₀} {.a₀} emp = snd (contr-center (is-fib-R (emp {Q} {a₀}))) 
      R-is-comp (ext {a₀} {a₁} {a₂} s r) =
        Q-elim Q refl-Q is-fib-Q a₁
          (λ x → R (ext s (snd x))
          (comp-Q (ext s (snd x)))) claim (a₂ , r)

        where by-β : comp-Q (ext s (refl-Q a₁)) == comp-Q s
              by-β = {!Q-elim-β!}

              R-comp : Q a₀ a₁
              R-comp = fst (contr-center (is-fib-R (ext s (refl-Q a₁))))

              R-fill : R (ext s (refl-Q a₁)) R-comp
              R-fill = snd (contr-center (is-fib-R (ext s (refl-Q a₁))))

              by-T-fib : R s R-comp
              by-T-fib = {!!}

              by-ih : R s (comp-Q s)
              by-ih = R-is-comp s 

              thus : comp-Q s == R-comp
              thus = fst= (contr-has-all-paths ⦃ is-fib-R s ⦄ (comp-Q s , by-ih) (R-comp , by-T-fib))
              
              claim : R (ext s (refl-Q a₁)) (comp-Q (ext s (refl-Q a₁)))
              claim = transport! (R (ext s (refl-Q a₁))) (by-β ∙ thus) R-fill  

    module _ {Q : UnaryRel} where

      seqcat : {a₀ a₁ a₂ : A} 
        → seq Q a₀ a₁ → seq Q a₁ a₂
        → seq Q a₀ a₂
      seqcat s emp = s
      seqcat s (ext t r) = ext (seqcat s t) r

      plc : {a₀ a₁ : A} → seq Q a₀ a₁ → Set
      plc emp = ⊥
      plc (ext s r) = plc s ⊔ ⊤

      src : {a₀ a₁ : A} {s : seq Q a₀ a₁} (p : plc s) → A
      src {s = ext s r} (inl p) = src p
      src {s = ext {a₀} {a₁} {a₂} s r} (inr unit) = a₁

      tgt : {a₀ a₁ : A} {s : seq Q a₀ a₁} (p : plc s) → A
      tgt {s = ext s r} (inl p) = tgt p
      tgt {s = ext {a₀} {a₁} {a₂} s r} (inr unit) = a₂

      inh : {a₀ a₁ : A} {s : seq Q a₀ a₁} (p : plc s) → Q (src p) (tgt p)
      inh {s = ext s r} (inl p) = inh p
      inh {s = ext s r} (inr unit) = r

      μ-seq : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → (δ : (p : plc s) → seq Q (src p) (tgt p))
        → seq Q a₀ a₁
      μ-seq emp δ = emp
      μ-seq (ext s r) δ =
        seqcat (μ-seq s (λ p → δ (inl p)))
               (δ (inr unit))
      
      data tr (R : SeqRel Q) : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁ → Set where
        lf-tr : {a₀ a₁ : A} (q : Q a₀ a₁)
          → tr R (ext emp q) q
        nd-tr : {a₀ a₁ : A} (s : seq Q a₀ a₁)
          → (δ : (p : plc s) → seq Q (src p) (tgt p))
          → (ε : (p : plc s) → tr R (δ p) (inh p))
          → (q : Q a₀ a₁) (r : R s q)
          → tr R (μ-seq s δ) q

      TrRel : SeqRel Q → Set₁
      TrRel R = {a₀ a₁ : A} {s : seq Q a₀ a₁} {q : Q a₀ a₁}
        → tr R s q → R s q → Set

      is-fib-tr : (R : SeqRel Q) (T : TrRel R) → Set
      is-fib-tr R T = {a₀ a₁ : A} {s : seq Q a₀ a₁} {q : Q a₀ a₁}
        → (θ : tr R s q) → is-contr (Σ (R s q) (T θ)) 

    module _ (Q : UnaryRel) (is-fib-Q : is-fib-unary Q)
             (R : SeqRel Q) (is-fib-R : is-fib-seq R) where

      refl-Q : (a : A) → Q a a
      refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

      comp-Q : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
      comp-Q = comp Q refl-Q is-fib-Q

      -- What hypotheses do I need on R in order that it has
      -- a composition?
      postulate

        R-unital : {a₀ a₁ : A} (q : Q a₀ a₁)
          → R (ext emp q) q

        R-is-comp : {a₀ a₁ a₂ : A}
          → (s : seq Q a₀ a₁) (r : Q a₁ a₂)
          → R (ext s r) {!!}

      -- R-free : {a₀ a₁ a₂ : A}
      --   → (s₀ : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
      --   → R (seqcat s₀ s₁) (comp-Q (ext (ext emp (comp-Q s₀)) (comp-Q s₁)))
      -- R-free = {!!} 

      R-free : {a₀ a₁ a₂ : A}
        → (s₀ : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
        → R (seqcat s₀ s₁) (comp-Q (ext s₀ (comp-Q s₁)))
      R-free = {!!} 

      R-γ-elim : {a₀ a₁ a₂ : A}
        → (s₀ : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
        → (q : Q a₁ a₂)
        → R s₁ q
        → R (seqcat s₀ s₁) (comp-Q (ext s₀ q))
      R-γ-elim = {!!}
      
      R-inv : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → (δ : (p : plc s) → seq Q (src p) (tgt p))
        -- → (ε : (p : plc s) → tr R (δ p) (inh p))
        → (ε : (p : plc s) → R (δ p) (inh p))
        → R (μ-seq s δ) (comp-Q s)
      R-inv emp δ ε = snd (contr-center (is-fib-R (emp {Q}))) 
      R-inv (ext s r) δ ε =
        let δ' p = δ (inl p)
            ε' p = ε (inl p)
            
            ih : R (μ-seq s δ') (comp-Q s)
            ih = R-inv s δ' ε'
            
            ε-ih : R (δ false) r
            ε-ih = ε false 

            from-γ : R (seqcat (μ-seq s (λ p → δ (inl p))) (δ false))
                     (comp-Q (ext (μ-seq s (λ p → δ (inl p))) (comp-Q (δ false))))
            from-γ = R-free (μ-seq s δ') (δ false)

        in {!R-γ-elim (μ-seq s δ') (δ false) r ε-ih!}


      assoc : {a₀ a₁ : A}
        → {s : seq Q a₀ a₁} {t : Q a₀ a₁}
        → tr R s t
        → R s t
      assoc (lf-tr q) = R-unital q
      assoc (nd-tr s δ ε t r) = {!!}

        -- So, here the idea would be that we can
        -- suppose that t = comp s.  Then we are reduced
        -- to showing that we always have:
        --
        --   R (μ-seq s δ) (comp s)
        --

