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
    module _ (Q : UnaryRel) (is-unital-Q : (a : A) → Q a a) (is-fib-Q : is-fib-unary Q) where

      comp : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
      comp (emp {a₀}) = is-unital-Q a₀
      comp (ext {a₀} {a₁} {a₂} s r) = transport! (Q a₀) p (comp s)

        where p : a₂ ==  a₁
              p = fst= (contr-has-all-paths ⦃ is-fib-Q a₁ ⦄ (a₂ , r) (a₁ , is-unital-Q a₁)) 

      Q-elim' : (a₀ : A) (P : Σ A (Q a₀) → Set)
        → (r : P (a₀ , is-unital-Q a₀))
        → (x : Σ A (Q a₀)) → P x
      Q-elim' a₀ P r x = transport P (contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₀ , is-unital-Q a₀) x) r 

      Q-elim : (P : {a₀ a₁ : A} → Q a₀ a₁ → Set)
        → (r : (a : A) → P (is-unital-Q a))
        → {a₀ a₁ : A} (q : Q a₀ a₁) → P q
      Q-elim P r {a₀} {a₁} q = transport! P' pth r'

        where pth : (a₁ , q) == (a₀ , is-unital-Q a₀)
              pth = contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₁ , q) (a₀ , is-unital-Q a₀)

              P' : Σ A (Q a₀) → Set
              P' x = P (snd x) 

              r' : P' (a₀ , is-unital-Q a₀)
              r' = r a₀ 

    module _ (Q : UnaryRel) (is-fib-Q : is-fib-unary Q)
             (R : SeqRel Q) (is-fib-R : is-fib-seq R) where
             
      is-unital-Q : (a : A) → Q a a
      is-unital-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

      comp-Q : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
      comp-Q = comp Q is-unital-Q is-fib-Q

      -- Yeah, so it's clear you can in fact finish this, though
      -- it needs the fibrancy of T.
      R-is-comp : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
      R-is-comp {a₀} {.a₀} emp = snd (contr-center (is-fib-R (emp {Q} {a₀}))) 
      R-is-comp (ext {a₀} {a₁} {a₂} s r) =
        Q-elim' Q is-unital-Q is-fib-Q a₁
          (λ x → R (ext s (snd x))
          (comp-Q (ext s (snd x)))) claim (a₂ , r)

        where by-β : (comp-Q (ext s (is-unital-Q a₁))) == comp-Q s
              by-β = {!!}

              R-comp : Q a₀ a₁
              R-comp = fst (contr-center (is-fib-R (ext s (is-unital-Q a₁))))

              R-fill : R (ext s (is-unital-Q a₁)) R-comp
              R-fill = snd (contr-center (is-fib-R (ext s (is-unital-Q a₁))))

              by-T-fib : R s R-comp
              by-T-fib = {!!}

              by-ih : R s (comp-Q s)
              by-ih = R-is-comp s 

              thus : comp-Q s == R-comp
              thus = fst= (contr-has-all-paths ⦃ is-fib-R s ⦄ (comp-Q s , by-ih) (R-comp , by-T-fib))
              
              claim : R (ext s (is-unital-Q a₁)) (comp-Q (ext s (is-unital-Q a₁)))
              claim = transport! (R (ext s (is-unital-Q a₁))) (by-β ∙ thus) R-fill  

      -- Right.  So by "Q id-elim" it suffices to consider r = refl.
      -- In this case, we should be able to show, from the induction
      -- hypothesis and fibrancy that there is a cell from the
      -- extension with the identity back to the composition of the
      -- sequence.

      -- It seems this would use the fibrancy of T, right?

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
             (R : SeqRel Q) (is-fib-R : is-fib-seq R)
             (T : TrRel R) (is-fib-T : is-fib-tr R T) where

      R-divisible : Set
      R-divisible = {a₀ a₁ : A} (s : seq Q a₀ a₁)
          → (δ : (p : plc s) → seq Q (src p) (tgt p))
          → (ε : (p : plc s) → tr R (δ p) (inh p))
          → (q : Q a₀ a₁)
          → (back : R (μ-seq s δ) q)
          → is-contr (Σ (R s q) (λ r → T (nd-tr s δ ε q r) back))

      -- So this looks excellent.  It appears I can just directly show
      -- that R is divisible.  I'm a bit surprised, but hey, why not.
      -- (Although you still have to show uniqueness...)
      
      conjecture : R-divisible
      conjecture {a₀} {a₁} s δ ε q back = has-level-in ((tr-lift , tr-wit) , {!!}) 

        where cmp : Q a₀ a₁
              cmp = fst (contr-center (is-fib-R s))

              fill : R s cmp
              fill = snd (contr-center (is-fib-R s)) 

              ext-tr : tr R (μ-seq s δ) cmp
              ext-tr = nd-tr s δ ε cmp fill
              
              competitor : R (μ-seq s δ) cmp
              competitor = fst (contr-center (is-fib-T ext-tr))

              by-fibrancy : (cmp , competitor) == (q , back)
              by-fibrancy = (contr-has-all-paths ⦃ is-fib-R (μ-seq s δ) ⦄ (cmp , competitor) (q , back))

              thus : cmp == q
              thus = fst= by-fibrancy

              tr-lift : R s q
              tr-lift = transport (R s) thus fill 

              we-have : T (nd-tr s δ ε cmp fill) competitor
              we-have = snd (contr-center (is-fib-T ext-tr)) 

              -- Great.  So now this is just a kind of funky tranpsort
              -- where I use the path over from the definition and the
              -- one from by-fibrancy simultaneously.
              
              tr-wit : T (nd-tr s δ ε q tr-lift) back
              tr-wit = {!snd (contr-center (is-fib-T ext-tr))!} 



      refl : (a : A) → Q a a
      refl a = fst (contr-center (is-fib-R emp)) 

      blorp : {a₀ a₁ a₂ : A} 
        → (s : seq Q a₀ a₁) (u : Q a₁ a₂)  (t : Q a₀ a₂)
        → R (ext s u) t ≃ R (ext s (snd (contr-center (is-fib-Q a₁))))
          (transport! (Q a₀) (fst= (contr-path (is-fib-Q a₁) (a₂ , u))) t)
      blorp s u t = {!!} 

      -- Hmmm.  But oddly, this doesn't actually use the fibrancy of V
      -- like I would have expected.  Still, it's something to keep
      -- in mind.  What *would* use the fibrancy of V?

      -- Anyway, the point is to observe that I can assume WLOG that
      -- either the target, or the exposed node is in fact the
      -- composite with respect to the previous relation.

      -- I still don't quite see how this helps ....

      -- I'd like to try to formalize the idea that "R is Q complete"
      -- What does this mean?

      div : {a₀ a₁ a₂ : A} (p : Q a₀ a₁) (q : Q a₀ a₂)
        → Q a₁ a₂
      div {a₀} {a₁} {a₂} p q = transport (λ x → Q x a₂) claim q 

        where claim : a₀ == a₁
              claim = fst= (contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₀ , refl a₀) (a₁ , p)) 
              
      wit : {a₀ a₁ a₂ : A} (p : Q a₀ a₁) (q : Q a₀ a₂)
        → R (ext (ext emp p) (div p q)) q
      wit = {!!}

      -- Yeah, okay, so this seems possible.  So will this generalize
      -- geometrically speaking? I mean, I think so.  Should we try it?
