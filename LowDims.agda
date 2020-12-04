{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import FundamentalThm

module LowDims (A : Set) where

  BinRel : Set₁
  BinRel = A → A → Set 

  is-fib-bin : BinRel → Set
  is-fib-bin Q = (a₀ : A) → is-contr (Σ A (λ a₁ → Q a₀ a₁))

  is-refl-bin : BinRel → Set
  is-refl-bin Q = (a : A) → Q a a

  IdRel : BinRel
  IdRel = _==_
  
  module BinElim (Q : BinRel) (is-fib-Q : is-fib-bin Q) (refl-Q : is-refl-bin Q) where

    Bin-elim : (a₀ : A) (P : Σ A (Q a₀) → Set)
      → (r : P (a₀ , refl-Q a₀))
      → (x : Σ A (Q a₀)) → P x
    Bin-elim a₀ P r x = transport P (contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₀ , refl-Q a₀) x) r 

    Bin-elim-β : (a₀ : A) (P : Σ A (Q a₀) → Set)
      → (r : P (a₀ , refl-Q a₀))
      → Bin-elim a₀ P r (a₀ , refl-Q a₀) == r
    Bin-elim-β a₀ P r = ap (λ x → transport P x r) claim
    
      where pth : (a₀ , refl-Q a₀) == (a₀ , refl-Q a₀)
            pth = contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₀ , refl-Q a₀) (a₀ , refl-Q a₀)

            claim : pth == idp
            claim = contr-has-all-paths ⦃ has-level-apply (contr-has-level {n = S ⟨-2⟩} (is-fib-Q a₀))
                                          (a₀ , refl-Q a₀) (a₀ , refl-Q a₀) ⦄ pth idp 


  module BinFT (Q : BinRel) (is-fib-Q : is-fib-bin Q) (refl-Q : is-refl-bin Q) where

    bin-ft : (a₀ a₁ : A) → Q a₀ a₁ ≃ (a₀ == a₁)
    bin-ft a₀ a₁ = fundamental-thm A (Q a₀) (is-fib-Q a₀) a₀ (refl-Q a₀) a₁

    bin-coh : (a : A) → –> (bin-ft a a) (refl-Q a) == idp
    bin-coh a = fundamental-thm-β A (Q a) (is-fib-Q a) a (refl-Q a)

  --
  --  Sequences
  --
  
  data seq (Q : BinRel) : A → A → Set where
    emp : {a : A} → seq Q a a
    ext : {a₀ a₁ a₂ : A}
      → (s : seq Q a₀ a₁) (r : Q a₁ a₂) 
      → seq Q a₀ a₂

  SeqRel : BinRel → Set₁
  SeqRel Q = {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁ → Set 

  module _ {Q : BinRel} where
      
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


    is-fib-seq : SeqRel Q → Set
    is-fib-seq R = {a₀ a₁ : A} (σ : seq Q a₀ a₁)
       → is-contr (Σ (Q a₀ a₁) (R σ)) 

    -- The analog of "subdivision invariance"
    is-invar-rel : SeqRel Q → Set
    is-invar-rel R = {a₀ a₁ : A} (s : seq Q a₀ a₁) (t : Q a₀ a₁)
      → (δ : (p : plc s) → seq Q (src p) (tgt p))
      → (ε : (p : plc s) → R (δ p) (inh p))
      → (r : R s t)
      → R (μ-seq s δ) t

  -- The composition relation on the identity type
  module IdCompRel where

    id-comp : {a₀ a₁ : A} → seq IdRel a₀ a₁ → a₀ == a₁
    id-comp emp = idp
    id-comp (ext s idp) = id-comp s

    IdCompRel : SeqRel IdRel
    IdCompRel s p = id-comp s == p 

  module _ {Q : BinRel} (R : SeqRel Q) where

    data tr : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁ → Set where
      lf-tr : {a₀ a₁ : A} (q : Q a₀ a₁)
        → tr (ext emp q) q
      nd-tr : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → (δ : (p : plc s) → seq Q (src p) (tgt p))
        → (ε : (p : plc s) → tr (δ p) (inh p))
        → (q : Q a₀ a₁) (r : R s q)
        → tr (μ-seq s δ) q

    TrRel : Set₁
    TrRel = {a₀ a₁ : A} {s : seq Q a₀ a₁} {q : Q a₀ a₁}
      → tr s q → R s q → Set

    is-fib-tr : TrRel → Set
    is-fib-tr T = {a₀ a₁ : A} {s : seq Q a₀ a₁} {q : Q a₀ a₁}
      → (θ : tr s q) → is-contr (Σ (R s q) (T θ)) 


  module _ (Q : BinRel) (is-fib-Q : is-fib-bin Q)
           (R : SeqRel Q) (is-fib-R : is-fib-seq R) where

    -- So, the question is, what additional data can I add to
    -- the hypotheses so that the space of such data becomes
    -- contractible?


  -- --  Showing that a fibrant, unital relation admits a composition
  -- module _ (Q : BinRel) (refl-Q : (a : A) → Q a a) (is-fib-Q : is-fib-unary Q) where

  --   comp : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
  --   comp (emp {a₀}) = refl-Q a₀
  --   comp (ext {a₀} {a₁} {a₂} s r) = Q-elim a₁ P (idf (Q a₀ a₁)) (a₂ , r) (comp s)

  --     where P : Σ A (Q a₁) → Set
  --           P (a , _) = Q a₀ a₁ → Q a₀ a

  --   comp-β : {a₀ a₁ : A} (s : seq Q a₀ a₁)
  --     → comp (ext s (refl-Q a₁)) == comp s
  --   comp-β {a₀} {a₁} s = app= (Q-elim-β a₁ P (idf (Q a₀ a₁))) (comp s) 

  --     where P : Σ A (Q a₁) → Set
  --           P (a , _) = Q a₀ a₁ → Q a₀ a

  -- module R-WitnessesComp (Q : BinRel) (is-fib-Q : is-fib-unary Q)
  --                        (R : SeqRel Q) (is-fib-R : is-fib-seq R)
  --                        (T : TrRel R) (is-fib-T : is-fib-tr T) where

  --   refl-Q : (a : A) → Q a a
  --   refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

  --   comp-Q : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
  --   comp-Q = comp Q refl-Q is-fib-Q

  --   -- Yeah, so it's clear you can in fact finish this, though
  --   -- it needs the fibrancy of T.
  --   R-is-comp : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
  --   R-is-comp {a₀} {.a₀} emp = snd (contr-center (is-fib-R (emp {Q} {a₀}))) 
  --   R-is-comp (ext {a₀} {a₁} {a₂} s r) =
  --     Q-elim Q refl-Q is-fib-Q a₁
  --       (λ x → R (ext s (snd x))
  --       (comp-Q (ext s (snd x)))) claim (a₂ , r)

  --     where by-β : comp-Q (ext s (refl-Q a₁)) == comp-Q s
  --           by-β = comp-β Q refl-Q is-fib-Q s

  --           R-comp : Q a₀ a₁
  --           R-comp = fst (contr-center (is-fib-R (ext s (refl-Q a₁))))

  --           R-fill : R (ext s (refl-Q a₁)) R-comp
  --           R-fill = snd (contr-center (is-fib-R (ext s (refl-Q a₁))))

  --           -- Oh.  We need a bit of definitional equality here
  --           -- in order to write this tree.
  --           r-tr : tr R s R-comp
  --           r-tr = nd-tr {!ext s (refl-Q a₁)!} {!!} {!!} {!!} {!!} 

  --           by-T-fib : R s R-comp
  --           by-T-fib = fst (contr-center (is-fib-T r-tr))

  --           by-ih : R s (comp-Q s)
  --           by-ih = R-is-comp s 

  --           thus : comp-Q s == R-comp
  --           thus = fst= (contr-has-all-paths ⦃ is-fib-R s ⦄ (comp-Q s , by-ih) (R-comp , by-T-fib))

  --           claim : R (ext s (refl-Q a₁)) (comp-Q (ext s (refl-Q a₁)))
  --           claim = transport! (R (ext s (refl-Q a₁))) (by-β ∙ thus) R-fill  


  -- module _ (Q : BinRel) (is-fib-Q : is-fib-unary Q)
  --          (R : SeqRel Q) (is-fib-R : is-fib-seq R) where

  --   refl-Q : (a : A) → Q a a
  --   refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

  --   comp-Q : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
  --   comp-Q = comp Q refl-Q is-fib-Q

  --   -- What hypotheses do I need on R in order that it has
  --   -- a composition?
  --   postulate

  --     R-unital : {a₀ a₁ : A} (q : Q a₀ a₁)
  --       → R (ext emp q) q

  --     R-is-comp : {a₀ a₁ a₂ : A}
  --       → (s : seq Q a₀ a₁) (r : Q a₁ a₂)
  --       → R (ext s r) {!comp-Q s!}

  --   -- R-free : {a₀ a₁ a₂ : A}
  --   --   → (s₀ : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
  --   --   → R (seqcat s₀ s₁) (comp-Q (ext (ext emp (comp-Q s₀)) (comp-Q s₁)))
  --   -- R-free = {!!} 

  --   R-free : {a₀ a₁ a₂ : A}
  --     → (s₀ : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
  --     → R (seqcat s₀ s₁) (comp-Q (ext s₀ (comp-Q s₁)))
  --   R-free = {!!} 

  --   R-γ-elim : {a₀ a₁ a₂ : A}
  --     → (s₀ : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
  --     → (q : Q a₁ a₂)
  --     → R s₁ q
  --     → R (seqcat s₀ s₁) (comp-Q (ext s₀ q))
  --   R-γ-elim = {!!}

  --   R-inv : {a₀ a₁ : A} (s : seq Q a₀ a₁)
  --     → (δ : (p : plc s) → seq Q (src p) (tgt p))
  --     -- → (ε : (p : plc s) → tr R (δ p) (inh p))
  --     → (ε : (p : plc s) → R (δ p) (inh p))
  --     → R (μ-seq s δ) (comp-Q s)
  --   R-inv emp δ ε = snd (contr-center (is-fib-R (emp {Q}))) 
  --   R-inv (ext s r) δ ε =
  --     let δ' p = δ (inl p)
  --         ε' p = ε (inl p)

  --         ih : R (μ-seq s δ') (comp-Q s)
  --         ih = R-inv s δ' ε'

  --         ε-ih : R (δ false) r
  --         ε-ih = ε false 

  --         from-γ : R (seqcat (μ-seq s (λ p → δ (inl p))) (δ false))
  --                  (comp-Q (ext (μ-seq s (λ p → δ (inl p))) (comp-Q (δ false))))
  --         from-γ = R-free (μ-seq s δ') (δ false)

  --     in {!R-γ-elim (μ-seq s δ') (δ false) r ε-ih!}


  --   assoc : {a₀ a₁ : A}
  --     → {s : seq Q a₀ a₁} {t : Q a₀ a₁}
  --     → tr R s t
  --     → R s t
  --   assoc (lf-tr q) = R-unital q
  --   assoc (nd-tr s δ ε t r) = {!!}

  --     -- Oh.  So I can clearly suppose that t = the fibrant composite
  --     -- of R.  But actually, in order to show this is comp S, I need
  --     -- T itself in a non-trivial way.

  --     -- So, here the idea would be that we can
  --     -- suppose that t = comp s.  Then we are reduced
  --     -- to showing that we always have:
  --     --
  --     --   R (μ-seq s δ) (comp s)
  --     --

