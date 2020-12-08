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

  module _ {Q₀ Q₁ : BinRel} (ϕ : {a₀ a₁ : A} → Q₀ a₀ a₁ → Q₁ a₀ a₁) where

    map-seq : {a₀ a₁ : A} → seq Q₀ a₀ a₁ → seq Q₁ a₀ a₁
    map-seq emp = emp
    map-seq (ext s r) = ext (map-seq s) (ϕ r)

  -- The composition relation on the identity type
  module _ where

    id-comp : {a₀ a₁ : A} → seq IdRel a₀ a₁ → a₀ == a₁
    id-comp emp = idp
    id-comp (ext s idp) = id-comp s

    IdCompRel : SeqRel IdRel
    IdCompRel s p = id-comp s == p 


  -- generic composition in a fibrant, reflexive relation
  module BinComp (Q : BinRel) (is-fib-Q : is-fib-bin Q) (refl-Q : is-refl-bin Q) where

    open BinElim Q is-fib-Q refl-Q

    comp-Q : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
    comp-Q (emp {a₀}) = refl-Q a₀
    comp-Q (ext {a₀} {a₁} {a₂} s r) = Bin-elim a₁ P (idf (Q a₀ a₁)) (a₂ , r) (comp-Q s)

      where P : Σ A (Q a₁) → Set
            P (a , _) = Q a₀ a₁ → Q a₀ a

    comp-Q-β : {a₀ a₁ : A} (s : seq Q a₀ a₁)
      → comp-Q (ext s (refl-Q a₁)) == comp-Q s
    comp-Q-β {a₀} {a₁} s = app= (Bin-elim-β a₁ P (idf (Q a₀ a₁))) (comp-Q s) 

      where P : Σ A (Q a₁) → Set
            P (a , _) = Q a₀ a₁ → Q a₀ a

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


  module FtDim2 (Q : BinRel) (is-fib-Q : is-fib-bin Q)
                (R : SeqRel Q) (is-fib-R : is-fib-seq R) where

    refl-Q : (a : A) → Q a a
    refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

    open BinFT Q is-fib-Q refl-Q
    open BinComp Q is-fib-Q refl-Q

    ϕ : {a₀ a₁ : A} → Q a₀ a₁ → IdRel a₀ a₁
    ϕ {a₀} {a₁} = –> (bin-ft a₀ a₁)

    postulate
      
      R-wit : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
      

    R-is-id-comp : {a₀ a₁ : A} (s : seq Q a₀ a₁) (t : Q a₀ a₁)
      → R s t ≃ IdCompRel (map-seq ϕ s) (ϕ t)
    R-is-id-comp s t = R s t                         ≃⟨ {!!} ⟩  -- fibrancy, if R witnesses composition
                       comp-Q s == t                 ≃⟨ {!!} ⟩  -- ϕ is an equivalence
                       ϕ (comp-Q s) == ϕ t           ≃⟨ {!!} ⟩  -- ϕ preserves composition
                       id-comp (map-seq ϕ s) == ϕ t  ≃⟨ {!!} ⟩  -- fibrancy 
                       IdCompRel (map-seq ϕ s) (ϕ t) ≃∎

  record FtDim1Data : Set₁ where
    field

      Q : BinRel
      is-fib-Q : is-fib-bin Q
      refl-Q : (a : A) → Q a a

  record FtDim2Data : Set₁ where
    field

      Q : BinRel
      is-fib-Q : is-fib-bin Q

      R : SeqRel Q
      is-fib-R : is-fib-seq R

    module BC = BinComp Q is-fib-Q (λ a → fst (contr-center (is-fib-R (emp {Q} {a})))) 
    open BC
    
    field
    
      wit-R : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → R s (comp-Q s) 

  postulate
  
    fundamental-thm-dim₂ : is-contr FtDim2Data

  module R-WitnessesComp (Q : BinRel) (is-fib-Q : is-fib-bin Q)
                         (R : SeqRel Q) (is-fib-R : is-fib-seq R) where

    refl-Q : (a : A) → Q a a
    refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

    open BinElim Q is-fib-Q refl-Q
    open BinComp Q is-fib-Q refl-Q

    postulate

      R-unital : {a₀ a₁ : A} (s : seq Q a₀ a₁) (t : Q a₀ a₁)
        → R (ext s (refl-Q a₁)) t
        → R s t 

      -- I mean, you could also just *assert* this.  In this way,
      -- it *is* just data and not any kind of function.
      extreme : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
      -- does this have some kind of nice transfer properties?


      -- I mean, it make sense to me that some *data* on one side
      -- is transformed into some *data* on the other.  But how
      -- does it make sense that an abstract *function* is transformed
      -- to another?
      
      or-maybe : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → R (ext s (refl-Q a₁)) (comp-Q s)


    -- So now I'm wondering what we have as consequences it we
    -- assume extreme.

    R-unit-right : {a₀ a₁ : A} (s : seq Q a₀ a₁)
      → R (ext s (refl-Q a₁)) (comp-Q s)
    R-unit-right {a₀} {a₁} s = transport (R (ext s (refl-Q a₁))) claim (extreme (ext s (refl-Q a₁))) 

      where claim : comp-Q (ext s (refl-Q a₁)) == comp-Q s
            claim = comp-Q-β s

    -- Interesting.  And probably there is more.

    R-concat : {a₀ a₁ a₂ : A} (s : seq Q a₀ a₁) (t : seq Q a₁ a₂)
      → R (seqcat s t) (comp-Q (ext (ext emp (comp-Q s)) (comp-Q t)))
    R-concat s emp = {!!}
    R-concat s (ext t r) = {!!}

    -- Right.  This is some long inductive argument and so on.
    -- but I think you'll be able to carry it out.

    -- Okay, interesting.  So the only thing we seem to need is this
    -- unitality postulate.  And this we are clearly going to get
    -- from the fibrancy in the next dimension.

    -- But what would it mean for this structure to be "transported to"
    -- the cancellation on the identity type? Becase the function is
    -- "abstract".

    R-is-comp : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
    R-is-comp {a₀} {.a₀} emp = snd (contr-center (is-fib-R (emp {Q} {a₀}))) 
    R-is-comp (ext {a₀} {a₁} {a₂} s r) =
      Bin-elim a₁
        (λ x → R (ext s (snd x))
        (comp-Q (ext s (snd x)))) claim (a₂ , r)

      where by-β : comp-Q (ext s (refl-Q a₁)) == comp-Q s
            by-β = comp-Q-β s

            by-ih : R s (comp-Q s)
            by-ih = R-is-comp s 

            R-comp : Q a₀ a₁
            R-comp = fst (contr-center (is-fib-R (ext s (refl-Q a₁))))

            R-fill : R (ext s (refl-Q a₁)) R-comp
            R-fill = snd (contr-center (is-fib-R (ext s (refl-Q a₁))))

            by-T-fib : R s R-comp
            by-T-fib = R-unital s R-comp R-fill 


            thus : comp-Q s == R-comp
            thus = fst= (contr-has-all-paths ⦃ is-fib-R s ⦄ (comp-Q s , by-ih) (R-comp , by-T-fib))

            claim : R (ext s (refl-Q a₁)) (comp-Q (ext s (refl-Q a₁)))
            claim = transport! (R (ext s (refl-Q a₁))) (by-β ∙ thus) R-fill  

    R-is-comp' : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
    R-is-comp' {a₀} {.a₀} emp = snd (contr-center (is-fib-R (emp {Q} {a₀}))) 
    R-is-comp' (ext {a₀} {a₁} {a₂} s r) = 
      Bin-elim a₁
        (λ x → R (ext s (snd x))
        (comp-Q (ext s (snd x)))) need (a₂ , r)

      where by-β : comp-Q (ext s (refl-Q a₁)) == comp-Q s
            by-β = comp-Q-β s

            by-ih : R s (comp-Q s)
            by-ih = R-is-comp' s 

            need : R (ext s (refl-Q a₁)) (comp-Q (ext s (refl-Q a₁)))
            need = {!!}


