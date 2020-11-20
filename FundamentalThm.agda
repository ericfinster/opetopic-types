{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FundamentalThm where

  -- The fundamental theorem of HoTT
  
  fundamental-thm : ∀ {i} (A : Type i) (P : A → Type i)
    → (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P))
    → (a₁ : A) → P a₁ ≃ (a₀ == a₁)
  fundamental-thm A P a₀ r is-c a₁ = equiv to from to-from from-to 

    where to :  P a₁ → a₀ == a₁
          to p = fst= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))

          from : a₀ == a₁ → P a₁
          from p = transport P p r

          to-from : (p : a₀ == a₁) → to (from p) == p
          to-from idp = ap fst= claim

            where claim : contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r) == idp
                  claim = contr-has-all-paths ⦃ =-preserves-contr {x = (a₀ , r)} {y = a₀ , r} is-c ⦄
                            (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r)) idp

          from-to : (p : P a₁) → from (to p) == p
          from-to p = to-transp (snd= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p)))

  --
  --  A couple coherences for later
  --

  rotate-left-eqv : ∀ {i} {A : Set i} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₁) (q : a₁ == a₂) (r : a₀ == a₂)
    → (p ∙ q == r) ≃ (q == ! p ∙ r)
  rotate-left-eqv idp q r = ide (q == r)

  postulate
  
    rotate-right-eqv : ∀ {i} {A : Set i} {a₀ a₁ a₂ : A}
      → (p : a₀ == a₁) (q : a₁ == a₂) (r : a₀ == a₂)
      → (p ∙ q == r) ≃ (p == r ∙ ! q)

  --
  --  Higher dimensional generalizations
  --

  module _ {A : Set} where

    BinRel : Set₁
    BinRel = A → A → Set

    is-fib-bin-rel : BinRel → Set
    is-fib-bin-rel B = (a : A) → is-contr (Σ A (B a))

    eq-is-fib : is-fib-bin-rel _==_
    eq-is-fib a = has-level-in ((a , idp) , contr) 

      where contr : (p : Σ A (_==_ a)) → (a , idp) == p
            contr (a , idp) = idp
            
    --
    --  Dimension 1 
    --
    
    data _===_ : A → A → Set where
      emp : {a : A} → a === a
      ext : {a₀ a₁ a₂ : A} → a₀ == a₁ → a₁ === a₂ → a₀ === a₂

    SeqRel : Set₁
    SeqRel = {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set 

    is-fib-seq-rel : (R : SeqRel) → Set
    is-fib-seq-rel R = {a₀ a₁ : A} (σ : a₀ === a₁)
      → is-contr (Σ (a₀ == a₁) (R σ)) 

    -- The composition relation
    comp : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁
    comp emp = idp
    comp (ext p σ) = p ∙ comp σ

    CompRel : SeqRel
    CompRel σ τ = comp σ == τ 


    seqcat : {a₀ a₁ a₂ : A} → a₀ === a₁ → a₁ === a₂ → a₀ === a₂
    seqcat emp σ₁ = σ₁
    seqcat (ext p σ₀) σ₁ = ext p (seqcat σ₀ σ₁)

    comp-seqcat : {a₀ a₁ a₂ : A}
      → (σ₀ : a₀ === a₁) (σ₁ : a₁ === a₂)
      → comp (seqcat σ₀ σ₁) == comp σ₀ ∙ comp σ₁
    comp-seqcat emp σ₁ = idp
    comp-seqcat (ext p σ₀) σ₁ =
      ap (λ x → p ∙ x) (comp-seqcat σ₀ σ₁) ∙
      ! (∙-assoc p (comp σ₀) (comp σ₁))
  
    is-unital-rel : SeqRel → Set
    is-unital-rel R = (a : A) → R emp (idp {a = a}) 

    div : {a₀ a₁ a₂ : A} (σ : a₁ === a₂) (τ : a₀ == a₂) → a₀ == a₁
    div σ τ = τ ∙ ! (comp σ) 

    is-divisible : SeqRel → Set
    is-divisible R = {a₀ a₁ a₂ : A} (p : a₀ == a₁)
      → (σ : a₁ === a₂) (τ : a₀ == a₂)
      → R (ext p σ) τ ≃ (p == div σ τ)

    comp-divisible : is-divisible CompRel
    comp-divisible p σ τ = goal

      where goal : (p ∙ comp σ == τ) ≃ (p == τ ∙ ! (comp σ) )
            goal = rotate-right-eqv p (comp σ) τ 

    comp-unique : (R : SeqRel) (ϕ : is-fib-seq-rel R)
      → (ψ : is-unital-rel R) (ρ : is-divisible R)
      → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
      → R σ τ ≃ (comp σ == τ)
    comp-unique R ϕ ψ ρ {a} emp τ =
      fundamental-thm (a == a) (λ p → R emp p) idp (ψ a) (ϕ emp) τ
    comp-unique R ϕ ψ ρ (ext p σ) τ =
      (comp-divisible p σ τ) ⁻¹ ∘e (ρ p σ τ)
      
    --
    --  Dimension 2
    -- 

    plc : {a₀ a₁ : A} → a₀ === a₁ → Set
    plc emp = ⊥
    plc (ext _ σ) = ⊤ ⊔ plc σ

    src : {a₀ a₁ : A} {σ : a₀ === a₁} (p : plc σ) → A
    src {σ = ext {a₀} _ _} (inl unit) = a₀
    src {σ = ext {a₀} _ σ} (inr p) = src p

    tgt : {a₀ a₁ : A} {σ : a₀ === a₁} (p : plc σ) → A
    tgt {σ = ext {a₁ = a₁} _ _} (inl unit) = a₁
    tgt {σ = ext _ _} (inr p) = tgt p

    inh : {a₀ a₁ : A} {σ : a₀ === a₁} (p : plc σ) → src p == tgt p
    inh {σ = ext x _} (inl unit) = x
    inh {σ = ext _ σ} (inr p) = inh p

    μ-seq : {a₀ a₁ : A} (σ : a₀ === a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → a₀ === a₁
    μ-seq emp δ = emp
    μ-seq (ext _ σ) δ =
      seqcat (δ (inl unit))
             (μ-seq σ (λ p → δ (inr p)))

    data tr (R : SeqRel) : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set where
      lf-tr : {a₀ a₁ : A} (p : a₀ == a₁)
        → tr R (ext p emp) p
      nd-tr : {a₀ a₁ : A}
        → (σ : a₀ === a₁) (τ : a₀ == a₁)
        → (r : R σ τ)
        → (δ : (p : plc σ) → src p === tgt p)
        → (ε : (p : plc σ) → tr R (δ p) (inh p))
        → tr R (μ-seq σ δ) τ 
    
    TrRel : SeqRel → Set₁
    TrRel R = {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → tr R σ τ → R σ τ → Set 

    is-fib-tr-rel : (R : SeqRel) (S : TrRel R) → Set
    is-fib-tr-rel R T = {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr R σ τ) → is-contr (Σ (R σ τ) (T θ)) 

    -- The associative relation
    comp-μ : {a₀ a₁ : A} (σ : a₀ === a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → comp (δ p) == (inh p))
      → comp (μ-seq σ δ) == comp σ
    comp-μ emp δ ε = idp
    comp-μ (ext p σ) δ ε = 
      let δ' p = δ (inr p)
          ε' p = ε (inr p)
          σ' = μ-seq σ δ'
      in comp-seqcat (δ true) σ' ∙ ε true ∙2 comp-μ σ δ' ε'

    assoc : {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr CompRel σ τ)
      → comp σ == τ
    assoc (lf-tr τ) = ∙-unit-r τ
    assoc (nd-tr σ τ θ δ ε) =
      comp-μ σ δ (λ p → assoc (ε p)) ∙ θ

    AssocRel : TrRel CompRel
    AssocRel θ ζ = assoc θ == ζ 

    is-unital-tr-rel : (T : TrRel CompRel) → Set
    is-unital-tr-rel T = {a₀ a₁ : A}
      → (p : a₀ == a₁)
      → T (lf-tr p) (∙-unit-r p)

    tr-div : {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr CompRel (δ p) (inh p))
      → (ζ : comp (μ-seq σ δ) == τ)
      → comp σ == τ
    tr-div σ τ δ ε ζ = ! (comp-μ σ δ (λ p → assoc (ε p))) ∙ ζ 

    is-divisible-tr-rel : (T : TrRel CompRel) → Set
    is-divisible-tr-rel T = {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (θ : comp σ == τ)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr CompRel (δ p) (inh p))
      → (ζ : comp (μ-seq σ δ) == τ)
      → T (nd-tr σ τ θ δ ε) ζ ≃ (θ == tr-div σ τ δ ε ζ) 

    assoc-is-divisible : is-divisible-tr-rel AssocRel 
    assoc-is-divisible σ τ θ δ ε ζ = goal

      where goal : (comp-μ σ δ (λ p → assoc (ε p)) ∙ θ == ζ) ≃ 
                   (θ == ! (comp-μ σ δ (λ p → assoc (ε p))) ∙ ζ)
            goal = rotate-left-eqv (comp-μ σ δ (λ p → assoc (ε p))) θ ζ
            
    assoc-unique : (T : TrRel CompRel) (ϕ : is-fib-tr-rel CompRel T)
      → (ψ : is-unital-tr-rel T) (ρ : is-divisible-tr-rel T)
      → {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr CompRel σ τ) (ζ : comp σ == τ)
      → T θ ζ ≃ AssocRel θ ζ
    assoc-unique T ϕ ψ ρ (lf-tr τ) ζ =
      fundamental-thm (τ ∙ idp == τ) (T (lf-tr τ)) (∙-unit-r τ) (ψ τ) (ϕ (lf-tr τ)) ζ
    assoc-unique T ϕ ψ ρ (nd-tr σ τ θ δ ε) ζ =
      (assoc-is-divisible σ τ θ δ ε ζ) ⁻¹ ∘e (ρ σ τ θ δ ε ζ)

    module _ (R : SeqRel) (S : TrRel R) 
             (is-fib-R : is-fib-seq-rel R)
             (is-fib-S : is-fib-tr-rel R S) where

      postulate
      
        -- This form is general, I think, although the path
        -- you transport along will come from what happens when
        -- you project off the target equality from the fibrancy
        -- of the previous.
        can-assume : {a₀ a₁ a₂ : A}
          → (p : a₀ == a₁) (σ : a₁ === a₂)
          → (τ : a₀ == a₂)
          → R (ext p σ) τ ≃ R (ext idp σ) (transport (λ x → x == a₂) p τ)  
        -- The point is, this is just the transport equivalence induced
        -- by the fact that the *previous* guy was fibrant.


      completeness : Set
      completeness = {a₀ a₁ a₂ : A}
        → (p : a₀ == a₁) (q : a₀ == a₂)
        → ((a₁ , p) == (a₂ , q)) ≃ Σ (a₁ == a₂) (λ r → R (ext p (ext r emp)) q)

      -- So, is there a map in one direction or the other?
      completeness-map : (is-unital-R : is-unital-rel R)
        → {a₀ a₁ a₂ : A}
        → (p : a₀ == a₁) (q : a₀ == a₂)
        → ((a₁ , p) == (a₂ , q)) → Σ (a₁ == a₂) (λ r → R (ext p (ext r emp)) q)
      completeness-map is-u-R p .p idp = idp , {!!}

      emp-tr : {a : A} (p : a == a) (r : R emp p) → tr R emp p
      emp-tr p r = nd-tr emp p r (λ { () }) (λ { () })

      -- Wow, this I find at least somewhat surprising, but okay.
      completeness-inv : (is-u-R : is-unital-rel R)
        → {a₀ a₁ a₂ : A}
        → (p : a₀ == a₁) (q : a₀ == a₂)
        → Σ (a₁ == a₂) (λ r → R (ext p (ext r emp)) q) → ((a₁ , p) == (a₂ , q))
      completeness-inv is-u-R {a₁ = a₁} p q (idp , r) = pair= idp (fst= (contr-has-all-paths ⦃ is-fib-R (ext p emp) ⦄ (p , blorp) (q , bleep)))

        where blorp : R (ext p emp) p
              blorp = fst (contr-center (is-fib-S (lf-tr p)))  

              bleep : R (ext p emp) q
              bleep = fst (contr-center (is-fib-S (nd-tr (ext p (ext idp emp)) q r
                          (λ { true → ext p emp ;
                               (inr true) → emp })
                          λ { true → lf-tr p ;
                              (inr true) → emp-tr idp (is-u-R a₁) }))) 

      -- Now, if we assume completeness, I think I can prove that R
      -- has left liftings.  On the other hand, it looks like if I
      -- knew that *S* has left liftings, then I would actually be
      -- able to prove completeness.  Not sure what to make of that....

      -- On the other hand, can I now just prove directly that R agrees
      -- with composition? 

      thm : (is-u-R : is-unital-rel R) 
        → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
        → R σ τ ≃ CompRel σ τ 
      thm is-u-R {a₀} emp τ = {!!}  -- This is fundamental theorem non-sense
      thm is-u-R (ext idp σ) τ = comp-case

        where R-tr : R (ext idp σ) τ → tr R σ τ
              R-tr r = {!!} 

                -- (nd-tr (ext idp σ) τ r
                --           (λ { true → emp ; 
                --                (inl p) → ? })
                --           λ { true → emp-tr idp (is-u-R _) ;
                --               (inr p) → ? })

              suffices-to : R (ext idp σ) τ → R σ τ 
              suffices-to r = fst (contr-center (is-fib-S (R-tr r)))

              suffices-from : R σ τ → R (ext idp σ) τ
              suffices-from = {!!}
              
              suffices : R (ext idp σ) τ ≃ R σ τ 
              suffices = {!!}
              
              comp-case : R (ext idp σ) τ ≃ (comp σ == τ)
              comp-case = (thm is-u-R σ τ) ∘e {!!} 

      -- Okay, it's a bit annoying because of some non-computation, but
      -- it seems that this is going to work fine, yeah? Oh one direction
      -- will just use the unit, but the other will use either completeness
      -- or else the lifting property of S.  Which, by the way, suggests that
      -- these two properties are equivalent.

      -- Hmm. Okay.  So while it's true that this will work, it won't
      -- generalize: in the next dimension, you won't be able to just
      -- compose with this nullifying tree to get what you want.


      -- -- is-fib-bin-rel : BinRel → Set
      -- -- is-fib-bin-rel B = (a : A) → is-contr (Σ A (B a))

      -- -- data tr (R : SeqRel) : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set where
      -- --   lf-tr : {a₀ a₁ : A} (p : a₀ == a₁)
      -- --     → tr R (ext p emp) p
      -- --   nd-tr : {a₀ a₁ : A}
      -- --     → (σ : a₀ === a₁) (τ : a₀ == a₁)
      -- --     → (r : R σ τ)
      -- --     → (δ : (p : plc σ) → src p === tgt p)
      -- --     → (ε : (p : plc σ) → tr R (δ p) (inh p))
      -- --     → tr R (μ-seq σ δ) τ 

      -- -- TrRel : SeqRel → Set₁
      -- -- TrRel R = {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      -- --   → tr R σ τ → R σ τ → Set 

      -- -- is-fib-seq-rel : (R : SeqRel) → Set
      -- -- is-fib-seq-rel R = {a₀ a₁ : A} (σ : a₀ === a₁)
      -- --   → is-contr (Σ (a₀ == a₁) (R σ)) 

      -- -- is-unital-rel : SeqRel → Set
      -- -- is-unital-rel R = (a : A) → R emp (idp {a = a}) 

      -- -- div : {a₀ a₁ a₂ : A} (σ : a₁ === a₂) (τ : a₀ == a₂) → a₀ == a₁
      -- -- div σ τ = τ ∙ ! (comp σ) 

      -- -- is-divisible : SeqRel → Set
      -- -- is-divisible R = {a₀ a₁ a₂ : A} (p : a₀ == a₁)
      -- --   → (σ : a₁ === a₂) (τ : a₀ == a₂)
      -- --   → R (ext p σ) τ ≃ (p == div σ τ)

