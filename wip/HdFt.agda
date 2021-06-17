{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import FundamentalThm

module HdFt where

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
             (is-unital-R : is-unital-rel R)
             
             (is-fib-R : is-fib-seq-rel R)
             (is-fib-S : is-fib-tr-rel R S) where

      postulate

        R-compatible : {a₀ a₁ a₂ : A}
          → (r : a₀ == a₁) (s : a₁ === a₂) 
          → R (ext r s) (r ∙ comp s)

      thm : {a₀ a₁ : A}
          → (s : a₀ === a₁) (r : a₀ == a₁)
          → R s r ≃ CompRel s r
      thm emp r = {!!}
      thm (ext p s) r = {!!}


