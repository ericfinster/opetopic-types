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

    --
    --  Dimension 1 
    --
    
    data _===_ : A → A → Set where
      emp : {a : A} → a === a
      ext : {a₀ a₁ a₂ : A} → a₀ == a₁ → a₁ === a₂ → a₀ === a₂

    comp : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁
    comp emp = idp
    comp (ext p σ) = p ∙ comp σ

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
  
    SeqRel : Set₁
    SeqRel = {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set 

    CompRel : SeqRel
    CompRel σ τ = comp σ == τ 

    is-contr-rel : SeqRel → Set
    is-contr-rel R = {a₀ a₁ : A} (σ : a₀ === a₁)
      → is-contr (Σ (a₀ == a₁) (R σ))  

    is-unital-rel : SeqRel → Set
    is-unital-rel R = (a : A) → R emp (idp {a = a}) 

    is-left-unital : SeqRel → Set
    is-left-unital R = {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
      → R (ext idp σ) τ ≃ R σ τ

    is-compositional : SeqRel → Set
    is-compositional R = {a₀ a₁ a₂ : A} (p : a₀ == a₁)
      → (σ : a₁ === a₂) (τ : a₀ == a₂)
      → R (ext p σ) τ ≃ R σ (! p ∙ τ) 

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

    comp-unique : (R : SeqRel) (ϕ : is-contr-rel R)
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

    data tr : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set where 
      lf-seq : {a₀ a₁ : A} (p : a₀ == a₁)
        → tr (ext p emp) p 
      nd-seq : {a₀ a₁ : A}
        → (σ : a₀ === a₁) (τ : a₀ == a₁)
        → (θ : comp σ == τ)
        → (δ : (p : plc σ) → src p === tgt p)
        → (ε : (p : plc σ) → tr (δ p) (inh p))
        → tr (μ-seq σ δ) τ 

    assoc : {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ)
      → comp σ == τ
    assoc (lf-seq τ) = ∙-unit-r τ
    assoc (nd-seq σ τ θ δ ε) =
      comp-μ σ δ (λ p → assoc (ε p)) ∙ θ
    
    TrRel : SeqRel → Set₁
    TrRel R = {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → tr σ τ → R σ τ → Set 

    is-contr-tr-rel : (T : TrRel CompRel) → Set
    is-contr-tr-rel T = {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ) → is-contr (Σ (comp σ == τ) (T θ)) 

    is-unital-tr-rel : (T : TrRel CompRel) → Set
    is-unital-tr-rel T = {a₀ a₁ : A}
      → (p : a₀ == a₁)
      → T (lf-seq p) (∙-unit-r p)

    tr-div : {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr (δ p) (inh p))
      → (ζ : comp (μ-seq σ δ) == τ)
      → comp σ == τ
    tr-div σ τ δ ε ζ = ! (comp-μ σ δ (λ p → assoc (ε p))) ∙ ζ 

    is-divisible-tr-rel : (T : TrRel CompRel) → Set
    is-divisible-tr-rel T = {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (θ : comp σ == τ)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr (δ p) (inh p))
      → (ζ : comp (μ-seq σ δ) == τ)
      → T (nd-seq σ τ θ δ ε) ζ ≃ (θ == tr-div σ τ δ ε ζ) 

    AssocRel : TrRel CompRel
    AssocRel θ ζ = assoc θ == ζ 

    assoc-is-divisible : is-divisible-tr-rel AssocRel 
    assoc-is-divisible σ τ θ δ ε ζ = goal

      where goal : (comp-μ σ δ (λ p → assoc (ε p)) ∙ θ == ζ) ≃ 
                   (θ == ! (comp-μ σ δ (λ p → assoc (ε p))) ∙ ζ)
            goal = rotate-left-eqv (comp-μ σ δ (λ p → assoc (ε p))) θ ζ
            
    assoc-unique : (T : TrRel CompRel) (ϕ : is-contr-tr-rel T)
      → (ψ : is-unital-tr-rel T) (ρ : is-divisible-tr-rel T)
      → {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ) (ζ : comp σ == τ)
      → T θ ζ ≃ AssocRel θ ζ
    assoc-unique T ϕ ψ ρ (lf-seq τ) ζ =
      fundamental-thm (τ ∙ idp == τ) (T (lf-seq τ)) (∙-unit-r τ) (ψ τ) (ϕ (lf-seq τ)) ζ
    assoc-unique T ϕ ψ ρ (nd-seq σ τ θ δ ε) ζ =
      (assoc-is-divisible σ τ θ δ ε ζ) ⁻¹ ∘e (ρ σ τ θ δ ε ζ)
