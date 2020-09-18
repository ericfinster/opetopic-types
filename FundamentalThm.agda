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

    postulate

      rotate-eqv : {a₀ a₁ a₂ : A}
        → (p : a₀ == a₂) (q : a₁ == a₀) (r : a₁ == a₂)
        → (p == ! q ∙ r) ≃ (q ∙ p == r)
        
    comp-unique : (R : SeqRel) (ϕ : is-contr-rel R)
      → (ψ : is-unital-rel R) (ρ : is-compositional R)
      → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
      → R σ τ ≃ (comp σ == τ)
    comp-unique R ϕ ψ ρ {a} emp τ =
      fundamental-thm (a == a) (λ p → R emp p) idp (ψ a) (ϕ emp) τ
    comp-unique R ϕ ψ ρ (ext p σ) τ =
      rotate-eqv (comp σ) p τ ∘e (comp-unique R ϕ ψ ρ σ (! p ∙ τ)) ∘e (ρ p σ τ)
      
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

    data tr : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set where 
      lf-seq : {a : A} → tr (ext (idp {a = a}) emp) idp
      nd-seq : {a₀ a₁ : A} (σ : a₀ === a₁) 
        → (δ : (p : plc σ) → src p === tgt p)
        → (ε : (p : plc σ) → tr (δ p) (inh p))
        → tr (μ-seq σ δ) (comp σ)

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

    interpret : {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ)
      → comp σ == τ
    interpret lf-seq = idp
    interpret (nd-seq σ δ ε) =
      comp-μ σ δ (λ p → interpret (ε p))

    TrRel : SeqRel → Set₁
    TrRel R = {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → tr σ τ → R σ τ → Set 

    is-contr-tr-rel : (T : TrRel CompRel) → Set
    is-contr-tr-rel T = {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ) → is-contr (Σ (comp σ == τ) (T θ)) 
    
    AssocRel : TrRel CompRel
    AssocRel θ ζ = interpret θ == ζ 

    assoc-unique : (T : TrRel CompRel) (ϕ : is-contr-tr-rel T)
      → {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ) (ζ : comp σ == τ)
      → T θ ζ == AssocRel θ ζ
    assoc-unique T ϕ lf-seq ζ = {!!}
    assoc-unique T ϕ (nd-seq σ δ ε) ζ = {!!}

