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
    comp (ext idp σ) = comp σ

    seqcat : {a₀ a₁ a₂ : A} → a₀ === a₁ → a₁ === a₂ → a₀ === a₂
    seqcat σ₀ emp = σ₀
    seqcat σ₀ (ext idp σ₁) = seqcat σ₀ σ₁

    comp-seqcat : {a₀ a₁ a₂ : A}
      → (p : a₀ === a₁) (q : a₁ === a₂)
      → comp (seqcat p q) == comp p ∙ comp q
    comp-seqcat p emp = ! (∙-unit-r (comp p))
    comp-seqcat p (ext idp q) = comp-seqcat p q
  
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

    comp-unique : (R : SeqRel) (ϕ : is-contr-rel R)
      → (ψ : is-unital-rel R) (ρ : is-left-unital R)
      → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
      → R σ τ ≃ (comp σ == τ) 
    comp-unique R ϕ ψ ρ {a} emp τ =
      fundamental-thm (a == a) (λ p → R emp p) idp (ψ a) (ϕ emp) τ
    comp-unique R ϕ ψ ρ {a₀} {a₁} (ext idp σ) τ =
      (comp-unique R ϕ ψ ρ σ τ) ∘e ρ σ τ

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
      lf-seq : {a₀ a₁ : A} (τ : a₀ == a₁)
        → tr (ext τ emp) τ
      nd-seq : {a₀ a₁ : A} (σ : a₀ === a₁) 
        → (δ : (p : plc σ) → src p === tgt p)
        → (ε : (p : plc σ) → tr (δ p) (inh p))
        → tr (μ-seq σ δ) (comp σ)

    lem₀ : {a₀ a₁ : A} (τ : a₀ == a₁)
      → comp (ext τ emp) == τ
    lem₀ idp = idp

    {-# TERMINATING #-}
    lem₁ : {a₀ a₁ : A} (σ : a₀ === a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr (δ p) (inh p))
      → comp (μ-seq σ δ) == comp σ
    
    interpret : {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr σ τ)
      → comp σ == τ

    interpret (lf-seq τ) = lem₀ τ
    interpret (nd-seq σ δ ε) =
      lem₁ σ δ ε

    lem₁ emp δ ε = idp
    lem₁ (ext idp σ) δ ε =
      let δ' p = δ (inr p)
          ε' p = ε (inr p)
          σ' = μ-seq σ δ'
      in comp-seqcat (δ true) σ' ∙
         ap (λ x → x ∙ comp σ') (interpret (ε true)) ∙
         lem₁ σ δ' ε' 

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
    assoc-unique T ϕ (lf-seq τ) ζ = {!!}
    assoc-unique T ϕ (nd-seq σ δ ε) ζ = {!!}

    -- comp-unique : (R : SeqRel) (ϕ : is-contr-rel R)
    --   → (ψ : is-unital-rel R) (ρ : is-left-unital R)
    --   → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
    --   → R σ τ ≃ (comp σ == τ) 
    -- comp-unique R ϕ ψ ρ {a} emp τ =
    --   fundamental-thm (a == a) (λ p → R emp p) idp (ψ a) (ϕ emp) τ
    -- comp-unique R ϕ ψ ρ {a₀} {a₁} (ext idp σ) τ =
    --   (comp-unique R ϕ ψ ρ σ τ) ∘e ρ σ τ

