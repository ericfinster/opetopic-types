{-# OPTIONS --without-K --rewriting #-}

open import Base

module OpetopicType where

  postulate

    𝕄 : Set

    Frm : 𝕄 → Set
    Cell : (M : 𝕄) (f : Frm M) → Set
    Tree : (M : 𝕄) (f : Frm M) → Set

    Pos : (M : 𝕄) {f : Frm M}
      → Tree M f → Set

    Typ : (M : 𝕄) {f : Frm M}
      → (σ : Tree M f) (p : Pos M σ)
      → Frm M 

    Inh : (M : 𝕄) {f : Frm M}
      → (σ : Tree M f) (p : Pos M σ)
      → Cell M (Typ M σ p)

    η : (M : 𝕄) {f : Frm M}
      → Cell M f → Tree M f

    η-pos : (M : 𝕄) {f : Frm M}
      → (τ : Cell M f) → Pos M (η M τ)

    η-pos-elim : (M : 𝕄) {f : Frm M} (τ : Cell M f)
      → (X : (p : Pos M (η M τ)) → Set)
      → (η-pos* : X (η-pos M τ))
      → (p : Pos M (η M τ)) → X p

    μ : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → Tree M f

    μ-pos : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M σ) (q : Pos M (δ p))
      → Pos M (μ M σ δ)

    μ-pos-fst : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → Pos M (μ M σ δ) → Pos M σ

    μ-pos-snd : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M (μ M σ δ))
      → Pos M (δ (μ-pos-fst M σ δ p))
      
    --
    --  Stict laws
    --

    -- Typ/Inh laws
    η-pos-typ : (M : 𝕄) (f : Frm M)
      → (τ : Cell M f) (p : Pos M (η M τ))
      → Typ M (η M τ) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : (M : 𝕄) (f : Frm M)
      → (τ : Cell M f) (p : Pos M (η M τ))
      → Inh M (η M τ) p ↦ τ
    {-# REWRITE η-pos-inh #-}

    η-pos-elim-β : (M : 𝕄) {f : Frm M} (τ : Cell M f)
      → (X : (p : Pos M (η M τ)) → Set)
      → (η-pos* : X (η-pos M τ))
      → η-pos-elim M τ X η-pos* (η-pos M τ) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-typ : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M (μ M σ δ))
      → Typ M (μ M σ δ) p ↦ Typ M (δ (μ-pos-fst M σ δ p)) (μ-pos-snd M σ δ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M (μ M σ δ))
      → Inh M (μ M σ δ) p ↦ Inh M (δ (μ-pos-fst M σ δ p)) (μ-pos-snd M σ δ p)
    {-# REWRITE μ-pos-inh #-}

    μ-pos-fst-β : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M σ) (q : Pos M (δ p))
      → μ-pos-fst M σ δ (μ-pos M σ δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M σ) (q : Pos M (δ p))
      → μ-pos-snd M σ δ (μ-pos M σ δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}
    
    μ-pos-η : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M (μ M σ δ))
      → μ-pos M σ δ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p) ↦ p
    {-# REWRITE μ-pos-η #-}
    
    -- μ laws
    μ-unit-right : (M : 𝕄) (f : Frm M)
      → (σ : Tree M f)
      → μ M σ (λ p → η M (Inh M σ p)) ↦ σ
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : (M : 𝕄) (f : Frm M) (τ : Cell M f)
      → (δ : (p : Pos M (η M τ)) → Tree M f)
      → μ M (η M τ) δ ↦ δ (η-pos M τ)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M (μ M σ δ)) → Tree M (Typ M (μ M σ δ) p))
      → μ M (μ M σ δ) ε ↦ μ M σ (λ p → μ M (δ p) (λ q → ε (μ-pos M σ δ p q)))
    {-# REWRITE μ-assoc #-}

  Filler : (M : 𝕄) → Set₁
  Filler M = {f : Frm M} (σ : Tree M f) (τ : Cell M f) → Set

  Frmₛ : (M : 𝕄) → Set
  Frmₛ M = Σ (Frm M) (λ f → Tree M f × Cell M f)
  
  data Pd (M : 𝕄) (F : Filler M) : Frmₛ M → Set where

    lf : {f : Frm M} (τ : Cell M f) → Pd M F (f , η M τ , τ)

    nd : {f : Frm M} (σ : Tree M f) (τ : Cell M f) (θ : F σ τ)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M σ) → Pd M F (Typ M σ p , δ p , Inh M σ p))
      → Pd M F (f , μ M σ δ , τ)

  Treeₛ : (M : 𝕄) (F : Filler M) → Frmₛ M → Set
  Treeₛ M F = Pd M F

  Cellₛ : (M : 𝕄) (F : Filler M) → Frmₛ M → Set
  Cellₛ M F (f , σ , τ) = F σ τ

  Posₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → Set
  Posₛ M F (lf τ) = ⊥
  Posₛ M F (nd σ τ θ δ ε) = ⊤ ⊔ (Σ (Pos M σ) (λ p → Posₛ M F (ε p)))

  Typₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (p : Posₛ M F σ) → Frmₛ M
  Typₛ M F (nd σ τ θ δ ε) (inl unit) = _ , σ , τ
  Typₛ M F (nd σ τ θ δ ε) (inr (p , q)) = Typₛ M F (ε p) q

  Inhₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (p : Posₛ M F σ) → Cellₛ M F (Typₛ M F σ p)
  Inhₛ M F (nd σ τ θ δ ε) (inl unit) = θ
  Inhₛ M F (nd σ τ θ δ ε) (inr (p , q)) = Inhₛ M F (ε p) q

  --
  --  Free monad signature
  --
  
  γ : (M : 𝕄) (F : Filler M)
    → {f : Frm M} {σ : Tree M f} {τ : Cell M f}
    → (ρ : Treeₛ M F (f , σ , τ))
    → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ε : (p : Pos M σ) → Treeₛ M F (Typ M σ p , δ p , Inh M σ p))
    → Treeₛ M F (f , μ M σ δ , τ)

  γ-pos-inl : (M : 𝕄) (F : Filler M)
    → {f : Frm M} {σ : Tree M f} {τ : Cell M f}
    → (ρ : Treeₛ M F (f , σ , τ))
    → (ϕ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ψ : (p : Pos M σ) → Treeₛ M F (Typ M σ p , ϕ p , Inh M σ p))
    → Posₛ M F ρ → Posₛ M F (γ M F ρ ϕ ψ)

  γ-pos-inr : (M : 𝕄) (F : Filler M)
    → {f : Frm M} {σ : Tree M f} {τ : Cell M f}
    → (ρ : Treeₛ M F (f , σ , τ))
    → (ϕ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ψ : (p : Pos M σ) → Treeₛ M F (Typ M σ p , ϕ p , Inh M σ p))
    → (p : Pos M σ) (q : Posₛ M F (ψ p))
    → Posₛ M F (γ M F ρ ϕ ψ)

  γ-pos-elim : (M : 𝕄) (F : Filler M)
    → {f : Frm M} {σ : Tree M f} {τ : Cell M f}
    → (ρ : Treeₛ M F (f , σ , τ))
    → (ϕ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ψ : (p : Pos M σ) → Treeₛ M F (Typ M σ p , ϕ p , Inh M σ p))
    → (X : Posₛ M F (γ M F ρ ϕ ψ) → Set)
    → (inl* : (p : Posₛ M F ρ) → X (γ-pos-inl M F ρ ϕ ψ p))
    → (inr* : (p : Pos M σ) (q : Posₛ M F (ψ p)) → X (γ-pos-inr M F ρ ϕ ψ p q))
    → (p : Posₛ M F (γ M F ρ ϕ ψ)) → X p

  --
  --  Free monad laws
  --
  
  postulate
  
    -- γ elim comp rules
    γ-pos-elim-inl-β : (M : 𝕄) (F : Filler M)
      → {f : Frm M} {σ : Tree M f} {τ : Cell M f}
      → (ρ : Treeₛ M F (f , σ , τ))
      → (ϕ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ψ : (p : Pos M σ) → Treeₛ M F (Typ M σ p , ϕ p , Inh M σ p))
      → (X : Posₛ M F (γ M F ρ ϕ ψ) → Set)
      → (inl* : (p : Posₛ M F ρ) → X (γ-pos-inl M F ρ ϕ ψ p))
      → (inr* : (p : Pos M σ) (q : Posₛ M F (ψ p)) → X (γ-pos-inr M F ρ ϕ ψ p q))
      → (p : Posₛ M F ρ)
      → γ-pos-elim M F ρ ϕ ψ X inl* inr* (γ-pos-inl M F ρ ϕ ψ p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : (M : 𝕄) (F : Filler M)
      → {f : Frm M} {σ : Tree M f} {τ : Cell M f}
      → (ρ : Treeₛ M F (f , σ , τ))
      → (ϕ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ψ : (p : Pos M σ) → Treeₛ M F (Typ M σ p , ϕ p , Inh M σ p))
      → (X : Posₛ M F (γ M F ρ ϕ ψ) → Set)
      → (inl* : (p : Posₛ M F ρ) → X (γ-pos-inl M F ρ ϕ ψ p))
      → (inr* : (p : Pos M σ) (q : Posₛ M F (ψ p)) → X (γ-pos-inr M F ρ ϕ ψ p q))
      → (p : Pos M σ) (q : Posₛ M F (ψ p))
      → γ-pos-elim M F ρ ϕ ψ X inl* inr* (γ-pos-inr M F ρ ϕ ψ p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}

    -- We don't seem to need the associativity, unit and
    -- distributivity laws for γ to finish type checking.  But it
    -- seems likely that we will need them later when actually working
    -- with these objects ....

  --
  --  Slice implementation 
  --

  ηₛ : (M : 𝕄) (F : Filler M) 
    → {f : Frmₛ M} (τ : Cellₛ M F f)
    → Treeₛ M F f
  ηₛ M F {f = f , σ , τ} θ =
    let η-dec p = η M (Inh M σ p)
        lf-dec p = lf {F = F} (Inh M σ p)
    in nd σ τ θ η-dec lf-dec

  η-posₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (τ : Cellₛ M F f)
    → Posₛ M F (ηₛ M F τ)
  η-posₛ M F τ = inl unit
  
  η-pos-elimₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (τ : Cellₛ M F f)
    → (X : (p : Posₛ M F (ηₛ M F τ)) → Set)
    → (η-pos* : X (η-posₛ M F τ))
    → (p : Posₛ M F (ηₛ M F τ)) → X p
  η-pos-elimₛ M F τ X η-pos* (inl unit) = η-pos*

  μₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (δ : (p : Posₛ M F σ) → Treeₛ M F (Typₛ M F σ p))
    → Treeₛ M F f
  μₛ M F (lf τ) κ = lf τ
  μₛ M F (nd σ τ θ δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M F (ε p) (κ↑ p) 
    in γ M F w δ ψ

  μ-posₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (δ : (p : Posₛ M F σ) → Treeₛ M F (Typₛ M F σ p))
    → (p : Posₛ M F σ) (q : Posₛ M F (δ p))
    → Posₛ M F (μₛ M F σ δ)
  μ-posₛ M F (nd σ τ θ δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M F (ε p) (κ↑ p)
    in γ-pos-inl M F w δ ψ r
  μ-posₛ M F (nd σ τ θ δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M F (ε p) (κ↑ p)
    in γ-pos-inr M F w δ ψ p (μ-posₛ M F (ε p) (κ↑ p) q r)

  μ-pos-fstₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (δ : (p : Posₛ M F σ) → Treeₛ M F (Typₛ M F σ p))
    → Posₛ M F (μₛ M F σ δ) → Posₛ M F σ
  μ-pos-fstₛ M F (nd σ τ θ δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M F (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Pos M σ) (λ p → Posₛ M F (ε p))
        inl* p = inl unit
        inr* p q = inr (p , μ-pos-fstₛ M F (ε p) (κ↑ p) q)
    in γ-pos-elim M F w δ ψ X inl* inr* p

  μ-pos-sndₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (δ : (p : Posₛ M F σ) → Treeₛ M F (Typₛ M F σ p))
    → (p : Posₛ M F (μₛ M F σ δ))
    → Posₛ M F (δ (μ-pos-fstₛ M F σ δ p))
  μ-pos-sndₛ M F (nd σ τ θ δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M F (ε p) (κ↑ p)
        X p = Posₛ M F (κ (μ-pos-fstₛ M F (nd σ τ θ δ ε) κ p))
        inl* p = p
        inr* p q = μ-pos-sndₛ M F (ε p) (κ↑ p) q
    in γ-pos-elim M F w δ ψ X inl* inr* p
    
  --
  --  Free monad implementation 
  --
  
  γ M F (lf τ) ϕ ψ = ψ (η-pos M τ)
  γ M F (nd σ τ θ δ ε) ϕ ψ = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M F (ε p) (ϕ↑ p) (ψ↑ p)
    in nd σ τ θ δ↑ ε↑

  γ-pos-inl M F (nd σ τ θ δ ε) ϕ ψ (inl unit) = inl unit
  γ-pos-inl M F (nd σ τ θ δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M F (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γ-pos-inl M F (ε p) (ϕ↑ p) (ψ↑ p) q)

  γ-pos-inr M F (lf τ) ϕ ψ p q =
    η-pos-elim M τ (λ p → Posₛ M F (ψ p) → Posₛ M F (ψ (η-pos M τ))) (λ p → p) p q
  γ-pos-inr M F (nd σ τ θ δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M F (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μ-pos-fst M σ δ p
        p₁ = μ-pos-snd M σ δ p
    in inr (p₀ , γ-pos-inr M F (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q)

  γ-pos-elim M F (lf τ) ϕ ψ X inl* inr* p = inr* (η-pos M τ) p
  γ-pos-elim M F (nd σ τ θ δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γ-pos-elim M F (nd σ τ θ δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M F (ε p) (ϕ↑ p) (ψ↑ p)
        X↑ p q = X (inr (p , q))
        inl*↑ p q = inl* (inr (p , q))
        inr*↑ p q r = inr* (μ-pos M σ δ p q) r
    in γ-pos-elim M F (ε p) (ϕ↑ p) (ψ↑ p) (X↑ p) (inl*↑ p) (inr*↑ p) q


