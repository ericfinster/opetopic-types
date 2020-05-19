{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Monad where

  postulate

    𝕄 : Set

    Frm : 𝕄 → Set
    Tree : (M : 𝕄) (f : Frm M) → Set

    Pos : (M : 𝕄) {f : Frm M}
      → Tree M f → Set

    Typ : (M : 𝕄) {f : Frm M}
      → (σ : Tree M f) (p : Pos M σ)
      → Frm M 

    η : (M : 𝕄) (f : Frm M)
      → Tree M f

    η-pos : (M : 𝕄) (f : Frm M)
      → Pos M (η M f)

    η-pos-elim : (M : 𝕄) (f : Frm M)
      → (X : (p : Pos M (η M f)) → Set)
      → (η-pos* : X (η-pos M f))
      → (p : Pos M (η M f)) → X p

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
      → (p : Pos M (η M f))
      → Typ M (η M f) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-elim-β : (M : 𝕄) (f : Frm M)
      → (X : (p : Pos M (η M f)) → Set)
      → (η-pos* : X (η-pos M f))
      → η-pos-elim M f X η-pos* (η-pos M f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-typ : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (p : Pos M (μ M σ δ))
      → Typ M (μ M σ δ) p ↦ Typ M (δ (μ-pos-fst M σ δ p)) (μ-pos-snd M σ δ p)
    {-# REWRITE μ-pos-typ #-}

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
      → μ M σ (λ p → η M (Typ M σ p)) ↦ σ
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : (M : 𝕄) (f : Frm M) 
      → (δ : (p : Pos M (η M f)) → Tree M f)
      → μ M (η M f) δ ↦ δ (η-pos M f)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M (μ M σ δ)) → Tree M (Typ M (μ M σ δ) p))
      → μ M (μ M σ δ) ε ↦ μ M σ (λ p → μ M (δ p) (λ q → ε (μ-pos M σ δ p q)))
    {-# REWRITE μ-assoc #-}

    -- μ pos compatibilities
    μ-pos-unit-right : (M : 𝕄) (f : Frm M)
      → (σ : Tree M f)
      → (p : Pos M σ) (q : Pos M (η M (Typ M σ p)))
      → μ-pos M σ (λ p → η M (Typ M σ p)) p q ↦ p 
    {-# REWRITE μ-pos-unit-right #-}

    μ-pos-unit-left : (M : 𝕄) (f : Frm M) 
      → (δ : (p : Pos M (η M f)) → Tree M f)
      → (p : Pos M (η M f)) (q : Pos M (δ p))
      → μ-pos M (η M f) δ p q ↦ η-pos-elim M f (λ p → Pos M (δ p) → Pos M (δ (η-pos M f))) (λ p → p) p q 
    {-# REWRITE μ-pos-unit-left #-} 

    μ-pos-assoc : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M (μ M σ δ)) → Tree M (Typ M (μ M σ δ) p))
      → (p : Pos M (μ M σ δ)) (q : Pos M (ε p))
      → μ-pos M (μ M σ δ) ε p q ↦ μ-pos M σ
              (λ p → μ M (δ p) (λ q → ε (μ-pos M σ δ p q))) (μ-pos-fst M σ δ p)
              (μ-pos M (δ (μ-pos-fst M σ δ p)) (λ q → ε (μ-pos M σ δ (μ-pos-fst M σ δ p) q)) (μ-pos-snd M σ δ p) q) 
    {-# REWRITE μ-pos-assoc #-}

    μ-pos-fst-unit-right : (M : 𝕄) {f : Frm M}
      → (σ : Tree M f) (p : Pos M σ)
      → μ-pos-fst M σ (λ p → η M (Typ M σ p)) p ↦ p 
    {-# REWRITE μ-pos-fst-unit-right #-}

    -- Hmmm.  This doesn't make much sense ...
    -- Really the expression we are rewriting
    -- here should be ill-typed
    μ-pos-fst-unit-left : (M : 𝕄) (f : Frm M) 
      → (δ : (p : Pos M (η M f)) → Tree M f)
      → (p : Pos M (δ (η-pos M f)))
      → μ-pos-fst M (η M f) δ p ↦ η-pos M f
    {-# REWRITE μ-pos-fst-unit-left #-}

    -- μ-pos-fst-assoc : (M : 𝕄) {f : Frm M} (σ : Tree M f)
    --   → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    --   → (ε : (p : Pos M (μ M σ δ)) → Tree M (Typ M (μ M σ δ) p))
    --   → μ-pos-fst M (μ M σ δ) ε {!!} ↦ {!!}

    -- μ-pos-snd : (M : 𝕄) {f : Frm M} (σ : Tree M f)
    --   → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    --   → (p : Pos M (μ M σ δ))
    --   → Pos M (δ (μ-pos-fst M σ δ p))

  Frmₛ : (M : 𝕄) → Set
  Frmₛ M = Σ (Frm M) (Tree M)
  
  data Pd (M : 𝕄) : Frmₛ M → Set where

    lf : (f : Frm M) → Pd M (f , η M f)

    nd : {f : Frm M} (σ : Tree M f) 
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M σ) → Pd M (Typ M σ p , δ p))
      → Pd M (f , μ M σ δ)

  Treeₛ : (M : 𝕄) → Frmₛ M → Set
  Treeₛ M = Pd M

  Posₛ : (M : 𝕄) {f : Frmₛ M}
    → (σ : Treeₛ M f) → Set
  Posₛ M (lf τ) = ⊥
  Posₛ M (nd σ δ ε) = ⊤ ⊔ (Σ (Pos M σ) (λ p → Posₛ M (ε p)))

  Typₛ : (M : 𝕄) {f : Frmₛ M}
    → (σ : Treeₛ M f) (p : Posₛ M σ)
    → Frmₛ M
  Typₛ M (nd σ δ ε) (inl unit) = _ , σ 
  Typₛ M (nd σ δ ε) (inr (p , q)) = Typₛ M (ε p) q

  --
  --  Free monad signature
  --
  
  γ : (M : 𝕄) {f : Frm M} {σ : Tree M f}
    → (ρ : Treeₛ M (f , σ))
    → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p))
    → Treeₛ M (f , μ M σ δ)

  γ-pos-inl : (M : 𝕄) {f : Frm M} {σ : Tree M f} 
    → (ρ : Treeₛ M (f , σ))
    → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p))
    → Posₛ M ρ → Posₛ M (γ M ρ δ ε)
  
  γ-pos-inr : (M : 𝕄) {f : Frm M} {σ : Tree M f} 
    → (ρ : Treeₛ M (f , σ))
    → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p))
    → (p : Pos M σ) (q : Posₛ M (ε p))
    → Posₛ M (γ M ρ δ ε)

  γ-pos-elim : (M : 𝕄) {f : Frm M} {σ : Tree M f} 
    → (ρ : Treeₛ M (f , σ))
    → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p))
    → (X : Posₛ M (γ M ρ δ ε) → Set)
    → (inl* : (p : Posₛ M ρ) → X (γ-pos-inl M ρ δ ε p))
    → (inr* : (p : Pos M σ) (q : Posₛ M (ε p)) → X (γ-pos-inr M ρ δ ε p q))
    → (p : Posₛ M (γ M ρ δ ε)) → X p

  --
  --  Free monad laws
  --
  
  postulate
  
    -- γ elim comp rules
    γ-pos-elim-inl-β : (M : 𝕄) {f : Frm M} {σ : Tree M f} 
      → (ρ : Treeₛ M (f , σ))
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p))
      → (X : Posₛ M (γ M ρ δ ε) → Set)
      → (inl* : (p : Posₛ M ρ) → X (γ-pos-inl M ρ δ ε p))
      → (inr* : (p : Pos M σ) (q : Posₛ M (ε p)) → X (γ-pos-inr M ρ δ ε p q))
      → (p : Posₛ M ρ)
      → γ-pos-elim M ρ δ ε X inl* inr* (γ-pos-inl M ρ δ ε p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : (M : 𝕄) {f : Frm M} {σ : Tree M f} 
      → (ρ : Treeₛ M (f , σ))
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → (ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p))
      → (X : Posₛ M (γ M ρ δ ε) → Set)
      → (inl* : (p : Posₛ M ρ) → X (γ-pos-inl M ρ δ ε p))
      → (inr* : (p : Pos M σ) (q : Posₛ M (ε p)) → X (γ-pos-inr M ρ δ ε p q))
      → (p : Pos M σ) (q : Posₛ M (ε p))
      → γ-pos-elim M ρ δ ε X inl* inr* (γ-pos-inr M ρ δ ε p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}

    -- We don't seem to need the associativity, unit and
    -- distributivity laws for γ to finish type checking.  But it
    -- seems likely that we will need them later when actually working
    -- with these objects ....

  --
  --  Slice implementation 
  --

  ηₛ : (M : 𝕄) → (f : Frmₛ M) → Treeₛ M f
  ηₛ M (f , σ) =
    let η-dec p = η M (Typ M σ p)
        lf-dec p = lf (Typ M σ p)
    in nd σ η-dec lf-dec

  η-posₛ : (M : 𝕄) (f : Frmₛ M)
    → Posₛ M (ηₛ M f)
  η-posₛ M f = inl unit
  
  η-pos-elimₛ : (M : 𝕄) (f : Frmₛ M)
    → (X : (p : Posₛ M (ηₛ M f)) → Set)
    → (η-pos* : X (η-posₛ M f))
    → (p : Posₛ M (ηₛ M f)) → X p
  η-pos-elimₛ M f X η-pos* (inl unit) = η-pos*

  μₛ : (M : 𝕄) {f : Frmₛ M} (σ : Treeₛ M f)
    → (δ : (p : Posₛ M σ) → Treeₛ M (Typₛ M σ p))
    → Treeₛ M f
  μₛ M (lf τ) κ = lf τ
  μₛ M (nd σ δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p) 
    in γ M w δ ψ

  μ-posₛ : (M : 𝕄) {f : Frmₛ M} (σ : Treeₛ M f)
    → (δ : (p : Posₛ M σ) → Treeₛ M (Typₛ M σ p))
    → (p : Posₛ M σ) (q : Posₛ M (δ p))
    → Posₛ M (μₛ M σ δ)
  μ-posₛ M (nd σ δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
    in γ-pos-inl M w δ ψ r
  μ-posₛ M (nd σ δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
    in γ-pos-inr M w δ ψ p (μ-posₛ M (ε p) (κ↑ p) q r)

  μ-pos-fstₛ : (M : 𝕄) {f : Frmₛ M} (σ : Treeₛ M f)
    → (δ : (p : Posₛ M σ) → Treeₛ M (Typₛ M σ p))
    → Posₛ M (μₛ M σ δ) → Posₛ M σ
  μ-pos-fstₛ M (nd σ δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Pos M σ) (λ p → Posₛ M (ε p))
        inl* p = inl unit
        inr* p q = inr (p , μ-pos-fstₛ M (ε p) (κ↑ p) q)
    in γ-pos-elim M w δ ψ X inl* inr* p

  μ-pos-sndₛ : (M : 𝕄) {f : Frmₛ M} (σ : Treeₛ M f)
    → (δ : (p : Posₛ M σ) → Treeₛ M (Typₛ M σ p))
    → (p : Posₛ M (μₛ M σ δ))
    → Posₛ M (δ (μ-pos-fstₛ M σ δ p))
  μ-pos-sndₛ M (nd σ δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
        X p = Posₛ M (κ (μ-pos-fstₛ M (nd σ δ ε) κ p))
        inl* p = p
        inr* p q = μ-pos-sndₛ M (ε p) (κ↑ p) q
    in γ-pos-elim M w δ ψ X inl* inr* p
    
  --
  --  Free monad implementation 
  --

  γ M (lf f) ϕ ψ = ψ (η-pos M f)
  γ M (nd σ δ ε) ϕ ψ = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
    in nd σ δ↑ ε↑

  γ-pos-inl M (nd σ δ ε) ϕ ψ (inl unit) = inl unit
  γ-pos-inl M (nd σ δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γ-pos-inl M (ε p) (ϕ↑ p) (ψ↑ p) q)

  γ-pos-inr M (lf f) ϕ ψ p q = 
    η-pos-elim M f (λ p → Posₛ M (ψ p) → Posₛ M (ψ (η-pos M f))) (λ p → p) p q
  γ-pos-inr M (nd σ δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μ-pos-fst M σ δ p
        p₁ = μ-pos-snd M σ δ p
    in inr (p₀ , γ-pos-inr M (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q)

  γ-pos-elim M (lf f) ϕ ψ X inl* inr* p = inr* (η-pos M f) p
  γ-pos-elim M (nd σ δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γ-pos-elim M (nd σ δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos M σ δ p q)
        ψ↑ p q = ψ (μ-pos M σ δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
        X↑ p q = X (inr (p , q))
        inl*↑ p q = inl* (inr (p , q))
        inr*↑ p q r = inr* (μ-pos M σ δ p q) r
    in γ-pos-elim M (ε p) (ϕ↑ p) (ψ↑ p) (X↑ p) (inl*↑ p) (inr*↑ p) q

  --
  --  The slice construction
  --

  postulate

    Slice : 𝕄 → 𝕄

    Frm-Slice : (M : 𝕄) 
      → Frm (Slice M) ↦ Frmₛ M
    {-# REWRITE Frm-Slice #-}
    
    Tree-Slice : (M : 𝕄) 
      → Tree (Slice M) ↦ Treeₛ M 
    {-# REWRITE Tree-Slice #-}

    Pos-Slice : (M : 𝕄) 
      → {f : Frm (Slice M)}
      → (σ : Tree (Slice M) f)
      → Pos (Slice M) σ ↦ Posₛ M σ
    {-# REWRITE Pos-Slice #-}

    Typ-Slice : (M : 𝕄) 
      → {f : Frm (Slice M)}
      → (σ : Tree (Slice M) f) (p : Pos (Slice M) σ)
      → Typ (Slice M) σ p ↦ Typₛ M σ p
    {-# REWRITE Typ-Slice #-}

    η-Slice : (M : 𝕄) 
      → (f : Frm (Slice M))
      → η (Slice M) f ↦ ηₛ M f
    {-# REWRITE η-Slice #-}

    η-pos-Slice : (M : 𝕄) 
      → (f : Frm (Slice M))
      → η-pos (Slice M) f ↦ η-posₛ M f
    {-# REWRITE η-pos-Slice #-}

    η-pos-elim-Slice : (M : 𝕄) 
      → (f : Frm (Slice M))
      → (X : (p : Pos (Slice M) (η (Slice M) f)) → Set)
      → (η-pos* : X (η-pos (Slice M) f))
      → (p : Pos (Slice M) (η (Slice M) f))
      → η-pos-elim (Slice M) f X η-pos* p ↦ η-pos-elimₛ M f X η-pos* p 
    {-# REWRITE η-pos-elim-Slice #-}

    μ-Slice : (M : 𝕄) 
      → {f : Frm (Slice M)} (σ : Tree (Slice M) f)
      → (δ : (p : Pos (Slice M) σ) → Tree (Slice M) (Typ (Slice M) σ p))
      → μ (Slice M) σ δ ↦ μₛ M σ δ
    {-# REWRITE μ-Slice #-}

    μ-pos-Slice : (M : 𝕄) 
      → {f : Frm (Slice M)} (σ : Tree (Slice M) f)
      → (δ : (p : Pos (Slice M) σ) → Tree (Slice M) (Typ (Slice M) σ p))
      → (p : Pos (Slice M) σ) (q : Pos (Slice M) (δ p))
      → μ-pos (Slice M) σ δ p q ↦ μ-posₛ M σ δ p q
    {-# REWRITE μ-pos-Slice #-}

    μ-pos-fst-Slice : (M : 𝕄) 
      → {f : Frm (Slice M)} (σ : Tree (Slice M) f)
      → (δ : (p : Pos (Slice M) σ) → Tree (Slice M) (Typ (Slice M) σ p))
      → (p : Pos (Slice M) (μ (Slice M) σ δ))
      → μ-pos-fst (Slice M) σ δ p ↦ μ-pos-fstₛ M σ δ p
    {-# REWRITE μ-pos-fst-Slice #-}
    
    μ-pos-snd-Slice : (M : 𝕄) 
      → {f : Frm (Slice M)} (σ : Tree (Slice M) f)
      → (δ : (p : Pos (Slice M) σ) → Tree (Slice M) (Typ (Slice M) σ p))
      → (p : Pos (Slice M) (μ (Slice M) σ δ))
      → μ-pos-snd (Slice M) σ δ p ↦ μ-pos-sndₛ M σ δ p
    {-# REWRITE μ-pos-snd-Slice #-}

