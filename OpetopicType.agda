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

  γ : (M : 𝕄) (F : Filler M)
    → {f : Frm M} (σ : Tree M f) (τ : Cell M f)
    → (ρ : Treeₛ M F (f , σ , τ))
    → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
    → (ε : (p : Pos M σ) → Treeₛ M F (Typ M σ p , δ p , Inh M σ p))
    → Treeₛ M F (f , μ M σ δ , τ)

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

  ηₛ : (M : 𝕄) (F : Filler M) 
    → {f : Frmₛ M} (τ : Cellₛ M F f)
    → Treeₛ M F f
  ηₛ M F {f = f , σ , τ} θ =
    let η-dec p = η M (Inh M σ p)
        lf-dec p = lf {F = F} (Inh M σ p)
    in nd σ τ θ η-dec lf-dec

  μₛ : (M : 𝕄) (F : Filler M)
    → {f : Frmₛ M} (σ : Treeₛ M F f)
    → (δ : (p : Posₛ M F σ) → Treeₛ M F (Typₛ M F σ p))
    → Treeₛ M F f
  μₛ M F (lf τ) κ = lf τ
  μₛ M F (nd σ τ θ δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M F (ε p) (κ↑ p) 
    in γ M F σ τ w δ ψ

  γ = {!!}
