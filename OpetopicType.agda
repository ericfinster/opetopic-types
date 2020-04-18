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

    μ : (M : 𝕄) {f : Frm M} (σ : Tree M f)
      → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
      → Tree M f

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

    -- μ laws
    μ-unit-right : (M : 𝕄) (f : Frm M)
      → (σ : Tree M f)
      → μ M σ (λ p → η M (Inh M σ p)) ↦ σ
    {-# REWRITE μ-unit-right #-}

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
  
  ηₛ : (M : 𝕄) (F : Filler M) 
    → {f : Frmₛ M} (τ : Cellₛ M F f)
    → Treeₛ M F f
  ηₛ M F {f = f , σ , τ} θ =
    let η-dec p = η M (Inh M σ p)
        lf-dec p = lf {F = F} (Inh M σ p)
    in nd σ τ θ η-dec lf-dec




