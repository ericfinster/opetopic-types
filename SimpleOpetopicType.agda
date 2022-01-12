{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import MiniHoTT

module SimpleOpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)

  --
  --  Polynomial Signature
  --

  Frm : ∀ {ℓ n} → 𝕆 ℓ n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → Frm X → Set ℓ
  Pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (t : Frm X) → Set ℓ

  --
  --  Monadic Signature
  --
  
  postulate

    η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Cns X f 

    η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Pos X (η X f) f 

    η-pos-elim : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : {g : Frm X} (p : Pos X (η X f) g) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → {g : Frm X} (p : Pos X (η X f) g)
      → P p 

    μ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → Cns X f

    μ-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (δ p) h)
      → Pos X (μ X c δ) h

    μ-pos-elim : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (P : {g : Frm X} (p : Pos X (μ X c δ) g) → Set ℓ)
      → (μ-pos* : {g : Frm X} (p : Pos X c g)
                  {h : Frm X} (q : Pos X (δ p) h)
                → P {h} (μ-pos X c δ p q))
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → P {g} p              
  
  --
  --  Monad Laws
  --

  postulate

    μ-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → μ X c (λ {g} p → η X g) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : {g : Frm X} (p : Pos X (η X f) g) → Cns X g)
      → μ X (η X f) δ ↦ δ (η-pos X f)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X c g)
             {h : Frm X} (q : Pos X (δ p) h) → Cns X h)
      → μ X (μ X c δ) (μ-pos-elim X c δ (λ {g} p → Cns X g) ε)
        ↦ μ X c (λ p → μ X (δ p) (ε p))
    {-# REWRITE μ-assoc #-}

    -- Position Elimination Laws
    
    η-pos-elim-β : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : {g : Frm X} (p : Pos X (η X f) g) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → η-pos-elim X f P η-pos* (η-pos X f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-elim-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (P : {g : Frm X} (p : Pos X (μ X c δ) g) → Set ℓ)
      → (μ-pos* : {g : Frm X} (p : Pos X c g)
                  {h : Frm X} (q : Pos X (δ p) h)
                → P {h} (μ-pos X c δ p q))
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (δ p) h)
      → μ-pos-elim X c δ P μ-pos* (μ-pos X c δ p q) ↦ μ-pos* p q
    {-# REWRITE μ-pos-elim-β #-}

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) where
  
    η-dec : (f : Frm Xₙ) (x : Xₛₙ f)
      → {g : Frm Xₙ} (p : Pos Xₙ (η Xₙ f) g) → Xₛₙ g
    η-dec f x = η-pos-elim Xₙ f (λ {g} p → Xₛₙ g) x 

    μ-dec : {f : Frm Xₙ} (c : Cns Xₙ f)
      → (δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g)
      → (θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
             {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
      → {g : Frm Xₙ} → Pos Xₙ (μ Xₙ c δ) g → Xₛₙ g
    μ-dec c δ θ = μ-pos-elim Xₙ c δ (λ {g} p → Xₛₙ g) θ 

    record SlcFrm : Set ℓ where
      inductive 
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ
        cns : Cns Xₙ frm
        tgt : Xₛₙ frm
        src : {f : Frm Xₙ} (p : Pos Xₙ cns f) → Xₛₙ f 

    open SlcFrm
    
    data Web : SlcFrm → Set ℓ where

      lf : {f : Frm Xₙ} (x : Xₛₙ f)
        → Web ⟪ f , η Xₙ f , x , η-dec f x ⟫ 

      nd : (φ : SlcFrm)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫ 

    data WebPos : {φ : SlcFrm} (ω : Web φ) → SlcFrm → Set ℓ where

      nd-here : (φ : SlcFrm)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → WebPos (nd φ δ θ ε) φ

      nd-there : (φ : SlcFrm)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
        → {ψ : SlcFrm} (ρ : WebPos (ε p) ψ)
        → WebPos (nd φ δ θ ε) ψ 

    --
    --  Grafting
    --
    
    postulate

      graft : {φ : SlcFrm} (ω : Web φ)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫ 
      
      graft-pos-inl : {φ : SlcFrm} (ω : Web φ)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → {ψ : SlcFrm} (p : WebPos ω ψ)
        → WebPos (graft ω δ θ ε) ψ

      graft-pos-inr : {φ : SlcFrm} (ω : Web φ)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → {f : Frm Xₙ} (p : Pos Xₙ (cns φ) f)
        → {ψ : SlcFrm} (q : WebPos (ε p) ψ)
        → WebPos (graft ω δ θ ε) ψ

      graft-pos-elim : {φ : SlcFrm} (ω : Web φ)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → Web ⟪ g , δ p , src φ p , θ p ⟫)
        → (P : {ψ : SlcFrm} (p : WebPos (graft ω δ θ ε) ψ) → Set ℓ)
        → (inl* : {ψ : SlcFrm} (p : WebPos ω ψ) → P (graft-pos-inl ω δ θ ε p))
        → (inr* : {f : Frm Xₙ} (p : Pos Xₙ (cns φ) f)
                  {ψ : SlcFrm} (q : WebPos (ε p) ψ)
                → P (graft-pos-inr ω δ θ ε p q))
        → {ψ : SlcFrm} (p : WebPos (graft ω δ θ ε) ψ) → P p 

  𝕆 ℓ O = ⊤
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ Xₙ → (f : Frm Xₙ) → Set ℓ)
  
  Frm {ℓ} {O} _ = ⊤
  Frm {ℓ} {S n} (Xₙ , Xₛₙ) = SlcFrm Xₙ Xₛₙ
  
  Cns {ℓ} {O} _ _ = ⊤
  Cns {ℓ} {S n} (Xₙ , Xₛₙ) = Web Xₙ Xₛₙ
  
  Pos {ℓ} {O} _ _ _ = ⊤
  Pos {ℓ} {S n} (Xₙ , Xₛₙ) c g = WebPos Xₙ Xₛₙ c g

  -- 
  --  Old, unfolded version of above
  --

  -- data Web {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) :
  --   (f : Frm Xₙ) (x : Xₛₙ f) (c : Cns Xₙ f)
  --   (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g) → Set ℓ where

  --   lf : {f : Frm Xₙ} (x : Xₛₙ f)
  --     → Web Xₙ Xₛₙ f x (η Xₙ f) (η-pos-elim Xₙ f (λ {g} p → Xₛₙ g) x) 

  --   nd : {f : Frm Xₙ} (c : Cns Xₙ f) (x : Xₛₙ f) 
  --     → (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g)
  --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g)
  --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
  --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
  --          → Xₛₙ h)
  --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
  --          → Web Xₙ Xₛₙ g (ν p) (δ p) (θ p))
  --     → Web Xₙ Xₛₙ f x (μ Xₙ c δ)
  --         (μ-pos-elim Xₙ c δ (λ {g} p → Xₛₙ g) θ) 

  -- data WebPos {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) : 
  --   {f : Frm Xₙ} {x : Xₛₙ f} {c : Cns Xₙ f}
  --   {ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g}
  --   (ρ : Web Xₙ Xₛₙ f x c ν)
  --   (g : Frm Xₙ) (y : Xₛₙ g) (d : Cns Xₙ g)
  --   (θ : {h : Frm Xₙ} (p : Pos Xₙ d h) → Xₛₙ h)  → Set ℓ where

  --   nd-here : {f : Frm Xₙ} {c : Cns Xₙ f} {x : Xₛₙ f}
  --     → {ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g}
  --     → {δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g}
  --     → {θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
  --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
  --          → Xₛₙ h}
  --     → {ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
  --          → Web Xₙ Xₛₙ g (ν p) (δ p) (θ p)}
  --     → WebPos Xₙ Xₛₙ (nd c x ν δ θ ε) f x c ν 

  --   nd-there : {f : Frm Xₙ} {c : Cns Xₙ f} {x : Xₛₙ f}
  --     → {ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g}
  --     → {δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g}
  --     → {θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
  --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
  --          → Xₛₙ h}
  --     → {ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
  --          → Web Xₙ Xₛₙ g (ν p) (δ p) (θ p)}
  --     → {g : Frm Xₙ} (p : Pos Xₙ c g)
  --     → {h : Frm Xₙ} {y : Xₛₙ h} {d : Cns Xₙ h}
  --     → {ρ : {k : Frm Xₙ} (q : Pos Xₙ d k) → Xₛₙ k}
  --     → (q : WebPos Xₙ Xₛₙ (ε p) h y d ρ)
  --     → WebPos Xₙ Xₛₙ (nd c x ν δ θ ε) h y d ρ



