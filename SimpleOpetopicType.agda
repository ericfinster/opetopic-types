{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import MiniHoTT

module SimpleOpetopicType where

  --
  --  Opetopic Types
  --

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

    μ-fst-frm : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → Frm X

    μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → Pos X c (μ-fst-frm X c δ p)

    μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → Pos X (δ (μ-fst X c δ p)) g

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
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → μ X (μ X c δ) ε ↦ μ X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
    {-# REWRITE μ-assoc #-}

  --
  --  Position Laws
  --
  
  postulate
  
    -- Position Computation Rules
    η-pos-elim-β : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : {g : Frm X} (p : Pos X (η X f) g) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → η-pos-elim X f P η-pos* (η-pos X f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-fst-frm-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (δ p) h)
      → μ-fst-frm X c δ (μ-pos X c δ p q) ↦ g 
    {-# REWRITE μ-pos-fst-frm-β #-}
    
    μ-pos-fst-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (δ p) h)
      → μ-fst X c δ (μ-pos X c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (δ p) h)
      → μ-snd X c δ (μ-pos X c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → μ-pos X c δ (μ-fst X c δ p) (μ-snd X c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}
      
  postulate
  
    -- Intro compatibility
    μ-pos-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → {g : Frm X} (p : Pos X c g)
      → μ-pos X c (λ {k} p → η X k) p (η-pos X g) ↦ p
    {-# REWRITE μ-pos-unit-r #-}

    μ-pos-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : {g : Frm X} (p : Pos X (η X f) g) → Cns X g)
      → {h : Frm X} (p : Pos X (δ (η-pos X f)) h)
      → μ-pos X (η X f) δ (η-pos X f) p ↦ p
    {-# REWRITE μ-pos-unit-l #-}

    μ-pos-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → {h : Frm X} (q : Pos X (ε p) h)
      → μ-pos X (μ X c δ) ε p q
        ↦ μ-pos X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) (μ-fst X c δ p)
          (μ-pos X (δ (μ-fst X c δ p)) (λ q → ε (μ-pos X c δ (μ-fst X c δ p) q))
          (μ-snd X c δ p) q)
    {-# REWRITE μ-pos-assoc #-}

    -- Frame Compatibility
    μ-fst-frm-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → {g : Frm X} (p : Pos X (μ X c (λ {g} p → η X g)) g)
      → μ-fst-frm X c (λ {g} p → η X g) p ↦ g
    {-# REWRITE μ-fst-frm-unit-r #-}

    μ-fst-frm-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : {g : Frm X} (p : Pos X (η X f) g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X (η X f) δ) g)
      → μ-fst-frm X (η X f) δ p ↦ f
    {-# REWRITE μ-fst-frm-unit-l #-}

    μ-fst-frm-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
      → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
        in μ-fst-frm X (μ X c δ) ε pqr
          ↦ μ-fst-frm X (δ p) (λ q → ε (μ-pos X c δ p q)) qr
    {-# REWRITE μ-fst-frm-assoc #-}
    
    -- First Projection
    μ-fst-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → {g : Frm X} (p : Pos X (μ X c (λ {g} p → η X g)) g)
      → μ-fst X c (λ {k} p → η X k) p ↦ p
    {-# REWRITE μ-fst-unit-r #-}

    μ-fst-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : {g : Frm X} (p : Pos X (η X f) g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X (η X f) δ) g)
      → μ-fst X (η X f) δ p ↦ η-pos X f
    {-# REWRITE μ-fst-unit-l #-}

    μ-fst-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
      → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            q = μ-fst X (δ p) (λ q → ε (μ-pos X c δ p q)) qr
        in μ-fst X (μ X c δ) ε pqr ↦ μ-pos X c δ p q  
    {-# REWRITE μ-fst-assoc #-}

    -- Second Projection
    μ-snd-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → {g : Frm X} (p : Pos X (μ X c (λ {g} p → η X g)) g)
      → μ-snd X c (λ {k} p → η X k) p ↦ η-pos X g
    {-# REWRITE μ-snd-unit-r #-}

    μ-snd-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : {g : Frm X} (p : Pos X (η X f) g) → Cns X g)
      → {g : Frm X} (p : Pos X (μ X (η X f) δ) g)
      → μ-snd X (η X f) δ p ↦ p
    {-# REWRITE μ-snd-unit-l #-}

    μ-snd-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
      → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
        in μ-snd X (μ X c δ) ε pqr
          ↦ μ-snd X (δ p) (λ q → ε (μ-pos X c δ p q)) qr 
    {-# REWRITE μ-snd-assoc #-} 


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
    μ-dec c δ θ p = θ (μ-fst Xₙ c δ p) (μ-snd Xₙ c δ p)

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

    -- One thing I am realizing is that you will probably *also* have
    -- to put the monad laws in the once unfolded form so that when
    -- we slice, there is the same behavior.  Well, I'm not sure if
    -- this is necessary or not ...
    
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
    
    graft : {φ : SlcFrm} (ω : Web φ)
      → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
      → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
      → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
           → Web ⟪ g , δ p , src φ p , θ p ⟫)
      → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫
    graft (lf {f} x) δ θ ε = ε (η-pos Xₙ f)
    graft (nd φ δ θ ε) ϕ ψ κ =
      let ϕ' {g} p {h} q = ϕ (μ-pos Xₙ (cns φ) δ {g} p {h} q)
          κ' {g} p {h} q = κ (μ-pos Xₙ (cns φ) δ {g} p {h} q)
          δ' {g} p = μ Xₙ {g} (δ p) (ϕ' p)
          -- Hmmm. Don't know why I can't make the λ's here into let defs ...
          ε' {g} p = graft (ε {g} p) (ϕ' p) (λ q r → ψ (μ-pos Xₙ (cns φ) δ p q) r) (κ' p) 
      in nd φ δ' (λ p q → ψ (μ-pos Xₙ (cns φ) δ p (μ-fst Xₙ (δ p) (ϕ' p) q)) ((μ-snd Xₙ (δ p) (ϕ' p) q))) ε' 

    postulate
    
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

