{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import MiniHoTT

module NewOpetopicType where

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
    → {f : Frm X} (c : Cns X f) → Set ℓ
  Typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (p : Pos X c) → Frm X


  --
  --  Monadic Signature
  --
  
  postulate

    η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Cns X f 

    η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Pos X (η X f) 

    η-pos-elim : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : (p : Pos X (η X f)) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → (p : Pos X (η X f)) → P p 

    μ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → Cns X f

    μ-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → Pos X (μ X c δ) 

    μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → Pos X c

    μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → Pos X (δ (μ-fst X c δ p))
  
  postulate

    --
    --  Position Typing
    --

    η-pos-typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (p : Pos X (η X f))
      → Typ X (η X f) p ↦ f
    {-# REWRITE η-pos-typ #-}

    μ-pos-typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → Typ X (μ X c δ) p ↦ Typ X (δ (μ-fst X c δ p)) (μ-snd X c δ p)
    {-# REWRITE μ-pos-typ #-}

    --
    --  Position Computation Rules
    --
    
    η-pos-elim-β : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : (p : Pos X (η X f)) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → η-pos-elim X f P η-pos* (η-pos X f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-fst-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → μ-fst X c δ (μ-pos X c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → μ-snd X c δ (μ-pos X c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → μ-pos X c δ (μ-fst X c δ p) (μ-snd X c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Monad Laws
    --

    μ-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → μ X c (λ p → η X (Typ X c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X (Typ X (η X f) p))
      → μ X (η X f) δ ↦ δ (η-pos X f)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → μ X (μ X c δ) ε ↦ 
        μ X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
    {-# REWRITE μ-assoc #-}

    --
    --  Compatibilities of Intro/Elim with Reductions
    --

    -- Introduction
    μ-pos-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f) (p : Pos X c)
      → μ-pos X c (λ p → η X (Typ X c p)) p (η-pos X (Typ X c p)) ↦ p
    {-# REWRITE μ-pos-unit-r #-}    

    μ-pos-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X f)
      → (p : Pos X (δ (η-pos X f)))
      → μ-pos X (η X f) δ (η-pos X f) p ↦ p
    {-# REWRITE μ-pos-unit-l #-}

    μ-pos-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → (pq : Pos X (μ X c δ)) (r : Pos X (ε pq))
      → let p = μ-fst X c δ pq
            q = μ-snd X c δ pq 
        in μ-pos X (μ X c δ) ε pq r
          ↦ μ-pos X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
              p (μ-pos X (δ p) (λ q → ε (μ-pos X c δ p q)) q r)
    {-# REWRITE μ-pos-assoc #-}
    
    -- First Projection
    μ-fst-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (p : Pos X (μ X c (λ p → η X (Typ X c p))))
      → μ-fst X c (λ p → η X (Typ X c p)) p ↦ p
    {-# REWRITE μ-fst-unit-r #-}

    μ-fst-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X f)
      → (p : Pos X (μ X (η X f) δ))
      → μ-fst X (η X f) δ p ↦ η-pos X f
    {-# REWRITE μ-fst-unit-l #-}

    -- μ-fst-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
    --   → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
    --   → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --         qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --         q = μ-fst X (δ p) (λ q → ε (μ-pos X c δ p q)) qr
    --     in μ-fst X (μ X c δ) ε pqr ↦ μ-pos X c δ p q  
    -- {-# REWRITE μ-fst-assoc #-}

    -- Second Projection
    μ-snd-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (p : Pos X (μ X c (λ p → η X (Typ X c p))))
      → μ-snd X c (λ p → η X (Typ X c p)) p ↦ η-pos X (Typ X c p)
    {-# REWRITE μ-snd-unit-r #-}

    μ-snd-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X (Typ X (η X f) p))
      → (p : Pos X (μ X (η X f) δ))
      → μ-snd X (η X f) δ p ↦ p
    {-# REWRITE μ-snd-unit-l #-}

    -- μ-snd-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
    --   → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
    --   → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --         qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --     in μ-snd X (μ X c δ) ε pqr
    --       ↦ μ-snd X (δ p) (λ q → ε (μ-pos X c δ p q)) qr 
    -- {-# REWRITE μ-snd-assoc #-} 

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) where
  
    η-dec : (f : Frm Xₙ) (x : Xₛₙ f)
      → (p : Pos Xₙ (η Xₙ f)) → Xₛₙ (Typ Xₙ (η Xₙ f) p)
    η-dec f = η-pos-elim Xₙ f (λ p → Xₛₙ (Typ Xₙ (η Xₙ f) p)) 

    μ-dec : {f : Frm Xₙ} (c : Cns Xₙ f)
      → (δ : (p : Pos Xₙ c) → Cns Xₙ (Typ Xₙ c p))
      → (θ : (p : Pos Xₙ c) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (p : Pos Xₙ (μ Xₙ c δ)) → Xₛₙ (Typ Xₙ (μ Xₙ c δ) p)
    μ-dec c δ θ p = θ (μ-fst Xₙ c δ p) (μ-snd Xₙ c δ p)

    -- record SlcFrm : Set ℓ where
    --   inductive 
    --   constructor ⟪_,_,_,_⟫ 
    --   field
    --     frm : Frm Xₙ
    --     cns : Cns Xₙ frm
    --     tgt : Xₛₙ frm
    --     src : {f : Frm Xₙ} (p : Pos Xₙ cns f) → Xₛₙ f 

    -- open SlcFrm
    
    -- data Web : SlcFrm → Set ℓ where

    --   lf : {f : Frm Xₙ} (x : Xₛₙ f)
    --     → Web ⟪ f , η Xₙ f , x , η-dec f x ⟫ 

    --   nd : (φ : SlcFrm)
    --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --     → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫ 

    -- -- One thing I am realizing is that you will probably *also* have
    -- -- to put the monad laws in the once unfolded form so that when
    -- -- we slice, there is the same behavior.  Well, I'm not sure if
    -- -- this is necessary or not ...
    
    -- data WebPos : {φ : SlcFrm} (ω : Web φ) → SlcFrm → Set ℓ where

    --   nd-here : (φ : SlcFrm)
    --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --     → WebPos (nd φ δ θ ε) φ

    --   nd-there : (φ : SlcFrm)
    --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --     → {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --     → {ψ : SlcFrm} (ρ : WebPos (ε p) ψ)
    --     → WebPos (nd φ δ θ ε) ψ 

    -- --
    -- --  Grafting
    -- --
    
    -- graft : {φ : SlcFrm} (ω : Web φ)
    --   → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --   → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --   → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --        → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --   → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫
    -- graft (lf {f} x) δ θ ε = ε (η-pos Xₙ f)
    -- graft (nd φ δ θ ε) ϕ ψ κ =
    --   let ϕ' {g} p {h} q = ϕ (μ-pos Xₙ (cns φ) δ {g} p {h} q)
    --       κ' {g} p {h} q = κ (μ-pos Xₙ (cns φ) δ {g} p {h} q)
    --       δ' {g} p = μ Xₙ {g} (δ p) (ϕ' p)
    --       -- Hmmm. Don't know why I can't make the λ's here into let defs ...
    --       ε' {g} p = graft (ε {g} p) (ϕ' p) (λ q r → ψ (μ-pos Xₙ (cns φ) δ p q) r) (κ' p) 
    --   in nd φ δ' (λ p q → ψ (μ-pos Xₙ (cns φ) δ p (μ-fst Xₙ (δ p) (ϕ' p) q)) ((μ-snd Xₙ (δ p) (ϕ' p) q))) ε' 

    -- postulate
    
    --   graft-pos-inl : {φ : SlcFrm} (ω : Web φ)
    --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --     → {ψ : SlcFrm} (p : WebPos ω ψ)
    --     → WebPos (graft ω δ θ ε) ψ

    --   graft-pos-inr : {φ : SlcFrm} (ω : Web φ)
    --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --     → {f : Frm Xₙ} (p : Pos Xₙ (cns φ) f)
    --     → {ψ : SlcFrm} (q : WebPos (ε p) ψ)
    --     → WebPos (graft ω δ θ ε) ψ

    --   graft-pos-elim : {φ : SlcFrm} (ω : Web φ)
    --     → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
    --     → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --            {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
    --     → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
    --          → Web ⟪ g , δ p , src φ p , θ p ⟫)
    --     → (P : {ψ : SlcFrm} (p : WebPos (graft ω δ θ ε) ψ) → Set ℓ)
    --     → (inl* : {ψ : SlcFrm} (p : WebPos ω ψ) → P (graft-pos-inl ω δ θ ε p))
    --     → (inr* : {f : Frm Xₙ} (p : Pos Xₙ (cns φ) f)
    --               {ψ : SlcFrm} (q : WebPos (ε p) ψ)
    --             → P (graft-pos-inr ω δ θ ε p q))
    --     → {ψ : SlcFrm} (p : WebPos (graft ω δ θ ε) ψ) → P p 




  𝕆 = {!!} 

  Frm = {!!} 
  Cns = {!!}
  Pos = {!!}
  Typ = {!!} 
