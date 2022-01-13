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

    -- μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → {f : Frm X} (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → {g : Frm X} (p : Pos X (μ X c δ) g)
    --   → Σ (Frm X) (Pos X c)

    -- μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → {f : Frm X} (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → {g : Frm X} (p : Pos X (μ X c δ) g)
    --   → Pos X (δ (snd (μ-fst X c δ p))) g

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

  -- Projections
  μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    → {g : Frm X} (p : Pos X (μ X c δ) g)
    → Σ (Frm X) (Pos X c)
  μ-fst X c δ = μ-pos-elim X c δ (λ p → Σ (Frm X) (Pos X c)) (λ {g} p _ → g , p) 

  μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    → {g : Frm X} (p : Pos X (μ X c δ) g)
    → Pos X (δ (snd (μ-fst X c δ p))) g
  μ-snd X c δ = μ-pos-elim X c δ
    (λ {g} p → Pos X (δ (snd (μ-fst X c δ p))) g)
    (λ {g} p q → q) 

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

    -- So this can in fact be more general if you introduce
    -- the projections ...  perhaps that is better? 
    μ-pos-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (δ p) h)
      → {k : Frm X} (r : Pos X (ε (μ-pos X c δ p q)) k)
      → μ-pos X (μ X c δ) ε (μ-pos X c δ p q) r
        ↦ μ-pos X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) p
          (μ-pos X (δ p) (λ q → ε (μ-pos X c δ p q)) q r)
    {-# REWRITE μ-pos-assoc #-}

    -- μ-pos-assoc' : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
    --   → {g : Frm X} (p : Pos X (μ X c δ) g)
    --   → {h : Frm X} (q : Pos X (ε p) h)
    --   → μ-pos X (μ X c δ) ε p q
    --     ↦ μ-pos X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) (snd (μ-fst X c δ p))
    --         (μ-pos X (δ (snd (μ-fst X c δ p))) (λ q → ε (μ-pos X c δ (snd (μ-fst X c δ p)) q))
    --           (μ-snd X c δ p) {!q!})

    -- Elim compatibility
    μ-pos-elim-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (P : {g : Frm X} (p : Pos X (μ X c (λ {h} p → η X h)) g) → Set ℓ)
      → (μ-pos* : {g : Frm X} (p : Pos X c g)
                  {h : Frm X} (q : Pos X (η X g) h)
                → P {h} (μ-pos X c (λ {h} p → η X h) p q))
      → {g : Frm X} (p : Pos X (μ X c (λ {g} p → η X g)) g)
      → μ-pos-elim X c (λ {g} p → η X g) P μ-pos* p ↦ μ-pos* p (η-pos X g) 
    {-# REWRITE μ-pos-elim-unit-r #-}

    μ-pos-elim-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : {g : Frm X} (p : Pos X (η X f) g) → Cns X g)
      → (P : {g : Frm X} (p : Pos X (μ X (η X f) δ) g) → Set ℓ)
      → (μ-pos* : {g : Frm X} (p : Pos X (η X f) g)
                  {h : Frm X} (q : Pos X (δ p) h)
                → P (μ-pos X (η X f) δ p q))
      → {g : Frm X} (p : Pos X (δ (η-pos X f)) g)
      → μ-pos-elim X (η X f) δ P μ-pos* p ↦ μ-pos* (η-pos X f) p
    {-# REWRITE μ-pos-elim-unit-l #-}

    μ-pos-elim-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
      → (P : {g : Frm X} (p : Pos X (μ X (μ X c δ) ε) g) → Set ℓ)
      → (μ-pos* : {g : Frm X} (p : Pos X (μ X c δ) g)
                  {h : Frm X} (q : Pos X (ε p) h)
                → P (μ-pos X (μ X c δ) ε p q ))
      → {g : Frm X} (p : Pos X (μ X (μ X c δ) ε) g)
      → μ-pos-elim X (μ X c δ) ε P μ-pos* p ↦
          μ-pos-elim X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
            P (λ p q → {!μ-pos* (μ-pos X c δ p (snd )) ?!}) p  

    -- I see.  This is not general enough.  Oh, and probably the same for
    -- associativity.  It should be *any* decoration of the multiplied
    -- constructor, not just one obtained from eliminating.  Let's try
    -- that.
    -- μ-pos-elim-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ε : {g : Frm X} (p : Pos X c g)
    --          {h : Frm X} (q : Pos X (δ p) h) → Cns X h)
    --   → (P : {g : Frm X} (p : Pos X (μ X (μ X c δ)
    --            (μ-pos-elim X c δ (λ {g} p → Cns X g) ε)) g) → Set ℓ)
    --   → (μ-pos* : {g : Frm X} (p : Pos X (μ X c δ) g)
    --               {h : Frm X} (q : Pos X (μ-pos-elim X c δ (λ {g} p → Cns X g) ε p) h)
    --             → P (μ-pos X (μ X c δ) (μ-pos-elim X c δ (λ {g} p → Cns X g) ε) p q ))
    --   → {g : Frm X} (p : Pos X (μ X (μ X c δ)
    --            (μ-pos-elim X c δ (λ {g} p → Cns X g) ε)) g)
    --   → μ-pos-elim X (μ X c δ) (μ-pos-elim X c δ (λ {g} p → Cns X g) ε) P μ-pos* p 
    --     ↦ μ-pos-elim X c (λ p → μ X (δ p) (ε p)) P
    --         (λ p → μ-pos-elim X (δ p) (ε p)
    --                (λ q → P (μ-pos X c (λ p₂ → μ X (δ p₂) (ε p₂)) p q))
    --                (λ q r → μ-pos* (μ-pos X c δ p q) r)) p



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
          ε' {g} p = graft (ε {g} p) (ϕ' p) (λ q r → ψ (μ-pos Xₙ (cns φ) δ p q) r) (κ' p) 
      in {!μ-dec (μ Xₙ (cns φ) δ) ϕ ψ !} 

      -- nd : (φ : SlcFrm)
      --   → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
      --   → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
      --          {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
      --   → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
      --        → Web ⟪ g , δ p , src φ p , θ p ⟫)
      --   → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫ 

  -- γₒ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (τ : 𝒯r o ρ)
  --   → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
  --   → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
  --   → 𝒯r o (μₒ ρ δ)
  -- γₒ o .(ηₒ o) (lf .o) ϕ ψ = ψ (ηₒ-pos o)
  -- γₒ o .(μₒ ρ δ) (nd .o ρ δ ε) ϕ ψ = 
  --   let ϕ' p q = ϕ (μₒ-pos ρ δ p q)
  --       ψ' p q = ψ (μₒ-pos ρ δ p q)
  --       δ' p = μₒ (δ p) (ϕ' p)
  --       ε' p = γₒ (Typ ρ p) (δ p) (ε p) (ϕ' p) (ψ' p) 
  --   in nd o ρ δ' ε'

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

