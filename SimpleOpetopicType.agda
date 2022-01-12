{-# OPTIONS --without-K --rewriting #-}

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
      → (p : P (η-pos X f))
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
      → (p : {g : Frm X} (p : Pos X c g)
             {h : Frm X} (q : Pos X (δ p) h)
             → P {h} (μ-pos X c δ p q))
      → {g : Frm X} (p : Pos X (μ X c δ) g)
      → P {g} p              

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
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ
        cns : Cns Xₙ frm
        tgt : Xₛₙ frm
        src : {f : Frm Xₙ} (p : Pos Xₙ cns f) → Xₛₙ f 

    open SlcFrm
    
    data NewWeb : SlcFrm → Set ℓ where

      lf : {f : Frm Xₙ} (x : Xₛₙ f)
        → NewWeb ⟪ f , η Xₙ f , x , η-dec f x ⟫ 

      nd : (φ : SlcFrm)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → NewWeb ⟪ g , δ p , src φ p , θ p ⟫)
        → NewWeb ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ θ ⟫ 

    data NewWebPos : {φ : SlcFrm} (ω : NewWeb φ) → SlcFrm → Set ℓ where

      nd-here : (φ : SlcFrm)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → NewWeb ⟪ g , δ p , src φ p , θ p ⟫)
        → NewWebPos (nd φ δ θ ε) φ

      nd-there : (φ : SlcFrm)
        → (δ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g) → Cns Xₙ g)
        → (θ : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
               {h : Frm Xₙ} (q : Pos Xₙ (δ p) h) → Xₛₙ h)
        → (ε : {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
             → NewWeb ⟪ g , δ p , src φ p , θ p ⟫)
        → {g : Frm Xₙ} (p : Pos Xₙ (cns φ) g)
        → {ψ : SlcFrm} (ρ : NewWebPos (ε p) ψ)
        → NewWebPos (nd φ δ θ ε) ψ 

  -- 
  --  Webs, their positions, and grafting 
  --

  data Web {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) :
    (f : Frm Xₙ) (x : Xₛₙ f) (c : Cns Xₙ f)
    (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g) → Set ℓ where

    lf : {f : Frm Xₙ} (x : Xₛₙ f)
      → Web Xₙ Xₛₙ f x (η Xₙ f) (η-pos-elim Xₙ f (λ {g} p → Xₛₙ g) x) 

    nd : {f : Frm Xₙ} (c : Cns Xₙ f) (x : Xₛₙ f) 
      → (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g)
      → (δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g)
      → (θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
             {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
           → Xₛₙ h)
      → (ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
           → Web Xₙ Xₛₙ g (ν p) (δ p) (θ p))
      → Web Xₙ Xₛₙ f x (μ Xₙ c δ)
          (μ-pos-elim Xₙ c δ (λ {g} p → Xₛₙ g) θ) 

  data WebPos {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) : 
    {f : Frm Xₙ} {x : Xₛₙ f} {c : Cns Xₙ f}
    {ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g}
    (ρ : Web Xₙ Xₛₙ f x c ν)
    (g : Frm Xₙ) (y : Xₛₙ g) (d : Cns Xₙ g)
    (θ : {h : Frm Xₙ} (p : Pos Xₙ d h) → Xₛₙ h)  → Set ℓ where

    nd-here : {f : Frm Xₙ} {c : Cns Xₙ f} {x : Xₛₙ f}
      → {ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g}
      → {δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g}
      → {θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
             {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
           → Xₛₙ h}
      → {ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
           → Web Xₙ Xₛₙ g (ν p) (δ p) (θ p)}
      → WebPos Xₙ Xₛₙ (nd c x ν δ θ ε) f x c ν 

    nd-there : {f : Frm Xₙ} {c : Cns Xₙ f} {x : Xₛₙ f}
      → {ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g}
      → {δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g}
      → {θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
             {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
           → Xₛₙ h}
      → {ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
           → Web Xₙ Xₛₙ g (ν p) (δ p) (θ p)}
      → {g : Frm Xₙ} (p : Pos Xₙ c g)
      → {h : Frm Xₙ} {y : Xₛₙ h} {d : Cns Xₙ h}
      → {ρ : {k : Frm Xₙ} (q : Pos Xₙ d k) → Xₛₙ k}
      → (q : WebPos Xₙ Xₛₙ (ε p) h y d ρ)
      → WebPos Xₙ Xₛₙ (nd c x ν δ θ ε) h y d ρ

    -- γ : {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ)
    --   → (f : Frm Xₙ) (x : Xₛₙ f) (c : Cns Xₙ f)
    --   → (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g) 
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ω : Web Xₙ Xₛₙ f x c ν)

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


  𝕆 = {!!}
  Frm = {!!}
  Cns = {!!} 
  Pos = {!!} 
