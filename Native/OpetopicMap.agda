open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType

module Native.OpetopicMap where

  --
  --  Maps of Opetopic Types
  --

  infixl 50 _⊙_

  data _⇒_  {ℓ₀ ℓ₁} : {n : ℕ} → 𝕆Type ℓ₀ n → 𝕆Type ℓ₁ n → Type (ℓ-max ℓ₀ ℓ₁)

  id-map : ∀ {ℓ n} → (X : 𝕆Type ℓ n) → X ⇒ X

  _⊙_ : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n}
    → {Y : 𝕆Type ℓ₁ n} {Z : 𝕆Type ℓ₂ n}
    → Y ⇒ Z → X ⇒ Y → X ⇒ Z

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y) → {ο : 𝕆 n} → Frm X ο → Frm Y ο 

  Web⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y)   
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (ω : Web X f ρ)
    → Web Y (Frm⇒ σ f) ρ

  postulate

    --
    --  Equations for maps
    -- 

    map-unit-l : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (σ : X ⇒ Y)
      → id-map Y ⊙ σ ↦ σ
    {-# REWRITE map-unit-l #-}

    map-unit-r : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (σ : X ⇒ Y)
      → σ ⊙ id-map X ↦ σ
    {-# REWRITE map-unit-r #-}

    map-assoc : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → {Z : 𝕆Type ℓ₂ n} {W : 𝕆Type ℓ₃ n}
      → (ρ : X ⇒ Y) (σ : Y ⇒ Z) (τ : Z ⇒ W)
      → τ ⊙ (σ ⊙ ρ) ↦ τ ⊙ σ ⊙ ρ
    {-# REWRITE map-assoc #-} 

    -- 
    --  Frame compatibilities
    --
    
    Frm⇒-id : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → {ο : 𝕆 n} (f : Frm X ο)
      → Frm⇒ (id-map X) f ↦ f
    {-# REWRITE Frm⇒-id #-}

    Frm⇒-⊙ : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n}
      → {Y : 𝕆Type ℓ₁ n} {Z : 𝕆Type ℓ₂ n}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z)
      → {ο : 𝕆 n} (f : Frm X ο)
      → Frm⇒ (τ ⊙ σ) f ↦ Frm⇒ τ (Frm⇒ σ f) 
    {-# REWRITE Frm⇒-⊙ #-}

    --
    --  Web compatibilities
    --

    Web⇒-id : ∀ {ℓ₀ n} {X : 𝕆Type ℓ₀ n} 
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → Web⇒ (id-map X) ω ↦ ω 
    {-# REWRITE Web⇒-id #-}

    Web⇒-⊙ : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n}
      → {Y : 𝕆Type ℓ₁ n} {Z : 𝕆Type ℓ₂ n}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z)
      → {ο : 𝕆 n} (f : Frm X ο)
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → Web⇒ (τ ⊙ σ) ω ↦ Web⇒ τ (Web⇒ σ ω)
    {-# REWRITE Web⇒-⊙ #-}

    --
    --  Shape compatibilities
    --

    Frm⇒-Shp : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (σ : X ⇒ Y)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → (p : Pos ρ)
      → Frm⇒ σ (Shp X ω p) ↦ Shp Y (Web⇒ σ ω) p 
    {-# REWRITE Frm⇒-Shp #-}
    
    --
    --  Monadic compatibilites
    --
    
    Web⇒-η : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (σ : X ⇒ Y) 
      → {ο : 𝕆 n} (f : Frm X ο)
      → Web⇒ σ (η X f) ↦ η Y (Frm⇒ σ f)
    {-# REWRITE Web⇒-η #-}
    
    Web⇒-μ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (σ : X ⇒ Y) 
      → {ο : 𝕆 n} (f : Frm X ο)
      → {ρ : ℙ ο} (s : Web X f ρ)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → (ϵ : (p : Pos ρ) → Web X (Shp X s p) (δ p))
      → Web⇒ σ (μ X s ϵ) ↦ μ Y (Web⇒ σ s) (λ p → Web⇒ σ (ϵ p))
    {-# REWRITE Web⇒-μ #-} 

  --
  --  Indexed versions
  --
  
  Idx⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y) → Idx X → Idx Y
  Idx⇒ σ (ο , f) = ο , Frm⇒ σ f 

  Src⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → {P : Idx X → Type ℓ₀}
    → {Q : Idx Y → Type ℓ₁}
    → (σₙ : X ⇒ Y) (σₛₙ : {i : Idx X} → P i → Q (Idx⇒ σₙ i))
    → {i : Idx X} (s : Src X P i)
    → Src Y Q (Idx⇒ σₙ i) 
  Src⇒ σₙ σₛₙ (ρ , ω , δ) = ρ , Web⇒ σₙ ω , λ p → σₛₙ (δ p)

  --
  --  Implementations
  --

  {-# NO_UNIVERSE_CHECK #-}
  data _⇒_ {ℓ₀} {ℓ₁} where

    ○⇒ : ○ ⇒ ○ 

    _∥⇒_ : {n : ℕ} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → {P : Idx X → Type ℓ₀} {Q : Idx Y → Type ℓ₁}
      → (σₙ : X ⇒ Y) (σₛₙ : {i : Idx X} → P i → Q (Idx⇒ σₙ i))
      → (X ∥ P) ⇒ (Y ∥ Q)

  id-map ○ = ○⇒
  id-map (X ∥ P) = id-map X ∥⇒ (λ p → p)

  ○⇒ ⊙ ○⇒ = ○⇒
  (σₙ ∥⇒ σₛₙ) ⊙ (τₙ ∥⇒ τₛₙ) =
    σₙ ⊙ τₙ ∥⇒ (λ p → σₛₙ (τₛₙ p))

  Frm⇒ ○⇒ {objₒ} ● = ●
  Frm⇒ {Y = Y ∥ Q} (σₙ ∥⇒ σₛₙ) (f ►⟦ t ∣ s ⟧) =
    Frm⇒ σₙ f ►⟦ σₛₙ t ∣ Src⇒ {Q = Q} σₙ σₛₙ s ⟧

  Web⇒ ○⇒ arr = arr
  Web⇒ (σₙ ∥⇒ σₛₙ) (lf t) = lf (σₛₙ t)
  Web⇒ {X = X ∥ P} {Y = Y ∥ Q} (σₙ ∥⇒ σₛₙ) (nd t s δ) =
    nd (σₛₙ t) (Src⇒ {Q = Q} σₙ σₛₙ s)
      (λ p → Src⇒ {Q = Q} σₙ σₛₙ (δ p .fst) , δ p .snd .fst ,
        Web⇒ {Y = Y ∥ Q} (σₙ ∥⇒ σₛₙ) {f = Shp X (fst (s .snd)) p ►⟦ s .snd .snd p ∣ fst (δ p) ⟧} (δ p .snd .snd))

