{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType

module OpetopicMap where

  infixr 40 _⇒_

  _⇒_ : ∀ {ℓ₀ ℓ₁ n} → 𝕆 ℓ₀ n → 𝕆 ℓ₁ n
    → Set (ℓ-max ℓ₀ ℓ₁)

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
    → {o : 𝒪 n} → Frm X o → Frm Y o
    
  Cns⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
    → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm X o}
    → Cns X f ρ → Cns Y (Frm⇒ α f) ρ

  postulate

    Shp-Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
      → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm X o} (c : Cns X f ρ) (p : Pos ρ)
      → Frm⇒ α (Shp X c p) ↦ Shp Y (Cns⇒ α c) p
    {-# REWRITE Shp-Frm⇒ #-} 

    η⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
      → {o : 𝒪 n} (f : Frm X o)
      → Cns⇒ α (η X f) ↦ η Y (Frm⇒ α f)
    {-# REWRITE η⇒ #-} 

    μ⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → Cns⇒ α (μ X c κ) ↦ μ Y (Cns⇒ α c) (λ p → Cns⇒ α (κ p))
    {-# REWRITE μ⇒ #-}

  module _ {ℓ₀ ℓ₁ n} {Xₙ : 𝕆 ℓ₀ n} {Yₙ : 𝕆 ℓ₁ n}
           (Xₛₙ : {o : 𝒪 n} → Frm Xₙ o → Set ℓ₀)
           (Yₛₙ : {o : 𝒪 n} → Frm Yₙ o → Set ℓ₁)
           (αₙ : Xₙ ⇒ Yₙ) (αₛₙ : {o : 𝒪 n} {f : Frm Xₙ o} → Xₛₙ f → Yₛₙ (Frm⇒ αₙ f)) where

    -- Bingo!
    WebFrm⇒ : {o : 𝒪 n} {ρ : 𝒫 o}
      → WebFrm Xₙ Xₛₙ o ρ → WebFrm Yₙ Yₛₙ o ρ 
    WebFrm⇒ φ = ⟪ Frm⇒ αₙ (frm φ) , Cns⇒ αₙ (cns φ) ,
                  αₛₙ (tgt φ) , (λ p → αₛₙ (src φ p)) ⟫ 

    Web⇒ : {o : 𝒪 n} {ρ : 𝒫 o}
      → {φ : WebFrm Xₙ Xₛₙ o ρ} {τ : 𝒯r o ρ}
      → Web Xₙ Xₛₙ φ τ → Web Yₙ Yₛₙ (WebFrm⇒ φ) τ 
    Web⇒ (lf x) = lf (αₛₙ x)
    Web⇒ (nd φ ι κ δ ν ε) =
      nd (WebFrm⇒ φ) ι κ
        (λ p → Cns⇒ αₙ (δ p))
        (λ p q → αₛₙ (ν p q))
        (λ p → Web⇒ (ε p))

  _⇒_ {n = O} _ _ = ⊤
  _⇒_ {n = S n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Σ (Xₙ ⇒ Yₙ) (λ α →
     {o : 𝒪 n} {f : Frm Xₙ o}
     → Xₛₙ f → Yₛₙ (Frm⇒ α f))

  Frm⇒ {n = O} α _ = tt
  Frm⇒ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) =
    WebFrm⇒ Xₛₙ Yₛₙ αₙ αₛₙ

  Cns⇒ {n = O} _ _ = tt
  Cns⇒ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) =
    Web⇒ Xₛₙ Yₛₙ αₙ αₛₙ
  
  --
  --  Composition
  --

  infixr 30 _⊚_
  
  _⊚_ : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n}
    → (Y ⇒ Z) → (X ⇒ Y) → (X ⇒ Z)

  postulate

    ⊚-Frm : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n}
      → (α : Y ⇒ Z) (β : X ⇒ Y) (o : 𝒪 n) (f : Frm X o)
      → Frm⇒ (α ⊚ β) f ↦ Frm⇒ α (Frm⇒ β f)
    {-# REWRITE ⊚-Frm #-}

    ⊚-assoc : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃ n}
      → {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n} {W : 𝕆 ℓ₃ n}
      → (α : Z ⇒ W) (β : Y ⇒ Z) (γ : X ⇒ Y)
      → (α ⊚ β) ⊚ γ ↦ α ⊚ β ⊚ γ
    {-# REWRITE ⊚-assoc #-}

    -- And unit laws ...

  _⊚_ {n = O} α β = tt
  _⊚_ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (αₙ , αₛₙ) (βₙ , βₛₙ) =
    αₙ ⊚ βₙ , λ x → αₛₙ (βₛₙ x)

  po-to-Σ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    → {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁}
    → (p : a₀ ≡ a₁) (q : b₀ ≡ b₁ [ B ↓ p ])
    → (a₀ , b₀) ≡ (a₁ , b₁)
  po-to-Σ refl refl = refl

  --
  -- Equality of functions
  --
  
  _⇒-≡_ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} 
    → (X ⇒ Y) → (X ⇒ Y) → Set (ℓ-max ℓ₀ ℓ₁)

  postulate
  
    ⇒-≡-to-≡ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} 
      → (α : X ⇒ Y) (β : X ⇒ Y)
      → α ⇒-≡ β → α ≡ β

  _⇒-≡_ {n = O} {X} {Y} α β = ⊤
  _⇒-≡_ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) (βₙ , βₛₙ) =
    Σ (αₙ ⇒-≡ βₙ) (λ e → {o : 𝒪 n} {f : Frm Xₙ o}
      (x : Xₛₙ f) → αₛₙ x ≡ βₛₙ x [ (λ ϕ → Yₛₙ (Frm⇒ ϕ f)) ↓ ⇒-≡-to-≡ αₙ βₙ e ] )

  -- And this last thing is by fun-ext.
  -- ⇒-≡-to-≡ {n = O} {X} {Y} α β e = refl
  -- ⇒-≡-to-≡ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) (βₙ , βₛₙ) (eₙ , eₛₙ) =
  --   po-to-Σ (⇒-≡-to-≡ αₙ βₙ eₙ) {!!}

