open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.OpetopicTerm
open import Native.Weakening

module Native.OpetopicMap where

  --
  --  Maps of Opetopic Types (as terms)
  --

  _⇒_ : ∀ {ℓ₀ ℓ₁ n} → 𝕆Type ℓ₀ n → 𝕆Type ℓ₁ n
    → Type (ℓ-max ℓ₀ ℓ₁)
  X ⇒ Y = 𝕆Term X (Wk X Y) 

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y) → {ο : 𝕆 n} → Frm X ο → Frm Y ο 
  Frm⇒ {X = X} {Y} σ f = πFrm X Y (Frm↑ σ f) 
  
  Web⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y)   
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (ω : Web X f ρ)
    → Web Y (Frm⇒ σ f) ρ
  Web⇒ {X = X} {Y} σ ω = πWeb X Y (Web↑ σ ω) 

  --
  --  Substitution - i.e. pulling back along a map
  --

  Subst : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (τ : X ⇒ Y) (Y↓ : 𝕆Type↓ ℓ₂ Y)
    → 𝕆Type↓ ℓ₂ X

  Frm← : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (τ : X ⇒ Y) (Y↓ : 𝕆Type↓ ℓ₂ Y)
    → {ο : 𝕆 n} (f : Frm X ο)
    → Frm↓ (Subst τ Y↓) f
    → Frm↓ Y↓ (Frm⇒ τ f)

  Web← : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (τ : X ⇒ Y) (Y↓ : 𝕆Type↓ ℓ₂ Y)
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (ω : Web X f ρ)
    → {f↓ : Frm↓ (Subst τ Y↓) f}
    → Web↓ (Subst τ Y↓) f↓ ω
    → Web↓ Y↓ (Frm← τ Y↓ f f↓) (Web⇒ τ ω)

  postulate

    Shp↓-Web← : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (τ : X ⇒ Y) (Y↓ : 𝕆Type↓ ℓ₂ Y)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → {f↓ : Frm↓ (Subst τ Y↓) f}
      → (ω↓ : Web↓ (Subst τ Y↓) f↓ ω)
      → (p : Pos ρ)
      → Shp↓ Y↓ (Web← τ Y↓ ω ω↓) p ↦ Frm← τ Y↓ (Shp X ω p) (Shp↓ (Subst τ Y↓) ω↓ p)
    {-# REWRITE Shp↓-Web← #-}

    Web←-η : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (τ : X ⇒ Y) (Y↓ : 𝕆Type↓ ℓ₂ Y)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {f↓ : Frm↓ (Subst τ Y↓) f}
      → Web← τ Y↓ (η X f) (η↓ (Subst τ Y↓) f↓) ↦ η↓ Y↓ (Frm← τ Y↓ f f↓) 
    {-# REWRITE Web←-η #-}

    Web←-μ : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
      → (τ : X ⇒ Y) (Y↓ : 𝕆Type↓ ℓ₂ Y)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
      → {f↓ : Frm↓ (Subst τ Y↓) f}
      → (ω↓ : Web↓ (Subst τ Y↓) f↓ ω)
      → (ϵ↓ : (p : Pos ρ) → Web↓ (Subst τ Y↓) (Shp↓ (Subst τ Y↓) ω↓ p) (ϵ p))
      → Web← τ Y↓ (μ X ω ϵ) (μ↓ (Subst τ Y↓) ω↓ ϵ↓) ↦
          μ↓ Y↓ (Web← τ Y↓ ω ω↓ ) λ p → Web← τ Y↓ (ϵ p) (ϵ↓ p)
    {-# REWRITE Web←-μ #-} 

  Subst {X = ○} {○} τ P = ○↓
  Subst {X = X ∥ P} {Y ∥ Q} (τₙ ► τₛₙ) (Y↓ ∥↓ Q↓) =
    Subst τₙ Y↓ ∥↓ λ {i} p i↓ → Q↓ (τₛₙ p) (Frm← τₙ Y↓ (snd i) i↓)

  Frm← {X = ○} {○} ■ ○↓ ● ●↓ = ●↓
  Frm← {X = X ∥ P} {Y ∥ Q} (τₙ ► τₛₙ) (Y↓ ∥↓ Q↓) (f ►⟦ t ∣ ρ , ω , ν ⟧) (f↓ ►⟦ t↓ ∣ ω↓ , ν↓ ⟧↓) =
    Frm← τₙ Y↓ f f↓ ►⟦ t↓ ∣ Web← τₙ Y↓ ω ω↓ , (λ p → ν↓ p) ⟧↓

  Web← {X = ○} {○} ■ ○↓ arr arr↓ = arr↓
  Web← {X = X ∥ P} {Y ∥ Q} (τₙ ► τₛₙ) (Y↓ ∥↓ W↓) (lf t) (lf↓ t↓) = lf↓ t↓
  Web← {X = X ∥ P} {Y ∥ Q} (τₙ ► τₛₙ) (Y↓ ∥↓ W↓) (nd t s δ) (nd↓ t↓ s↓ δ↓) =
      nd↓ t↓ (Web← τₙ Y↓ (s .snd .fst) (s↓ .fst) , (λ p → s↓ .snd p))
             (λ p → (Web← τₙ Y↓ (δ p .fst .snd .fst) (δ↓ p .fst .fst) , snd (fst (δ↓ p))) ,
                    (Web← (τₙ ► τₛₙ) (Y↓ ∥↓ W↓) (snd (snd (δ p))) (δ↓ p .snd)))
