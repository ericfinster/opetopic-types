open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

module Native.Weakening where

  Wk : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → 𝕆Type↓ ℓ₁ X

  πFrm : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → {ο : 𝕆 n} {f : Frm X ο}
    → Frm↓ (Wk X Y) f → Frm Y ο 

  πWeb : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → {ο : 𝕆 n} {ρ : ℙ ο}
    → {f : Frm X ο} {ω : Web X f ρ}
    → {f↓ : Frm↓ (Wk X Y) f}
    → (ω↓ : Web↓ (Wk X Y) ω f↓)
    → Web Y (πFrm X Y f↓) ρ 

  postulate

    Shp-πWeb : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
      → {ο : 𝕆 n} {ρ : ℙ ο}
      → {f : Frm X ο} {ω : Web X f ρ}
      → {f↓ : Frm↓ (Wk X Y) f}
      → (ω↓ : Web↓ (Wk X Y) ω f↓)
      → (p : Pos ρ)
      → Shp Y (πWeb X Y ω↓) p ↦ πFrm X Y (Shp↓ (Wk X Y) ω↓ p)
    {-# REWRITE Shp-πWeb #-} 

    πWeb-η : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} (Y : 𝕆Type ℓ₁ n)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ (Wk X Y) f)
      → πWeb X Y (η↓ (Wk X Y) f↓) ↦ η Y (πFrm X Y f↓)
    {-# REWRITE πWeb-η #-}

    πWeb-μ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} (Y : 𝕆Type ℓ₁ n)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ (Wk X Y) f)
      → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ (Wk X Y) ω f↓)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
      → (ϵ↓ : (p : Pos ρ) → Web↓ (Wk X Y) (ϵ p) (Shp↓ (Wk X Y) ω↓ p))
      → πWeb X Y (μ↓ (Wk X Y) ω↓ ϵ↓) ↦ μ Y (πWeb X Y ω↓) (λ p → πWeb X Y (ϵ↓ p))
    {-# REWRITE πWeb-μ #-}


  πIdx : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → {i : Idx X} (i↓ : Idx↓ (Wk X Y) i)
    → Idx Y
  πIdx X Y {ο , f} f↓ = (ο , πFrm X Y f↓)

  Wk-cell : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (P : Idx X → Type ℓ₀) (Q : Idx Y → Type ℓ₁)
    → {i : Idx X} → P i → Idx↓ (Wk X Y) i → Type ℓ₁
  Wk-cell {X = X} {Y} P Q _ i↓ = Q (πIdx X Y i↓)

  πSrc : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (P : Idx X → Type ℓ₀)
    → (Q : Idx Y → Type ℓ₁)
    → {i : Idx X} {s : Src X P i}
    → {i↓ : Idx↓ (Wk X Y) i} (s↓ : Src↓ (Wk X Y) (Wk-cell P Q) s i↓)
    → Src Y Q (πIdx X Y i↓)
  πSrc {X = X} {Y} P Q {s = ρ , ω , δ} (ω↓ , δ↓) =
    ρ , πWeb X Y ω↓ , δ↓ 

  Wk ○ ○ = ○↓
  Wk (X ∥ P) (Y ∥ Q) =
    Wk X Y ∥↓ Wk-cell P Q

  {-# TERMINATING #-}
  πFrm ○ ○ ●↓ = ●
  πFrm (X ∥ P) (Y ∥ Q) {f = f ►⟦ t ∣ s ⟧} (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) =
    πFrm X Y f↓ ►⟦ t↓ ∣ s .fst , πWeb X Y (s↓ .fst) , (λ p → s↓ .snd p) ⟧

  πBranch : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (P : Idx X → Type ℓ₀)
    → (Q : Idx Y → Type ℓ₁)
    → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)}
    → {b : Branch X P t}
    → {f↓ : Frm↓ (Wk X Y) f} {t↓ : Wk-cell P Q t f↓}
    → Branch↓ (Wk X Y) (Wk-cell P Q) b t↓
    → Branch Y Q t↓
  πBranch P Q {b = s , tr , ω} (s↓ , ω↓) =
    πSrc P Q {s = s} s↓ , tr , πWeb (_ ∥ P) (_ ∥ Q) ω↓

  πWeb ○ ○ arr↓ = arr
  πWeb (X ∥ P) (Y ∥ Q) (lf↓ t↓) = lf t↓
  πWeb (X ∥ P) (Y ∥ Q) (nd↓ {s = ρ , ω , δ} {ϵ}  t↓ (ω↓ , δ↓) ϵ↓) =
    nd t↓ (ρ , πWeb X Y ω↓ , δ↓) (λ p → πBranch P Q (ϵ↓ p))


