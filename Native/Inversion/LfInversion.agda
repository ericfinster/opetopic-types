{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.Universe

open import Cubical.Foundations.Everything

module Native.Inversion.LfInversion where

  -- Acutually, this has nothing to do with the universe any more.
  -- This is generic for dependent opetopic types.  That might
  -- make things kind easier ...

  -- Web↓-rec : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
  --   → {ο : 𝕆 n} {f : Frm X ο} 
  --   → {ρ : ℙ ο} (ω : Web X f ρ)
  --   → (f↓ : Frm↓ X↓ f) → Type ℓ↓
  -- Web↓-rec ○↓ arr f↓ = 𝟙 _
  -- Web↓-rec (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) =
  --   s↓ ≡ ret↓ X↓ P↓ t↓
  -- Web↓-rec (X↓ ∥↓ P↓) (nd t s δ) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) =
  --   {!!}

  --
  --  Inverting Lf↓
  --

  module _ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    {P : Idx X → Type ℓ}
    {P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓}
    {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)}
    where

    lf-data-to : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
      → ret↓ X↓ P↓ t↓ ≡ s↓
    lf-data-to ._ ._ (lf↓ t↓) = refl

    lf-data-from : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → ret↓ X↓ P↓ t↓ ≡ s↓
      → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
    lf-data-from {f↓} t↓ s↓ p = J (λ s↓' p' → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓' ⟧↓)) (lf↓ t↓) p 

    lf-data-section : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → section (lf-data-to t↓ s↓) (lf-data-from t↓ s↓)
    lf-data-section {f↓} t↓ s↓ p = J (λ s↓' p' → lf-data-to t↓ s↓' (lf-data-from t↓ s↓' p') ≡ p') {!!} p 

  -- module _ {ℓ n} {ο : 𝕆 n} (F : Frm (𝕌 ℓ n) ο) (T : 𝕌-cell (ο , F)) where

  --   lf-data : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓) → Type ℓ
  --   lf-data {f↓} s↓ = Σ[ t↓ ∈ T f↓ ] (𝕍ret T t↓ ≡ s↓)

  --   web-over : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓) → Type ℓ
  --   web-over {f↓} s↓ = Σ[ t↓ ∈ T f↓ ] (Web↓ (𝕍 ℓ (suc n)) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) (lf T)) 

  --   src-over-lf-to : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓)
  --     → lf-data s↓ → web-over s↓
  --   src-over-lf-to {f↓} s↓ (t↓ , σ↓) =
  --     J (λ s↓' _ → Σ[ t↓ ∈ T f↓ ] (Web↓ (𝕍 ℓ (suc n)) (f↓ ►⟦ t↓ ∣ s↓' ⟧↓) (lf T)))
  --     (t↓ , lf↓ t↓) σ↓ 

  --   src-over-lf-from : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓)
  --     → web-over s↓ → lf-data s↓
  --   src-over-lf-from ._(t↓ , lf↓ .t↓) = t↓ , refl

  --   src-over-lf-section : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓) 
  --     → section (src-over-lf-to s↓) (src-over-lf-from s↓)
  --   src-over-lf-section ._ (t↓ , lf↓ .t↓) = transportRefl (t↓ , lf↓ t↓)

  --   src-over-lf-retract : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓)
  --     → retract (src-over-lf-to s↓) (src-over-lf-from s↓)
  --   src-over-lf-retract s↓ (t↓ , p) = 
  --     J (λ s↓' p' → src-over-lf-from s↓' (src-over-lf-to s↓' (t↓ , p')) ≡ (t↓ , p')) lem p

  --     where lem = src-over-lf-from (𝕍ret T t↓) (src-over-lf-to (𝕍ret T t↓) (t↓ , refl))
  --                     ≡[ i ]⟨ src-over-lf-from (𝕍ret T t↓) (transportRefl (t↓ , lf↓ t↓) i) ⟩ 
  --                 (t↓ , refl) ∎

  --   src-over-lf-equiv : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (𝕌ret T) f↓)
  --     → lf-data s↓ ≃ web-over s↓
  --   src-over-lf-equiv s↓ = isoToEquiv
  --     (iso (src-over-lf-to s↓) (src-over-lf-from s↓)
  --          (src-over-lf-section s↓) (src-over-lf-retract s↓))
