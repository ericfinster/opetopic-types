open import Core.Prelude 
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.Universe

open import MiniHoTT

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
      → ret↓ X↓ P↓ t↓ == s↓
    lf-data-to ._ ._ (lf↓ t↓) = idp

    lf-data-from : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → ret↓ X↓ P↓ t↓ == s↓
      → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
    lf-data-from {f↓} t↓ s↓ p = J (λ s↓' p' → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓' ⟧↓)) (lf↓ t↓) p 

    lf-data-section : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → (p : ret↓ X↓ P↓ t↓ == s↓)
      → lf-data-to t↓ s↓ (lf-data-from t↓ s↓ p) == p
    lf-data-section {f↓} t↓ s↓ p = J (λ s↓' p' → lf-data-to t↓ s↓' (lf-data-from t↓ s↓' p') == p') idp p
    
    lf-data-retract : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → (ω : Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓))
      → lf-data-from t↓ s↓ (lf-data-to t↓ s↓ ω) == ω
    lf-data-retract ._ ._ (lf↓ t↓) = idp

    src-over-lf-equiv : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ (ret X P t) f↓)
      → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
      ≃ (ret↓ X↓ P↓ t↓ == s↓)
    src-over-lf-equiv t↓ s↓ = equiv
      (lf-data-to t↓ s↓) (lf-data-from t↓ s↓)
      (lf-data-section t↓ s↓) (lf-data-retract t↓ s↓)


