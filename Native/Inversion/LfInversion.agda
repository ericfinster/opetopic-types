{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.Universe

open import Cubical.Foundations.Everything

module Native.Inversion.LfInversion where

  --
  --  Inverting Lf↓
  --

  module _ {ℓ n} {ο : 𝕆 n} (F : Frm (𝕌 ℓ n) ο) (T : 𝕌-cell (ο , F)) where

    lf-data : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓) → Type ℓ
    lf-data {f↓} s↓ = Σ[ t↓ ∈ T f↓ ] (𝕍ret T t↓ ≡ s↓)

    web-over : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓) → Type ℓ
    web-over {f↓} s↓ = Σ[ t↓ ∈ T f↓ ] (Web↓ (𝕍 ℓ (suc n)) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) (lf T)) 

    src-over-lf-to : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓)
      → lf-data s↓ → web-over s↓
    src-over-lf-to {f↓} s↓ (t↓ , σ↓) =
      J (λ s↓' _ → Σ[ t↓ ∈ T f↓ ] (Web↓ (𝕍 ℓ (suc n)) (f↓ ►⟦ t↓ ∣ s↓' ⟧↓) (lf T)))
      (t↓ , lf↓ t↓) σ↓ 

    src-over-lf-from : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓)
      → web-over s↓ → lf-data s↓
    src-over-lf-from ._(t↓ , lf↓ .t↓) = t↓ , refl

    src-over-lf-section : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓) 
      → section (src-over-lf-to s↓) (src-over-lf-from s↓)
    src-over-lf-section ._ (t↓ , lf↓ .t↓) = transportRefl (t↓ , lf↓ t↓)

    src-over-lf-retract : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓)
      → retract (src-over-lf-to s↓) (src-over-lf-from s↓)
    src-over-lf-retract s↓ (t↓ , p) = 
      J (λ s↓' p' → src-over-lf-from s↓' (src-over-lf-to s↓' (t↓ , p')) ≡ (t↓ , p')) lem p

      where lem = src-over-lf-from (𝕍ret T t↓) (src-over-lf-to (𝕍ret T t↓) (t↓ , refl))
                      ≡[ i ]⟨ src-over-lf-from (𝕍ret T t↓) (transportRefl (t↓ , lf↓ t↓) i) ⟩ 
                  (t↓ , refl) ∎

    src-over-lf-equiv : {f↓ : Frm↓ (𝕍 ℓ n) F} (s↓ : 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓)
      → lf-data s↓ ≃ web-over s↓
    src-over-lf-equiv s↓ = isoToEquiv
      (iso (src-over-lf-to s↓) (src-over-lf-from s↓)
           (src-over-lf-section s↓) (src-over-lf-retract s↓))
