open import Core.Prelude 
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.Universe

open import MiniHoTT

module Native.Inversion.NdInversion where

  module _ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    {P : Idx X → Type ℓ}
    {P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓}
    {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)}
    {s : Src X P (ο , f)} {δ : (p : Pos (s .fst)) → Branch X P (s .snd .snd p)}
    where

    nd-data-to : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
      → (s↓ : Src↓ X↓ P↓ (join X P (s .fst , s .snd .fst , λ p → δ p .fst)) f↓)
      → Web↓ (X↓ ∥↓ P↓) (nd t s δ) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
      → Σ[ σ↓ ∈ Src↓ X↓ P↓ s f↓ ]
        Σ[ δ↓ ∈ ((p : Pos (s .fst)) → Branch↓ X↓ P↓ (δ p) (σ↓ .snd p)) ]
        join↓ X↓ P↓ (σ↓ .fst , λ p → δ↓ p .fst) == s↓
    nd-data-to ._ ._ (nd↓ t↓ s↓ δ↓) = s↓ , δ↓ , idp

    nd-data-from : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
      → (s↓ : Src↓ X↓ P↓ (join X P (s .fst , s .snd .fst , λ p → δ p .fst)) f↓)
      → Σ[ σ↓ ∈ Src↓ X↓ P↓ s f↓ ]
        Σ[ δ↓ ∈ ((p : Pos (s .fst)) → Branch↓ X↓ P↓ (δ p) (σ↓ .snd p)) ]
        join↓ X↓ P↓ (σ↓ .fst , λ p → δ↓ p .fst) == s↓
      → Web↓ (X↓ ∥↓ P↓) (nd t s δ) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
    nd-data-from t↓ ._ (σ↓ , δ↓ , idp) = nd↓ t↓ σ↓ δ↓ 

    nd-data-to-from : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
      → (s↓ : Src↓ X↓ P↓ (join X P (s .fst , s .snd .fst , λ p → δ p .fst)) f↓)
      → (θ : Σ[ σ↓ ∈ Src↓ X↓ P↓ s f↓ ]
             Σ[ δ↓ ∈ ((p : Pos (s .fst)) → Branch↓ X↓ P↓ (δ p) (σ↓ .snd p)) ]
             join↓ X↓ P↓ (σ↓ .fst , λ p → δ↓ p .fst) == s↓)
      → nd-data-to t↓ s↓ (nd-data-from t↓ s↓ θ) == θ
    nd-data-to-from t↓ ._ (σ↓ , δ↓ , idp) = idp

    nd-data-from-to : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
      → (s↓ : Src↓ X↓ P↓ (join X P (s .fst , s .snd .fst , λ p → δ p .fst)) f↓)
      → (ω : Web↓ (X↓ ∥↓ P↓) (nd t s δ) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓))
      → nd-data-from t↓ s↓ (nd-data-to t↓ s↓ ω) == ω
    nd-data-from-to ._ ._ (nd↓ t↓ s↓ δ↓) = idp 

    nd-data-equiv : {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
      → (s↓ : Src↓ X↓ P↓ (join X P (s .fst , s .snd .fst , λ p → δ p .fst)) f↓)
      → Web↓ (X↓ ∥↓ P↓) (nd t s δ) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)
      ≃ (Σ[ σ↓ ∈ Src↓ X↓ P↓ s f↓ ]
         Σ[ δ↓ ∈ ((p : Pos (s .fst)) → Branch↓ X↓ P↓ (δ p) (σ↓ .snd p)) ]
         join↓ X↓ P↓ (σ↓ .fst , λ p → δ↓ p .fst) == s↓)
    nd-data-equiv t↓ s↓ = equiv
      (nd-data-to t↓ s↓) (nd-data-from t↓ s↓)
      (nd-data-to-from t↓ s↓) (nd-data-from-to t↓ s↓) 
