open import Core.Prelude 
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

open import MiniHoTT

module Native.Inversion.EtaInversion where


  Frm↓-= : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
      → {P : Idx X → Type ℓ}
      → {P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓}
      → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)} {s : Src X P (ο , f)}
      → {f↓₀ : Frm↓ X↓ f} {t↓₀ : P↓ t f↓₀} {s↓₀ : Src↓ X↓ P↓ s f↓₀}
      → {f↓₁ : Frm↓ X↓ f} {t↓₁ : P↓ t f↓₁} {s↓₁ : Src↓ X↓ P↓ s f↓₁}
      → (p : f↓₀ == f↓₁) → t↓₀ == t↓₁ [ P↓ t ↓ p ]
      → s↓₀ == s↓₁ [ Src↓ X↓ P↓ s ↓ p ]
      → Path {A = Frm↓ (X↓ ∥↓ P↓) (f ►⟦ t ∣ s ⟧)} (f↓₀ ►⟦ t↓₀ ∣ s↓₀ ⟧↓) (f↓₁ ►⟦ t↓₁ ∣ s↓₁ ⟧↓)
  Frm↓-= idp idp idp = idp

  branch-over-leaf-unique : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)}
    → {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
    → (b : Branch↓ X↓ P↓ ((ηₒ ο , η X f , cst t) , lfₒ ο , lf t) t↓)
    → b == (ret↓ X↓ P↓ t↓ , lf↓ t↓)
  branch-over-leaf-unique X↓ P↓ t↓ (._ , lf↓ .t↓) = idp

  η↓-dec-unique : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {ο : 𝕆 n} {f : Frm X ο} {s : Src X P (ο , f)}
    → {f↓ : Frm↓ X↓ f} (s↓ : Src↓ X↓ P↓ s f↓)
    → (δ : (p : Pos (fst s)) → Branch↓ X↓ P↓ (ret X P (s .snd .snd p) , lfₒ (Typ (fst s) p) , lf (s .snd .snd p)) (snd s↓ p))
    → δ == (λ p → ret↓ X↓ P↓ (s↓ .snd p) , lf↓ (s↓ .snd p))
  η↓-dec-unique X↓ P↓ s↓ δ = λ= (λ p → branch-over-leaf-unique X↓ P↓ (snd s↓ p) (δ p))

  η↓-typ-eq : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {ο : 𝕆 n} {f : Frm X ο} (x : P (ο , f))
    → (f↓ : Frm↓ X↓ f)
    → (s : Src↓ X↓ P↓ (ret X P x) f↓)
    → Shp↓ X↓ (fst s) (η-posₒ ο) == f↓
  η↓-typ-eq ○↓ Q↓ t ●↓ (arr↓ , δ) = idp
  η↓-typ-eq (X↓ ∥↓ P↓) Q↓ {f = f ►⟦ t ∣ s ⟧} x (f↓ ►⟦ t↓ ∣ ._ , ._ ⟧↓) (nd↓ .t↓ s↓ δ↓ , δ) = 
   Frm↓-= idp idp claim

   where claim : s↓ == join↓ X↓ P↓ (s↓ .fst , λ p → δ↓ p .fst)
         claim = ! (ap (λ d → join↓ X↓ P↓ (s↓ .fst , (λ p → d p .fst))) (η↓-dec-unique X↓ P↓ s↓ δ↓))

      
    -- η↓-inv : {ο : 𝕆 n} {f : Frm X ο} (x : P (ο , f))
    --   → (f↓ : Frm↓ X↓ f)
    --   → (s : Src↓ X↓ P↓ (ret X P x) f↓)
    --   → P↓ x f↓ 
    -- η↓-inv x f↓ s = {!snd s (η-posₒ _)!} 


  -- η↓-dec-contr : ∀ {n ℓ}
  --   → {F : UFrm n ℓ} {S : USrc F} 
  --   → {frm : Frm↓ F} (src : USrc↓ S frm)
  --   → isContr (Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S (η-dec CellFib {f = F} S) src)
  -- η↓-dec-contr {frm = frm} src = η↓-dec {f = frm} src , λ brs → η↓-dec-unique {frm = frm} src brs

  -- η↓-dec-unique-β : ∀ {n ℓ}
  --   → {F : UFrm n ℓ} {S : USrc F} 
  --   → {frm : Frm↓ F} (src : USrc↓ S frm)
  --   → η↓-dec-unique {frm = frm} src (η↓-dec {f = frm} src) ≡ refl
  -- η↓-dec-unique-β {frm = frm} src =
  --   isContr→isOfHLevel 2 (η↓-dec-contr {frm = frm} src)
  --     (η↓-dec {f = frm} src) (η↓-dec {f = frm} src)
  --     (η↓-dec-unique {frm = frm} src (η↓-dec {f = frm} src)) refl 


  -- η↓-typ-eq-β : ∀ {n ℓ}
  --   → {F : Frm (𝕆U n ℓ)} (C : CellFib F)
  --   → {f : Frm↓ F} (c : C f)
  --   → η↓-typ-eq C (ηU↓ C c) ≡ refl
  -- η↓-typ-eq-β {zero} C c = refl
  -- η↓-typ-eq-β {suc n} {F = F , S , T} C {f , s , t} c j i  =
  --   f , cong (canopy↓ CellFib (λ C → C) {f = f} {s = s}) (η↓-dec-unique-β {frm = f} s j) i , t


  
  -- η↓-inv-lem : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (C : CellFib F)
  --   → {f : Frm↓ F} (s : USrc↓ (ηU C) f) 
  --   → (λ i → USrc↓ (ηU C) (η↓-typ-eq C s i))
  --     [ ηU↓ C (s ⊚↓ ηU-pos C) ≡ s ]
  -- η↓-inv-lem {zero} C s i = s
  -- η↓-inv-lem {suc n} {F = F , S , T} C (nd↓ {frm} src tgt flr brs) i =
  --   nd↓ src tgt flr (η↓-dec-unique {F = F} {S} src brs i)

  -- ηU↓-inv : ∀ {n ℓ} 
  --   → {F : UFrm n ℓ} (C : CellFib F)
  --   → {f : Frm↓ F}
  --   → USrc↓ (ηU C) f → C f
  -- ηU↓-inv C s = transport (λ i → C (η↓-typ-eq C s i)) (s ⊚↓ ηU-pos C)

  -- ηU↓-section : ∀ {n ℓ} 
  --   → {F : UFrm n ℓ} (C : CellFib F)
  --   → {f : Frm↓ F}
  --   → section (ηU↓ C {f = f}) (ηU↓-inv C)
  -- ηU↓-section C {f} s =  ηU↓ C (transport (λ i → C (η↓-typ-eq C s i)) (s ⊚↓ ηU-pos C))
  --                          ≡⟨ transport-natural (λ f → ηU↓ C {f}) (s ⊚↓ ηU-pos C) (η↓-typ-eq C s) ⟩
  --                        transport (λ i → USrc↓ (ηU C) (η↓-typ-eq C s i)) (ηU↓ C (s ⊚↓ ηU-pos C))
  --                          ≡⟨ fst (PathP≃Path (λ i → USrc↓ (ηU C) (η↓-typ-eq C s i)) (ηU↓ C (s ⊚↓ ηU-pos C)) s)
  --                             (η↓-inv-lem C s) ⟩ 
  --                        s ∎ 

  -- ηU↓-retract : ∀ {n ℓ} 
  --   → {F : UFrm n ℓ} (C : CellFib F)
  --   → {f : Frm↓ F}
  --   → retract (ηU↓ C {f = f}) (ηU↓-inv C)
  -- ηU↓-retract {n} C {f} c =
  --   transport (λ i → C (η↓-typ-eq C (ηU↓ C c) i)) c   ≡[ j ]⟨ transport (λ i → C (η↓-typ-eq-β C c j i)) c ⟩ 
  --   transport (λ i → C f) c                           ≡⟨ transportRefl {A = C f} c ⟩ 
  --   c ∎

  -- η↓-equiv : ∀ {n ℓ} 
  --   → {F : UFrm n ℓ} (C : CellFib F)
  --   → (f : Frm↓ F)
  --   → C f ≃ USrc↓ (ηU C) f 
  -- η↓-equiv C f = isoToEquiv
  --   (iso (ηU↓ C) (ηU↓-inv C)
  --     (ηU↓-section C) (ηU↓-retract C))


