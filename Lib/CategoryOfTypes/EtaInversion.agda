--
--  Universe.agda - The opetopic type of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Core.OpetopicType
open import Core.Universe

open import Lib.CategoryOfTypes.Lemmas

module Lib.CategoryOfTypes.EtaInversion where

  η↓-dec-unique : ∀ {n ℓ}
    → {F : UFrm n ℓ} {S : USrc F} 
    → {frm : Frm↓ F} (src : USrc↓ S frm)
    → (brs : Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S (η-dec CellFib {f = F} S) src)
    → η↓-dec {f = frm} src ≡ brs 
  η↓-dec-unique {F = F} {S} {frm} src brs =
    Dec↓-≡ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S _ src (η↓-dec {f = frm} src) brs
      (λ p → branch-lem CellFib (λ C → C) (S ⊚ p) (src ⊚↓ p) (brs ⊛↓ p)) 

  η↓-dec-contr : ∀ {n ℓ}
    → {F : UFrm n ℓ} {S : USrc F} 
    → {frm : Frm↓ F} (src : USrc↓ S frm)
    → isContr (Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S (η-dec CellFib {f = F} S) src)
  η↓-dec-contr {frm = frm} src = η↓-dec {f = frm} src , λ brs → η↓-dec-unique {frm = frm} src brs

  η↓-dec-unique-β : ∀ {n ℓ}
    → {F : UFrm n ℓ} {S : USrc F} 
    → {frm : Frm↓ F} (src : USrc↓ S frm)
    → η↓-dec-unique {frm = frm} src (η↓-dec {f = frm} src) ≡ refl
  η↓-dec-unique-β {frm = frm} src =
    isContr→isOfHLevel 2 (η↓-dec-contr {frm = frm} src)
      (η↓-dec {f = frm} src) (η↓-dec {f = frm} src)
      (η↓-dec-unique {frm = frm} src (η↓-dec {f = frm} src)) refl 

  η↓-typ-eq : ∀ {n ℓ}
    → {F : Frm (𝕆U n ℓ)} (C : CellFib F)
    → {f : Frm↓ F} (s : USrc↓ (ηU C) f)
    → Typ↓ (λ C → C) s (ηU-pos C) ≡ f
  η↓-typ-eq {zero} C s = refl
  η↓-typ-eq {suc n} {F = F , S , T} C (nd↓ {frm} src tgt flr brs) i =
    frm , cong (canopy↓ CellFib (λ C → C) {f = frm} {s = src}) (η↓-dec-unique {F = F} {S} src brs) i , tgt

  η↓-typ-eq-β : ∀ {n ℓ}
    → {F : Frm (𝕆U n ℓ)} (C : CellFib F)
    → {f : Frm↓ F} (c : C f)
    → η↓-typ-eq C (ηU↓ C c) ≡ refl
  η↓-typ-eq-β {zero} C c = refl
  η↓-typ-eq-β {suc n} {F = F , S , T} C {f , s , t} c j i  =
    f , cong (canopy↓ CellFib (λ C → C) {f = f} {s = s}) (η↓-dec-unique-β {frm = f} s j) i , t

  η↓-inv-lem : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (C : CellFib F)
    → {f : Frm↓ F} (s : USrc↓ (ηU C) f) 
    → (λ i → USrc↓ (ηU C) (η↓-typ-eq C s i))
      [ ηU↓ C (s ⊚↓ ηU-pos C) ≡ s ]
  η↓-inv-lem {zero} C s i = s
  η↓-inv-lem {suc n} {F = F , S , T} C (nd↓ {frm} src tgt flr brs) i =
    nd↓ src tgt flr (η↓-dec-unique {F = F} {S} src brs i)

  ηU↓-inv : ∀ {n ℓ} 
    → {F : UFrm n ℓ} (C : CellFib F)
    → {f : Frm↓ F}
    → USrc↓ (ηU C) f → C f
  ηU↓-inv C s = transport (λ i → C (η↓-typ-eq C s i)) (s ⊚↓ ηU-pos C)

  ηU↓-section : ∀ {n ℓ} 
    → {F : UFrm n ℓ} (C : CellFib F)
    → {f : Frm↓ F}
    → section (ηU↓ C {f = f}) (ηU↓-inv C)
  ηU↓-section C {f} s =  ηU↓ C (transport (λ i → C (η↓-typ-eq C s i)) (s ⊚↓ ηU-pos C))
                           ≡⟨ transport-natural (λ f → ηU↓ C {f}) (s ⊚↓ ηU-pos C) (η↓-typ-eq C s) ⟩
                         transport (λ i → USrc↓ (ηU C) (η↓-typ-eq C s i)) (ηU↓ C (s ⊚↓ ηU-pos C))
                           ≡⟨ fst (PathP≃Path (λ i → USrc↓ (ηU C) (η↓-typ-eq C s i)) (ηU↓ C (s ⊚↓ ηU-pos C)) s)
                              (η↓-inv-lem C s) ⟩ 
                         s ∎ 

  ηU↓-retract : ∀ {n ℓ} 
    → {F : UFrm n ℓ} (C : CellFib F)
    → {f : Frm↓ F}
    → retract (ηU↓ C {f = f}) (ηU↓-inv C)
  ηU↓-retract {n} C {f} c =
    transport (λ i → C (η↓-typ-eq C (ηU↓ C c) i)) c   ≡[ j ]⟨ transport (λ i → C (η↓-typ-eq-β C c j i)) c ⟩ 
    transport (λ i → C f) c                           ≡⟨ transportRefl {A = C f} c ⟩ 
    c ∎

  η↓-equiv : ∀ {n ℓ} 
    → {F : UFrm n ℓ} (C : CellFib F)
    → (f : Frm↓ F)
    → C f ≃ USrc↓ (ηU C) f 
  η↓-equiv C f = isoToEquiv
    (iso (ηU↓ C) (ηU↓-inv C)
      (ηU↓-section C) (ηU↓-retract C))


