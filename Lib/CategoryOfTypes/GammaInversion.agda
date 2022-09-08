{-# OPTIONS --no-termination-check #-}
--
--  GammaInversion.agda - Inverting γ
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Core.OpetopicType
open import Core.Universe

open import Lib.CategoryOfTypes.Lemmas

module Lib.CategoryOfTypes.GammaInversion where

  module _ {n ℓ}
    (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) where

    γ↓-cnpy : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
      → Pd↓ X P (γ X Upd Brs) (f , s , t)
      → USrc↓ S f
    γ↓-cnpy (lf T) Brs {t = t} ρ = ηU↓ T t
    γ↓-cnpy (nd {F} S T C LBrs) Brs (nd↓ src tgt flr brs) =
      bind↓ (λ C → C) (λ C → C) S (λ p → lvs (LBrs ⊛ p))
        src (λ p → γ↓-cnpy (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p))) 

    γ↓-base : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
       → (Upd : Pd X (F , S , T))
       → (Brs : (p : UPos S) → Branch X (S ⊚ p))
       → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
       → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
       → Pd↓ X P Upd (f , γ↓-cnpy Upd Brs ρ  , t)
    γ↓-base (lf T) Brs {t = t} ρ = lf↓ t
    γ↓-base (nd {F} S T C LBrs) Brs (nd↓ {frm} src tgt flr brs) =
      nd↓ src tgt flr
        (λ-dec↓ {Y = Branch X} (Branch↓ X P) {F = F} {S = S} LBrs {s = src} λ p →
              [ γ↓-cnpy (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p))
              , γ↓-base (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p))
              ]↓)

    γ↓-dec' : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
       → (Upd : Pd X (F , S , T))
       → (Brs : (p : UPos S) → Branch X (S ⊚ p))
       → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
       → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
       → (p : UPos {F = F} S) → Branch↓ X P (Brs p) (γ↓-cnpy Upd Brs ρ ⊚↓ p)
    γ↓-dec' (lf T) Brs {s = s} {t = t} ρ =
      η-pos-elim T (λ p → Branch↓ X P (Brs p) t) [ s , ρ ]↓
    γ↓-dec' (nd {F} S T C LBrs) Brs (nd↓ {frm} src tgt flr brs) pq =
      let p = canopy-fst X LBrs pq
          q = canopy-snd X LBrs pq
      in γ↓-dec' (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)) q

    γ↓-dec : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
       → (Upd : Pd X (F , S , T))
       → (Brs : (p : UPos S) → Branch X (S ⊚ p))
       → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
       → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
       → Dec↓ (Branch X) (Branch↓ X P) S (λ-dec (Branch X) S Brs) (γ↓-cnpy Upd Brs ρ)
    γ↓-dec {S = S} Upd Brs ρ = λ-dec↓ {Y = Branch X} (Branch↓ X P) (λ-dec (Branch X) S Brs) (γ↓-dec' Upd Brs ρ) 

    γ↓-coh : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
       → (Upd : Pd X (F , S , T))
       → (Brs : (p : UPos S) → Branch X (S ⊚ p))
       → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
       → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
       → bind↓ (λ C → C) (λ C → C) S (λ p → lvs (Brs p))
           (γ↓-cnpy Upd Brs ρ) (λ p → lvs↓ (γ↓-dec Upd Brs ρ ⊛↓ p)) ≡ s
    γ↓-coh (lf T) Brs {s = s} {t = t} ρ = refl
    γ↓-coh (nd {F} S T C LBrs) Brs (nd↓ {frm} src tgt flr brs) i =  
      bind↓ (λ C → C) (λ C → C)
        S (λ p → bind (λ F₁ → Frm↓ F₁ → Type ℓ) (λ F₁ → Frm↓ F₁ → Type ℓ) (Typ (λ F₁ → Frm↓ F₁ → Type ℓ) S p)
                   (lvs (LBrs ⊛ p)) (λ q → lvs (Brs (canopy-pos X LBrs p q))))
        src (λ p → γ↓-coh (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)) i)
    
