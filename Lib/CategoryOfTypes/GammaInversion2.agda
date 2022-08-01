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
open import Lib.CategoryOfTypes.GammaInversion

module Lib.CategoryOfTypes.GammaInversion2 where

  module _ {n ℓ}
    (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) where

    postulate

      γ↓-section : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
        → (Upd : Pd X (F , S , T))
        → (Brs : (p : UPos S) → Branch X (S ⊚ p))
        → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
        → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
        → (λ i → Pd↓ X P (γ X Upd Brs) (f , γ↓-coh X P Upd Brs ρ i , t))
            [ γ↓ X P (γ↓-base X P Upd Brs ρ) (γ↓-dec' X P Upd Brs ρ) ≡ ρ ]

      γ↓-cnpy-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
        → (Upd : Pd X (F , S , T))
        → (Brs : (p : UPos S) → Branch X (S ⊚ p))
        → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
        → (pd : Pd↓ X P Upd (f , s , t))
        → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
        → γ↓-cnpy X P Upd Brs (γ↓ X P pd brs) ≡ s 

      γ↓-base-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
        → (Upd : Pd X (F , S , T))
        → (Brs : (p : UPos S) → Branch X (S ⊚ p))
        → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
        → (pd : Pd↓ X P Upd (f , s , t))
        → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
        → (λ i → Pd↓ X P Upd (f , γ↓-cnpy-β Upd Brs pd brs i , t))
           [ γ↓-base X P Upd Brs (γ↓ X P pd brs) ≡ pd ]

      γ↓-dec-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
        → (Upd : Pd X (F , S , T))
        → (Brs : (p : UPos S) → Branch X (S ⊚ p))
        → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
        → (pd : Pd↓ X P Upd (f , s , t))
        → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
        → (λ i → (p : UPos {F = F} S) → Branch↓ X P (Brs p) ((γ↓-cnpy-β Upd Brs pd brs i) ⊚↓ p))
           [ γ↓-dec' X P Upd Brs (γ↓ X P pd brs) ≡ brs ]

      γ↓-coh-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
        → (Upd : Pd X (F , S , T))
        → (Brs : (p : UPos S) → Branch X (S ⊚ p))
        → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
        → (pd : Pd↓ X P Upd (f , s , t))
        → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
        → (λ i → μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs p))} (ν↓ (γ↓-cnpy-β Upd Brs pd brs i) (λ p → lvs↓ (γ↓-dec-β Upd Brs pd brs i p)))
               ≡ μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs p))} (ν↓ s (λ p → lvs↓ (brs p))))
            [ γ↓-coh X P Upd Brs (γ↓ X P pd brs) ≡ refl ]
