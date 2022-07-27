--
--  GammaInversion.agda - Inverting γ
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.Universe

open import Experimental.Local.CategoryOfTypes.Lemmas
open import Experimental.Local.CategoryOfTypes.GammaInversionDone


module Experimental.Local.CategoryOfTypes.GammaInversion where

  module _ {n ℓ}
    (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) where

    open Done X P

    γ↓-cnpy-coh : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
      → (pd : Pd↓ X P (γ X Upd Brs) (f , s , t))
      → μ↓ {X = CellFib} (λ C → C) {F = F} {S = ν S (λ p → lvs (Brs p))}
          (ν↓ {X = CellFib} {P = λ C → C} {F = F} {S = S} (γ↓-cnpy Upd Brs pd)
            (λ p → {!!})) ≡ s
    γ↓-cnpy-coh = {!!} 


    -- γ↓-base : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
    --   → (Upd : Pd X (F , S , T))
    --   → (Brs : (p : UPos S) → Branch X (S ⊚ p))
    --   → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
    --   → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
    --   → Pd↓ X P Upd (f , γ↓-cnpy Upd Brs ρ  , t)
    -- γ↓-base (lf T) Brs {t = t} ρ = lf↓ t
    -- γ↓-base (nd {F} S T C LBrs) Brs (nd↓ src tgt flr brs) = {!!}

    -- Goal: Pd↓Nd X P S T C LBrs
    --       (f ,
    --        μ↓ (λ C₁ → C₁)
    --        (ν↓ src
    --         (λ p →
    --            γ↓-cnpy (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
    --            (br↓ (brs ⊛↓ p))))
    --        , tgt)

    -- nd↓ : {frm : Frm↓ F} (src : Src↓ {X = CellFib} (λ C → C) S frm) (tgt : T frm)
    --   → (flr : P C (frm , src , tgt))
    --   → (brs : Dec↓ (Branch X) Branch↓ S Brs src)
    --   → Pd↓Nd S T C Brs (frm , μ↓ (λ C → C) (ν↓ src (λ p → lvs↓ (brs ⊛↓ p))) , tgt)
