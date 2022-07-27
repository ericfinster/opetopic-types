--
--  GammaInversionDone.agda - Inverting γ↓ (repo for finished material)
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.Universe

open import Experimental.Local.CategoryOfTypes.Lemmas

module Experimental.Local.CategoryOfTypes.GammaInversionDone where

  module Done {n ℓ}
    (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) where

    {-# TERMINATING #-}
    γ↓-cnpy : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
      → Pd↓ X P (γ X Upd Brs) (f , s , t)
      → USrc↓ S f
    γ↓-cnpy (lf T) Brs {t = t} ρ = ηU↓ T t
    γ↓-cnpy (nd {F} S T C LBrs) Brs (nd↓ src tgt flr brs) =
      μ↓ {X = CellFib} (λ C → C) {F = F} {S = ν {X = 𝕆U n ℓ} S (λ p → lvs (LBrs ⊛ p))}
        (ν↓ {Y = Src CellFib} {Q = Src↓ (λ C → C)} {F = F} {S = S} {ϕ = λ p → lvs (LBrs ⊛ p)} src
          λ p → γ↓-cnpy (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)))
