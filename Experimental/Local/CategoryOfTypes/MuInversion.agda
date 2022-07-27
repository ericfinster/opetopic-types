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

module Experimental.Local.CategoryOfTypes.MuInversion where

  module _ {n ℓ}
    (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) where

    postulate
    
      γ↓-cnpy : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
        → (Upd : Pd X (F , S , T))
        → (Brs : (p : UPos S) → Branch X (S ⊚ p))
        → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
        → Pd↓ X P (γ X Upd Brs) (f , s , t)
        → USrc↓ S f

      γ↓-base : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
         → (Upd : Pd X (F , S , T))
         → (Brs : (p : UPos S) → Branch X (S ⊚ p))
         → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
         → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
         → Pd↓ X P Upd (f , γ↓-cnpy Upd Brs ρ  , t)

      γ↓-dec : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
         → (Upd : Pd X (F , S , T))
         → (Brs : (p : UPos S) → Branch X (S ⊚ p))
         → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
         → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
         → Dec↓ (Branch X) (Branch↓ X P) S (λ-dec (Branch X) S Brs) (γ↓-cnpy Upd Brs ρ)

      γ↓-coh : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
         → (Upd : Pd X (F , S , T))
         → (Brs : (p : UPos S) → Branch X (S ⊚ p))
         → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
         → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
         → μ↓ {X = CellFib} (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs p))}
              (ν↓ {F = F} {S = S} {ϕ = λ p → lvs (Brs p)} {f = f} (γ↓-cnpy Upd Brs ρ) (λ p → lvs↓ (γ↓-dec Upd Brs ρ ⊛↓ p))) ≡ s

  {-# TERMINATING #-}
  μ↓-inv : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {S : Src (Src X) F} {f : Frm↓ F}
    → Src↓ P (μ X S) f → Src↓ (Src↓ P) S f
  μ↓-inv {zero} P s = s
  μ↓-inv {suc n} P {S = lf T} (lf↓ t) = lf↓ t
  μ↓-inv {suc n} {X = X} P {S = nd {F} S T C Brs} {f = f , s , t} ρ =
    transport (λ i → Pd↓Nd (Pd X) (Pd↓ X P) S T C Brs (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t)) result

    where src : Src↓ {X = CellFib} (λ C → C) {F = F} S f
          src = γ↓-cnpy X P C (μ-brs X Brs) ρ 

          tgt : T f
          tgt = t

          flr : Pd↓ X P C (f , src , tgt)
          flr = γ↓-base X P C (μ-brs X Brs) ρ 

          brs : Dec↓ (Branch (Pd X)) (Branch↓ (Pd X) (Pd↓ X P)) S Brs src
          brs = λ-dec↓  {Y = Branch (Pd X)} (Branch↓ (Pd X) (Pd↓ X P)) {F = F} {S = S} Brs {s = src}
            λ p → [ lvs↓ (γ↓-dec X P C (μ-brs X Brs) ρ ⊛↓ p)
                  , μ↓-inv {suc n} {X = X} P {S = br (Brs ⊛ p)} (br↓ (γ↓-dec X P C (μ-brs X Brs) ρ ⊛↓ p))
                  ]↓

          result : Pd↓Nd (Pd X) (Pd↓ X P) S T C Brs (f ,
            μ↓ {X = CellFib} (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))}
              (ν↓ {F = F} {S = S} {ϕ = λ p → lvs (Brs ⊛ p)} {f = f} src (λ p → lvs↓ (brs ⊛↓ p))) , t)
          result = nd↓ src tgt flr brs  

