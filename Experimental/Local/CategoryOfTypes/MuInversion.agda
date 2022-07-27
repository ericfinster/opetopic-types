{-# OPTIONS --no-termination-check #-}
--
--  MuInversion.agda - Inverting μ↓
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.Universe

open import Experimental.Local.CategoryOfTypes.Lemmas
open import Experimental.Local.CategoryOfTypes.GammaInversion

module Experimental.Local.CategoryOfTypes.MuInversion where

  μ↓-inv : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {S : Src (Src X) F} {f : Frm↓ F}
    → Src↓ P (μ X S) f → Src↓ (Src↓ P) S f
  μ↓-inv {zero} P s = s
  μ↓-inv {suc n} P {S = lf T} (lf↓ t) = lf↓ t
  μ↓-inv {suc n} {X = X} P {S = nd {F} S T C Brs} {f = f , s , t} ρ =
    transport (λ i → Pd↓Nd (Pd X) (Pd↓ X P) S T C Brs (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t))
      (nd↓ (γ↓-cnpy X P C (μ-brs X Brs) ρ) t (γ↓-base X P C (μ-brs X Brs) ρ)
           (λ-dec↓  {Y = Branch (Pd X)} (Branch↓ (Pd X) (Pd↓ X P)) {F = F} {S = S} Brs {s = γ↓-cnpy X P C (μ-brs X Brs) ρ}
             λ p → [ lvs↓ (γ↓-dec X P C (μ-brs X Brs) ρ ⊛↓ p)
                   , μ↓-inv {suc n} {X = X} P {S = br (Brs ⊛ p)} (br↓ (γ↓-dec X P C (μ-brs X Brs) ρ ⊛↓ p))
                   ]↓))


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

  μ↓-retract : ∀ {n ℓ}
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src (Src X) F) (f : Frm↓ F)
    → retract (μ↓ P {f = f} {S = S}) (μ↓-inv P)
  μ↓-retract {zero} P S f s = refl
  μ↓-retract {suc n} P (lf T) ._ (lf↓ x) = refl
  μ↓-retract {suc n} {X = X} P (nd S T C Brs) ._ (nd↓ {frm} src tgt flr brs) = 
    let μ-ufld = γ↓ X P flr (λ p → [ lvs↓ (brs ⊛↓ p) , μ↓ P (br↓ (brs ⊛↓ p)) ]↓)  in 

    transport (λ i → Pd↓Nd (Pd X) (Pd↓ X P) S T C Brs (frm , γ↓-coh X P C (μ-brs X Brs) μ-ufld i , tgt))
     (nd↓ (γ↓-cnpy X P C (μ-brs X Brs) μ-ufld) tgt (γ↓-base X P C (μ-brs X Brs) μ-ufld)
          (λ-dec↓ (Branch↓ (Pd X) (Pd↓ X P)) Brs
              (λ p → [ lvs↓ (γ↓-dec' X P C (μ-brs X Brs) μ-ufld p)
                     , μ↓-inv P (br↓ (γ↓-dec' X P C (μ-brs X Brs) μ-ufld p))
                     ]↓)))

      ≡⟨ {!!} ⟩ 

    nd↓ src tgt flr brs ∎

  --
  --  The Equivalence
  --

  -- μ↓-section : ∀ {n ℓ}
  --   → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
  --   → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
  --   → {F : Frm (𝕆U n ℓ)} (S : Src (Src X) F) (f : Frm↓ F)
  --   → section (μ↓ P {f = f} {S = S}) (μ↓-inv P)
  -- μ↓-section {zero} P S f s = refl
  -- μ↓-section {suc n} P (lf T) ._ (lf↓ x) = refl
  -- μ↓-section {suc n} {ℓ} {X} P (nd {F} S T C Brs) (f , s , t) ρ = 

  --   μ↓ P (transport (λ i → Pd↓Nd (Pd X) (Pd↓ X P) S T C Brs (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t))
  --      (nd↓ (γ↓-cnpy X P C (μ-brs X Brs) ρ) t
  --           (γ↓-base X P C (μ-brs X Brs) ρ)
  --           (λ-dec↓ (Branch↓ (Pd X) (Pd↓ X P)) Brs
  --            (λ p → [ lvs↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p)
  --                   , μ↓-inv P (br↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p)) ]↓))))

  --     ≡⟨ transport-natural
  --           {A = Src↓ (λ C → C) (μ {X = 𝕆U n ℓ} CellFib (ν {f = F} S (λ p → lvs (Brs ⊛ p)))) f}
  --           {B = λ s → Pd↓Nd (Pd X) (Pd↓ X P) S T C Brs (f , s , t)}
  --           {C = λ s → Pd↓ X P (γ X C (μ-brs X Brs)) (f , s , t)}
  --           (λ s' → μ↓ {n = suc n} {X = X} P {f = f , s' , t} {S = nd S T C Brs})
  --           (nd↓ (γ↓-cnpy X P C (μ-brs X Brs) ρ) t
  --                (γ↓-base X P C (μ-brs X Brs) ρ)
  --                (λ-dec↓ (Branch↓ (Pd X) (Pd↓ X P)) Brs
  --                 (λ p → [ lvs↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p)
  --                        , μ↓-inv P (br↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p)) ]↓)))
  --                (γ↓-coh X P C (μ-brs X Brs) ρ)
  --      ⟩ 

  --   transport (λ i → Pd↓ X P (γ X C (μ-brs X Brs)) (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t))
  --     (γ↓ X P (γ↓-base X P C (μ-brs X Brs) ρ) (λ p →
  --       [ lvs↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p)
  --       , μ↓ P (μ↓-inv P {S = br (Brs ⊛ p)} (br↓  (γ↓-dec' X P C (μ-brs X Brs) ρ p))) ]↓))

  --     ≡[ i ]⟨ transport (λ i → Pd↓ X P (γ X C (μ-brs X Brs)) (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t))
  --             (γ↓ X P (γ↓-base X P C (μ-brs X Brs) ρ) (λ p →
  --               [ lvs↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p) , μ↓-section P (br (Brs ⊛ p)) _ (br↓ (γ↓-dec' X P C (μ-brs X Brs) ρ p)) i ]↓)) ⟩ 

  --   transport (λ i → Pd↓ X P (γ X C (μ-brs X Brs)) (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t))
  --     (γ↓ X P (γ↓-base X P C (μ-brs X Brs) ρ) (γ↓-dec' X P C (μ-brs X Brs) ρ))

  --     ≡⟨ fst (PathP≃Path (λ i → Pd↓ X P (γ X C (μ-brs X Brs)) (f , γ↓-coh X P C (μ-brs X Brs) ρ i , t))
  --           (γ↓ X P (γ↓-base X P C (μ-brs X Brs) ρ) (γ↓-dec' X P C (μ-brs X Brs) ρ)) ρ) (γ↓-section X P C (μ-brs X Brs) ρ) ⟩ 

  --   ρ ∎
    

  -- Nope.  It's a more tricky path-over construction.
  
  -- μ↓-equiv : ∀ {n ℓ}
  --   → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
  --   → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
  --   → {F : Frm (𝕆U n ℓ)} (S : Src (Src X) F) (f : Frm↓ F)
  --   → Src↓ (Src↓ P) S f ≃ Src↓ P (μ X S) f 
  -- μ↓-equiv P S f = isoToEquiv
  --   (iso (μ↓ P) (μ↓-inv P)
  --     (μ↓-section P S f) (μ↓-retract P S f)) 
