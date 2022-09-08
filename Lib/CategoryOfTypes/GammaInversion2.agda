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

    γ↓-section : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ (canopyU' S Brs) f} {t : T f}
      → (ρ : Pd↓ X P (γ X Upd Brs) (f , s , t))
      → (λ i → Pd↓ X P (γ X Upd Brs) (f , γ↓-coh X P Upd Brs ρ i , t))
          [ γ↓ X P (γ↓-base X P Upd Brs ρ) (γ↓-dec' X P Upd Brs ρ) ≡ ρ ]
    γ↓-section (lf T) Brs {t = t} ρ = refl 
    γ↓-section (nd {F} S T C LBrs) Brs (nd↓ {f} src tgt flr brs) = 
      transport⁻ (λ j → (λ i → Pd↓Nd X P S T C (λ-dec (Branch X) S (γ-brs X LBrs Brs))
                    (f , bind↓ (λ C₁ → C₁) (λ C₁ → C₁) S
                               (λ p → bind (λ F₁ → Frm↓ F₁ → Type ℓ) (λ F₁ → Frm↓ F₁ → Type ℓ)
                                           (Typ (λ F₁ → Frm↓ F₁ → Type ℓ) S p) (lvs (LBrs ⊛ p))
                                           (λ q → lvs (Brs (canopy-pos X LBrs p q))))
                               src (λ p → lvs↓ (Dec↓-≡-β (Branch X) (Branch↓ X P) S (λ-dec (Branch X) S (γ-brs X LBrs Brs)) src brs'' brs
                                    (λ p i → [ γ↓-coh X P (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)) i
                                             , γ↓-section (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)) i ]↓) p j i)) , tgt))
                      [ nd↓ src tgt flr brs'' ≡ nd↓ src tgt flr brs ])
                 (λ i → nd↓ src tgt flr (brs''≡brs i))


      where brs' : Dec↓ (Branch X) (Branch↓ X P) S LBrs src
            brs' = λ-dec↓ {Y = Branch X} (Branch↓ X P) {F = F} {S = S} LBrs {s = src} λ p →
              [ γ↓-cnpy X P (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p))
              , γ↓-base X P (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p))
              ]↓

            brs'' : Dec↓ (Branch X) (Branch↓ X P) S (λ-dec (Branch X) S (γ-brs X LBrs Brs)) src
            brs'' = λ-dec↓ (Branch↓ X P) (λ-dec (Branch X) S (γ-brs X LBrs Brs))
                      (γ↓-brs X P LBrs Brs brs' (λ pq → γ↓-dec' X P (br (LBrs ⊛ canopy-fst X LBrs pq))
                                                        (λ q → Brs (canopy-pos X LBrs (canopy-fst X LBrs pq) q))
                                                        (br↓ (brs ⊛↓ canopy-fst X LBrs pq)) (canopy-snd X LBrs pq)))

            brs''≡brs : brs'' ≡ brs
            brs''≡brs = Dec↓-≡ (Branch X) (Branch↓ X P) S (λ-dec (Branch X) S (γ-brs X LBrs Brs)) src brs'' brs
                          λ p i → [ γ↓-coh X P (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)) i
                                  , γ↓-section (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q)) (br↓ (brs ⊛↓ p)) i ]↓ 

    γ↓-cnpy-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
      → (pd : Pd↓ X P Upd (f , s , t))
      → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
      → γ↓-cnpy X P Upd Brs (γ↓ X P pd brs) ≡ s 
    γ↓-cnpy-β (lf T) Brs (lf↓ t) brs = refl
    γ↓-cnpy-β (nd {F} S T C LBrs) Brs (nd↓ {f} src tgt flr lbrs) brs i = 
      bind↓ (λ C → C) (λ C → C) S (λ p → lvs (LBrs ⊛ p)) src
        (λ p → γ↓-cnpy-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                         (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i)

    γ↓-base-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
      → (pd : Pd↓ X P Upd (f , s , t))
      → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
      → (λ i → Pd↓ X P Upd (f , γ↓-cnpy-β Upd Brs pd brs i , t))
         [ γ↓-base X P Upd Brs (γ↓ X P pd brs) ≡ pd ]
    γ↓-base-β (lf T) Brs (lf↓ t) brs = refl
    γ↓-base-β (nd {F} S T C LBrs) Brs (nd↓ {f} src tgt flr lbrs) brs = 
      transport⁻ (λ j → (λ i → Pd↓Nd X P S T C LBrs
                                 (f , bind↓ (λ C₁ → C₁) (λ C₁ → C₁) S (λ p → lvs (LBrs ⊛ p)) src
                                 (λ p →  lvs↓ (Dec↓-≡-β (Branch X) (Branch↓ X P) S LBrs src lbrs' lbrs
                                                 (λ p i → [ γ↓-cnpy-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                                                              (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i
                                                          , γ↓-base-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                                                              (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i ]↓) p j i)) , tgt))
                          [ nd↓ src tgt flr lbrs'
                          ≡ nd↓ src tgt flr lbrs ])
                 (λ i → nd↓ src tgt flr (ih i))                        

      where lbrs' : Dec↓ (Branch X) (Branch↓ X P) S LBrs src
            lbrs' = λ-dec↓ (Branch↓ X P) LBrs (λ p →
                        [ γ↓-cnpy X P (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                            (γ↓ X P (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)))
                        , γ↓-base X P (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                            (γ↓ X P (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q))) ]↓)
                            
            ih : lbrs' ≡ lbrs
            ih = Dec↓-≡ (Branch X) (Branch↓ X P) S LBrs src lbrs' lbrs
                   (λ p i → [ γ↓-cnpy-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                                (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i
                            , γ↓-base-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                                (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i ]↓) 

    γ↓-dec-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
      → (pd : Pd↓ X P Upd (f , s , t))
      → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
      → (λ i → (p : UPos {F = F} S) → Branch↓ X P (Brs p) ((γ↓-cnpy-β Upd Brs pd brs i) ⊚↓ p))
         [ γ↓-dec' X P Upd Brs (γ↓ X P pd brs) ≡ brs ]
    γ↓-dec-β (lf T) Brs (lf↓ t) brs i p = 
      η-pos-elim T (λ p →
          η-pos-elim T (λ p' → Branch↓ X P (Brs p') t)
            [ lvs↓ (brs (η-pos CellFib T))
            , br↓ (brs (η-pos CellFib T)) ]↓ p
            ≡ brs p) refl p i 

    γ↓-dec-β (nd {F} S T C LBrs) Brs (nd↓ {f} src tgt flr lbrs) brs i pq = 
      let p = canopy-fst X LBrs pq
          q = canopy-snd X LBrs pq
      in γ↓-dec-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                  (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i q 

    γ↓-coh-β : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → (Upd : Pd X (F , S , T))
      → (Brs : (p : UPos S) → Branch X (S ⊚ p))
      → {f : Frm↓ F} {s : USrc↓ S f} {t : T f}
      → (pd : Pd↓ X P Upd (f , s , t))
      → (brs : (p : UPos {F = F} S) → Branch↓ X P (Brs p) (s ⊚↓ p))
      → (λ i → bind↓ (λ C → C) (λ C → C) S (λ p → lvs (Brs p))
                     (γ↓-cnpy-β Upd Brs pd brs i)
                     (λ p → lvs↓ (γ↓-dec-β Upd Brs pd brs i p))
             ≡ bind↓ (λ C → C) (λ C → C) S (λ p → lvs (Brs p)) s (λ p → lvs↓ (brs p)))
          [ γ↓-coh X P Upd Brs (γ↓ X P pd brs) ≡ refl ]
    γ↓-coh-β (lf T) Brs (lf↓ t) brs = refl
    γ↓-coh-β (nd {F} S T C LBrs) Brs (nd↓ {f} src tgt flr lbrs) brs i j = 
      bind↓ (λ C → C) (λ C → C)
        S (λ p → bind CellFib CellFib (Typ CellFib S p)
                   (lvs (LBrs ⊛ p)) (λ q → lvs (Brs (canopy-pos X LBrs p q))))
        src (λ p → γ↓-coh-β (br (LBrs ⊛ p)) (λ q → Brs (canopy-pos X LBrs p q))
                            (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) i j)


    -- Old types: these should be the same, but keep them around until you check....
    -- μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs p))} (ν↓ (γ↓-cnpy-β Upd Brs pd brs i) (λ p → lvs↓ (γ↓-dec-β Upd Brs pd brs i p)))
    -- ≡ μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs p))} (ν↓ s (λ p → lvs↓ (brs p))))
