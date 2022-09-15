--
--  CompositeFibrant.agda - The composite of fibrant relations is fibrant
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Core.OpetopicType
open import Core.Universe

open import Lib.Decorations
open import Lib.CategoryOfTypes.Lemmas
open import Lib.CategoryOfTypes.EtaInversion
open import Lib.CategoryOfTypes.MuInversion

module Lib.CategoryOfTypes.CompositeFibrant where

  ucomp : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → CellFib F
  ucomp {F = F} S ϕ = USrc↓ {F = F} S 

  ufill : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → CellFib (F , S , ucomp S ϕ)
  ufill S ϕ (f , s , t) = s ≡ t 

  ufill-is-fib-rel : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → is-fib-rel (ufill S ϕ)
  ufill-is-fib-rel S ϕ f s = isContrSingl s

  --
  --  Inverting Lf↓
  --

  module _ {n ℓ}
    {F : Frm (𝕆U n ℓ)} (T : CellFib F)  where

    src-over-lf-to : {f : Frm↓ F} (s : USrc↓ (ηU T) f)
      → Σ[ t ∈ T f ] (η↓ (λ P → P) {C = T} t ≡ s)
      → Σ[ t ∈ T f ] (USrc↓ (lf T) (f , s , t))
    src-over-lf-to {f} s (t , p) =
      J (λ s' p' → Σ[ t ∈ T f ] (USrc↓ (lf T) (f , s' , t)))
      (t , lf↓ t) p  

    src-over-lf-from : {f : Frm↓ F} (s : USrc↓ (ηU T) f)
      → Σ[ t ∈ T f ] (USrc↓ (lf T) (f , s , t))
      → Σ[ t ∈ T f ] (η↓ (λ P → P) {C = T} t ≡ s)
    src-over-lf-from ._ (t , lf↓ .t) = t , refl

    src-over-lf-section : {f : Frm↓ F} (s : USrc↓ (ηU T) f)
      → section (src-over-lf-to s) (src-over-lf-from s)
    src-over-lf-section ._ (t , lf↓ .t) = transportRefl (t , lf↓ t)

    src-over-lf-retract : {f : Frm↓ F} (s : USrc↓ (ηU T) f)
      → retract (src-over-lf-to s) (src-over-lf-from s)
    src-over-lf-retract s (t , p) =
      J (λ s' p' → src-over-lf-from s' (src-over-lf-to s' (t , p')) ≡ (t , p')) lem p

      where lem = src-over-lf-from (ηU↓ T t) (src-over-lf-to (ηU↓ T t) (t , refl))
                    ≡[ i ]⟨ src-over-lf-from (ηU↓ T t) (transportRefl (t , lf↓ t) i) ⟩
                  (t , refl) ∎ 

    src-over-lf-equiv : {f : Frm↓ F} (s : USrc↓ (ηU T) f)
      → (Σ[ t ∈ T f ] (η↓ (λ P → P) {C = T} t ≡ s))
      ≃ (Σ[ t ∈ T f ] (USrc↓ (lf T) (f , s , t)))
    src-over-lf-equiv s = isoToEquiv
      (iso (src-over-lf-to s) (src-over-lf-from s)
           (src-over-lf-section s) (src-over-lf-retract s)) 

  --
  --  Inverting nd↓
  --
  
  module _ {n ℓ}
    (F : Frm (𝕆U n ℓ)) (S : Src CellFib F) (T : CellFib F)
    (C : CellFib (F , S , T)) (D : Dec {X = 𝕆U n ℓ} (Branch CellFib) S) where

    src-over-nd-to : (f : Frm↓ F) (cnpy : USrc↓ (canopy {X = 𝕆U n ℓ} CellFib {s = S} D) f)
      → Σ[ t ∈ T f ] (USrc↓ (nd S T C D) (f , cnpy , t))
      → Σ[ s ∈ Src↓ (λ C → C) S f ] 
          (Σ[ t ∈ T f ] C (f , s , t)) × 
          (Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S D s ]
            canopy↓ CellFib (λ C → C) {S = S} {D = D} {f = f} {s = s} brs ≡ cnpy)
    src-over-nd-to f ._ (.tgt , nd↓ src tgt flr brs) = src , ((tgt , flr) , (brs , refl))

    src-over-nd-from : (f : Frm↓ F) (cnpy : USrc↓ (canopy {X = 𝕆U n ℓ} CellFib {s = S} D) f)
      → Σ[ s ∈ Src↓ (λ C → C) S f ] 
          (Σ[ t ∈ T f ] C (f , s , t)) × 
          (Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S D s ]
            canopy↓ CellFib (λ C → C) {S = S} {D = D} {f = f} {s = s} brs ≡ cnpy)
      → Σ[ t ∈ T f ] (USrc↓ (nd S T C D) (f , cnpy , t))
    src-over-nd-from f cnpy (src , (tgt , flr) , (brs , p)) =
      J (λ c' p' → Σ[ t ∈ T f ] USrc↓ (nd S T C D) (f , c' , t))
        (tgt , nd↓ src tgt flr brs) p 

    src-over-nd-section : (f : Frm↓ F) (cnpy : USrc↓ (canopy {X = 𝕆U n ℓ} CellFib {s = S} D) f)
      → section (src-over-nd-to f cnpy) (src-over-nd-from f cnpy)
    src-over-nd-section f cnpy (src , (tgt , flr) , (brs , p)) = 
      J (λ c' p' → src-over-nd-to f c'
           (src-over-nd-from f c' (src , (tgt , flr) , brs , p'))
             ≡ (src , (tgt , flr) , brs , p'))
        lem p

      where lem = src-over-nd-to f (canopy↓ CellFib (λ C → C) {S = S} {D = D} {f = f} {s = src} brs)
                    (src-over-nd-from f (canopy↓ CellFib (λ C → C) {S = S} {D = D} {f = f} {s = src} brs)
                      (src , (tgt , flr) , brs , refl))
                      
                    ≡[ i ]⟨ src-over-nd-to f (canopy↓ CellFib (λ C → C) {S = S} {D = D} {f = f} {s = src} brs)
                              (transportRefl (tgt , nd↓ src tgt flr brs) i) ⟩
                    
                  (src , (tgt , flr) , brs , refl) ∎
                  
    src-over-nd-retract : (f : Frm↓ F) (cnpy : USrc↓ (canopy {X = 𝕆U n ℓ} CellFib {s = S} D) f)
      → retract (src-over-nd-to f cnpy) (src-over-nd-from f cnpy)
    src-over-nd-retract f ._ (.tgt , nd↓ src tgt flr brs) = transportRefl (tgt , nd↓ src tgt flr brs) 

    src-over-nd-equiv : (f : Frm↓ F) (cnpy : USrc↓ (canopy {X = 𝕆U n ℓ} CellFib {s = S} D) f)
      → (Σ[ t ∈ T f ] (USrc↓ (nd S T C D) (f , cnpy , t)))
      ≃ (Σ[ s ∈ Src↓ (λ C → C) S f ] 
          (Σ[ t ∈ T f ] C (f , s , t)) × 
          (Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S D s ]
           canopy↓ CellFib (λ C → C) {S = S} {D = D} {f = f} {s = s} brs ≡ cnpy))
    src-over-nd-equiv f cnpy = isoToEquiv
      (iso (src-over-nd-to f cnpy) (src-over-nd-from f cnpy)
           (src-over-nd-section f cnpy) (src-over-nd-retract f cnpy)) 

  --
  --  Main theorem
  --

  {-# TERMINATING #-}
  ucomp-is-fib-rel : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → is-fib-rel (USrc↓ {F = F} S)

  ucomp-is-fib-rel {zero} S ϕ = tt*
  ucomp-is-fib-rel {suc n} (lf {F} T) ϕ f cnpy = 
    isOfHLevelRespectEquiv 0 (src-over-lf-equiv T cnpy)
      ((η↓-equiv T f) .snd .equiv-proof cnpy) 

  ucomp-is-fib-rel {suc n} {ℓ} (nd {F} S T C Brs) ϕ f cnpy = 
    isOfHLevelRespectEquiv 0 (invEquiv lemma)
      (μ↓-equiv {X = CellFib} (λ C → C) {F = F}
        (ν {f = F} S (λ p → lvs (Brs ⊛ p))) f .snd .equiv-proof cnpy) 

    where module D = Dec↓ΣEquiv {n} {ℓ} CellFib (Branch CellFib) (λ C → C) (Branch↓ CellFib (λ C → C))

          ih : (p : Pos D.D.ΣPQ (D.D.to (S , Brs))) → is-fib-rel (USrc↓ (br (Brs ⊛ ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p)))
          ih p = ucomp-is-fib-rel (br (Brs ⊛ ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p))
                                               (λ q → ϕ (nd-there (ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p) q))
                                               
          claim : Src↓ D.ΣUV (D.D.to (S , Brs)) f ≃ Src↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) (D.D.to (S , Brs)) f
          claim = Src↓-emap D.D.ΣPQ D.ΣUV (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) (D.D.to (S , Brs))
                            (λ p f → D.ΣUV (D.D.to (S , Brs) ⊚ p) f
                            
                                       ≃⟨ isoToEquiv (iso (λ (c , br) → lvs↓ br , c , br↓ br)
                                                          (λ (l , c , b) → c , [ l , b ]↓)
                                                          (λ cbr → refl {x = cbr})
                                                          λ lcb → refl {x = lcb}) ⟩
                                       
                                     Σ[ s ∈ (Src↓ (λ C → C) (lvs (Brs ⊛ ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p)) f) ]
                                     Σ[ c ∈ (S ⊚ ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p) f ]
                                     USrc↓ (br (Brs ⊛ ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p)) (f , s , c) 
                                     
                                       ≃⟨ Σ-contractSnd (λ s → ih p f s) ⟩ 
                                               
                                     Src↓ (λ C → C) (lvs (Brs ⊛ ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p)) f ■) f

          lemma = (Σ[ t ∈ T f ] Src↓ (λ C → C) (nd S T C Brs) (f , cnpy , t))

                    ≃⟨ src-over-nd-equiv F S T C Brs f cnpy ⟩

                  (Σ[ s ∈ Src↓ (λ C → C) S f ] 
                    (Σ[ t ∈ T f ] C (f , s , t)) × 
                    (Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S Brs s ]
                     bind↓ (λ C → C) (λ C → C) {F = F} S
                       (λ p → lvs (Brs ⊛ p)) s
                       (λ p → lvs↓ (brs ⊛↓ p)) ≡ cnpy))

                    ≃⟨ Σ-cong-equiv-snd (λ s → Σ-contractFst (ϕ nd-here f s)) ⟩

                  (Σ[ s ∈ Src↓ (λ C → C) S f ] 
                   Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S Brs s ]
                   bind↓ (λ C → C) (λ C → C) {F = F} S
                     (λ p → lvs (Brs ⊛ p)) s
                     (λ p → lvs↓ (brs ⊛↓ p)) ≡ cnpy)

                    ≃⟨ invEquiv Σ-assoc-≃ ⟩

                  (Σ[ sb ∈ (Σ[ s ∈ Src↓ (λ C → C) S f ] (Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S Brs s)) ] 
                   bind↓ (λ C → C) (λ C → C) {F = F}
                     S (λ p → lvs (Brs ⊛ p))
                     (fst sb) (λ p → lvs↓ (snd sb ⊛↓ p))
                     ≡ cnpy)

                    ≃⟨ Σ-cong-equiv-fst (D.eqv S Brs) ⟩

                  -- D.ΣUV              =   λ (C , Br) f → Σ[ c ∈ C f ] Branch↓ CellFib (λ C → C) Br c
                  -- D.D.to (S , Brs)   =   ν {Q = λ F → Σ[ C ∈ CellFib F ] Branch CellFib C} {f = F} S (λ p → S ⊚ p , Brs ⊛ p)
                  (Σ[ s ∈ Src↓ D.ΣUV (D.D.to (S , Brs)) f ] 
                                                        
                   bind↓ D.ΣUV (λ C → C) {F = F}
                     (D.D.to (S , Brs)) (λ p → lvs (snd ((D.D.to (S , Brs)) ⊚ p))) 
                     s (λ p → lvs↓ (snd (s ⊚↓ p)))
                     ≡ cnpy)

                    ≃⟨ invEquiv (Σ-cong-equiv-fst {A = Src↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) (D.D.to (S , Brs)) f }
                                         {A' = Src↓ D.ΣUV (D.D.to (S , Brs)) f}
                                         {B = λ s → bind↓ D.ΣUV (λ C → C) {F = F}
                                           (D.D.to (S , Brs)) (λ p → lvs (snd ((D.D.to (S , Brs)) ⊚ p))) 
                                           s (λ p → lvs↓ (snd (s ⊚↓ p)))
                                           ≡ cnpy} (invEquiv (claim))) ⟩ 

                  (Σ[ s ∈ Src↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) (ν {f = F} S (λ p → S ⊚ p , Brs ⊛ p)) f ] 
                                                        
                   let s' = ν↓ {Q = D.ΣUV} {S = D.D.to (S , Brs)} {ϕ = λ p → D.D.to (S , Brs) ⊚ p}
                               s (λ p → ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .fst ,
                                         [ s ⊚↓ p , ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .snd ]↓)
                       s'' = ν↓ {F = F} {S = D.D.to (S , Brs)} {ϕ = λ p → lvs (snd ((D.D.to (S , Brs)) ⊚ p))} {f = f} s' (λ p → lvs↓ (snd (s' ⊚↓ p)))

                       t = ν↓ {Q = Src↓ (λ C → C)} {F} {ν {f = F} S (λ p → (S ⊚ p) , (Brs ⊛ p))} {f = f} s (λ p → s ⊚↓ p)
                       -- t' = ν↓ {Q = Src↓ (λ C → C)} {F} {ν {f = F} S (λ p → (S ⊚ p) , (Brs ⊛ p))} {f = f} s 
                       --        (λ p → lvs↓ (snd (ν↓ s (λ p → ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .fst ,
                       --                   [ s ⊚↓ p , ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .snd ]↓) ⊚↓ p)))
                                         
                       need : ν↓ {f = f} (ν↓ {f = f} s (λ p → ih p (Typ↓ (λ pr → Src↓ (λ C₁ → C₁) (lvs (snd pr))) s p) (s ⊚↓ p) .fst .fst ,
                                   [ s ⊚↓ p , ih p (Typ↓ (λ pr → Src↓ (λ C₁ → C₁) (lvs (snd pr))) s p) (s ⊚↓ p) .fst .snd ]↓))
                                 (λ p → lvs↓ (snd (ν↓ s (λ p₁ → ih p₁ (Typ↓ (λ pr → Src↓ (λ C₁ → C₁) (lvs (snd pr))) s p₁) (s ⊚↓ p₁) .fst .fst ,
                                                   [ s ⊚↓ p₁ ,  ih p₁ (Typ↓ (λ pr → Src↓ (λ C₁ → C₁) (lvs (snd pr))) s p₁) (s ⊚↓ p₁) .fst .snd ]↓) ⊚↓ p)))
                               ≡ 
                              ν↓ {Q = Src↓ (λ C → C)} {F} {ν {f = F} S (λ p → (S ⊚ p) , (Brs ⊛ p))} {f = f} s
                                   (λ p → lvs↓ (snd (ν↓ s (λ p₁ → ih p₁ (Typ↓ (λ pr → Src↓ (λ C₁ → C₁) (lvs (snd pr))) s p₁) (s ⊚↓ p₁) .fst .fst ,
                                                     [ s ⊚↓ p₁ ,  ih p₁ (Typ↓ (λ pr → Src↓ (λ C₁ → C₁) (lvs (snd pr))) s p₁) (s ⊚↓ p₁) .fst .snd ]↓) ⊚↓ p)))

                       need = ν↓-comp-id {R = D.ΣUV} {F} {D.D.to (S , Brs)} {ϕ' = λ p → D.D.to (S , Brs) ⊚ p} {f = f} s
                                 (λ p → ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .fst ,
                                         [ s ⊚↓ p , ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .snd ]↓)
                                   (λ p → lvs↓ (snd (ν↓ s (λ p → ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .fst ,
                                         [ s ⊚↓ p , ih p (Typ↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) s p) (s ⊚↓ p) .fst .snd ]↓) ⊚↓ p)))

                   in μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))} s''
                        ≡ cnpy)

                    ≃⟨ {!!} ⟩ 

                  -- → ν↓ {Q = R} (ν↓ {Q = Q} s ψ) ψ' ↦ ν↓ {Q = R} s (λ p → ψ' (ν-pos S ϕ p))

                  (Σ[ s ∈ Src↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) (ν {f = F} S (λ p → S ⊚ p , Brs ⊛ p)) f ] 
                                                        
                     μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))}
                         (ν↓ {Q = Src↓ (λ C → C)} {F} {ν {f = F} S (λ p → (S ⊚ p) , (Brs ⊛ p))} {f = f}
                            s (λ p → s ⊚↓ p)) ≡ cnpy)

                    ≃⟨ Σ-cong-equiv-fst {A = Src↓ (λ (C , Br) → Src↓ (λ C → C) (lvs Br)) (ν {f = F} S (λ p → S ⊚ p , Brs ⊛ p)) f}
                                         {A' = Src↓ (Src↓ (λ C → C)) (ν {f = F} S (λ p → lvs (Brs ⊛ p))) f}
                                         {B = λ s → μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))} s ≡ cnpy}
                                         (Src↓-base-map D.D.ΣPQ (Src CellFib) (λ x → lvs (snd x)) (Src↓ (λ C → C))
                                           {F} (ν {f = F} S (λ p → S ⊚ p , Brs ⊛ p)) f) ⟩ 


                  (Σ[ s ∈ Src↓ (Src↓ (λ C → C)) (ν {f = F} S (λ p → lvs (Brs ⊛ p))) f ]
                      μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))} s ≡ cnpy) ■


