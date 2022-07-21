{-# OPTIONS --no-termination-check #-}
--
--  Sigma.agda - Sigma of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Universe

module Experimental.Local.UniversalFib where

  𝕆V : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝕆π : (n : ℕ) (ℓ : Level) → 𝕆V n ℓ ⇒ 𝕆U n ℓ 

  π-Frm : ∀ {n ℓ} → (f : Frm (𝕆V n ℓ)) → Frm↓ (Frm⇒ (𝕆π n ℓ) f)

  ElFib : ∀ {n ℓ} 
    → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
    → Frm (𝕆V n ℓ) → Type (ℓ-suc ℓ)
  ElFib {n} {ℓ} X P f =
    Σ[ C ∈ X (Frm⇒ (𝕆π n ℓ) f) ]
    P C (π-Frm f) 

  π-Src : ∀ {n ℓ}
    → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
    → {f : Frm (𝕆V n ℓ)} (s : Src (ElFib X P) f)
    → Src↓ X P (Src⇒ s (𝕆π n ℓ) (λ p → fst (s ⊚ p))) (π-Frm f)

  postulate

    Typ↓-π-Src : ∀ {n ℓ}
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
      → {f : Frm (𝕆V n ℓ)} (s : Src (ElFib X P) f)
      → (p : Pos X (Src⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q))))
      → Typ↓ P (π-Src X P s) p ↦ π-Frm (Typ (ElFib X P) s (Pos⇐ s (𝕆π n ℓ) (λ q → fst (s ⊚ q)) p)) 
    {-# REWRITE Typ↓-π-Src #-}

    ⊚↓-π-Src : ∀ {n ℓ}
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
      → {f : Frm (𝕆V n ℓ)} (s : Src (ElFib X P) f)
      → (p : Pos X (Src⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q))))
      → (π-Src X P s) ⊚↓ p ↦ snd (s ⊚ Pos⇐ s (𝕆π n ℓ) (λ q → fst (s ⊚ q)) p)
    {-# REWRITE ⊚↓-π-Src #-}
    
    π-Src-ν : ∀ {n ℓ} 
      → {X Y : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
      → {f : Frm (𝕆V n ℓ)} (s : Src (ElFib X P) f)
      → {ϕ : (p : Pos X (Src⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q)))) → Y (Typ X (Src⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q))) p)}
      → (ψ : (p : Pos X (Src⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q)))) → Q (ϕ p) (Typ↓ P (π-Src X P s) p))
      → ν↓ {P = P} {Q = Q} (π-Src X P {f = f} s) ψ ↦
         π-Src Y Q (ν {Q = ElFib Y Q} s (λ p →
           ϕ (Pos⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q)) p) ,
           ψ (Pos⇒ s (𝕆π n ℓ) (λ q → fst (s ⊚ q)) p)))
    {-# REWRITE π-Src-ν #-}

    π-Src-η : ∀ {n ℓ}
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
      → {f : Frm (𝕆V n ℓ)} (e : ElFib X P f)
      → π-Src X P {f = f} (η {X = 𝕆V n ℓ} (ElFib X P) e) ↦
        η↓ P {C = fst e} (snd e) 
    {-# REWRITE π-Src-η #-}

    π-Src-μ : ∀ {n ℓ}
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
      → {f : Frm (𝕆V n ℓ)} (s : Src (Src (ElFib X P)) f)
      → π-Src X P (μ {X = 𝕆V n ℓ} (ElFib X P) s) ↦
        μ↓ P (π-Src (Src X) (Src↓ X P)
          (ν {Q = ElFib (Src X) (Src↓ X P)} s
            (λ p → Src⇒ (s ⊚ p) (𝕆π n ℓ) (λ q → fst ((s ⊚ p) ⊚ q)) ,
                   π-Src X P (s ⊚ p))))
    {-# REWRITE π-Src-μ #-} 

    -- Note that we are *forced* to write the rule for ν in the
    -- direction we have above.  This suggests that the rules for η
    -- and μ should also follow this convention.  This is possible for
    -- η, but not for μ unless we add the corresponding "zipping"
    -- operation.  Don't know if this is a problem ...
    
    -- π-Src-η' : ∀ {n ℓ}
    --   → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    --   → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
    --   → {f : Frm (𝕆V n ℓ)} (C : X (Frm⇒ (𝕆π n ℓ) f))
    --   → (c : P C (π-Frm f))
    --   → η↓ P {C = C} c ↦ π-Src X P {f = f} (η {X = 𝕆V n ℓ} (ElFib X P) (C , c)) 
    -- {-# REWRITE π-Src-η' #-}

    -- π-Src-μ' : ∀ {n ℓ}
    --   → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    --   → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
    --   → {f : Frm (𝕆V n ℓ)} (s : Src (ElFib (Src X) (Src↓ X P)) f)  -- (s : Src (Src (ElFib X P)) f)
    --   → μ↓ P (π-Src (Src X) (Src↓ X P) s) ↦ {!!} 

  𝕆V zero ℓ = tt*
  𝕆V (suc n) ℓ = 𝕆V n ℓ , ElFib CellFib (λ C → C)

  𝕆π zero ℓ = tt*
  𝕆π (suc n) ℓ = 𝕆π n ℓ , fst

  π-Frm {zero} f = tt*
  π-Frm {suc n} (f , s , t) =
    π-Frm f , π-Src {n} CellFib (λ C → C) s , snd t

  π-Src-brs : ∀ {n ℓ}
    → (X : Frm (𝕆U (suc n) ℓ) → Type (ℓ-suc ℓ))
    → (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → Frm↓ F → Type ℓ)
    → {f : Frm (fst (𝕆V (suc n) ℓ))} (src : Src (snd (𝕆V (suc n) ℓ)) f)
    → (tgt : snd (𝕆V (suc n) ℓ) f) (flr : ElFib X P (f , src , tgt))
    → (brs : Dec {X = 𝕆V n ℓ} {P = ElFib CellFib (λ C → C)} (Branch (ElFib X P)) src)
    → (p : Pos CellFib (Src⇒ src (𝕆π n ℓ) (λ q → fst (src ⊚ q))))
    → Branch↓ X P
        (Src⇒-brs src tgt flr brs (𝕆π n ℓ) fst
         (λ p₁ → fst (nd src tgt flr brs ⊚ p₁)) p)
        (snd (src ⊚ Pos⇐ src (𝕆π n ℓ) (λ q → fst (src ⊚ q)) p)) 
  π-Src-brs {n} {ℓ} X P src tgt flr brs p = 
    let p' = Pos⇐ src (𝕆π n ℓ) (λ q → fst (src ⊚ q)) p
    in [ π-Src CellFib (λ C → C) {f = Typ (ElFib CellFib (λ C → C)) src p'} (lvs (brs ⊛ p'))   
       , π-Src {suc n} X P (br (brs ⊛ p')) 
       ]↓

  π-Src {zero} X P s = snd s
  π-Src {suc n} X P (lf tgt) = lf↓ (snd tgt)
  π-Src {suc n} {ℓ} X P (nd {frm} src tgt flr brs) =
    nd↓ (π-Src {n} CellFib (λ C → C) src) (snd tgt) (snd flr)
      (λ-dec↓ (Branch↓ X P)
          (Src⇒-brs src tgt flr brs (𝕆π n ℓ) fst
              (λ p → fst (nd src tgt flr brs ⊚ p)))
          {s = π-Src CellFib (λ C → C) {frm} src}
          (π-Src-brs X P src tgt flr brs))
                              
          

