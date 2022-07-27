{-# OPTIONS --no-positivity-check --no-termination-check #-}
--
--  Universe.agda - The opetopic type of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType

module Experimental.Local.Universe where

  𝕆U : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)

  Frm↓ : ∀ {n ℓ} → Frm (𝕆U n ℓ) → Type ℓ

  CellFib : ∀ {n ℓ} → Frm (𝕆U n ℓ) → Type (ℓ-suc ℓ)
  CellFib {ℓ = ℓ} F = Frm↓ F → Type ℓ

  Src↓ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src X F)
    → Frm↓ F → Type ℓ 

  Typ↓ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {S : Src X F}
    → {f : Frm↓ F} (s : Src↓ P S f)
    → (p : Pos {X = 𝕆U n ℓ} X S)
    → Frm↓ (Typ X S p)

  _⊚↓_ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → {P : {F : Frm (𝕆U n ℓ)} → X F → Frm↓ F → Type ℓ}
    → {F : Frm (𝕆U n ℓ)} {S : Src X F}
    → {f : Frm↓ F} (s : Src↓ P S f)
    → (p : Pos {X = 𝕆U n ℓ} X S)
    → P (S ⊚ p) (Typ↓ P s p) 

  Dec↓ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ))
    → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
    → (Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src X F) (D : Dec {X = 𝕆U n ℓ} Y S)
    → {f : Frm↓ F} (s : Src↓ P S f)
    → Type ℓ

  _⊛↓_ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → {Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ)}
    → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
    → {Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ}
    → {F : Frm (𝕆U n ℓ)} {S : Src X F} {D : Dec {X = 𝕆U n ℓ} Y S}
    → {f : Frm↓ F} {s : Src↓ P S f}
    → Dec↓ Y Q S D s
    → (p : Pos X S) → Q (D ⊛ p) (s ⊚↓ p) 

  λ-dec↓ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → {Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ)}
    → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
    → (Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {S : Src X F}
    → (D : Dec {X = 𝕆U n ℓ} Y S)
    → {f : Frm↓ F} {s : Src↓ P S f}
    → (δ : (p : Pos X S) → Q (D ⊛ p) (s ⊚↓ p))
    → Dec↓ Y Q S D s

  ν↓ : ∀ {n ℓ} 
    → {X Y : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
    → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
    → {F : Frm (𝕆U n ℓ)} {S : Src X F}
    → {ϕ : (p : Pos X S) → Y (Typ X S p)}
    → {f : Frm↓ F} (s : Src↓ P S f)
    → (ψ : (p : Pos X S) → Q (ϕ p) (Typ↓ P s p))
    → Src↓ Q (ν S ϕ) f

  η↓ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
    → {C : X F} (x : P C f)
    → Src↓ P (η X C) f

  μ↓ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
    → {S : Src (Src X) F} (s : Src↓ (Src↓ P) S f)
    → Src↓ P (μ X S) f

  𝕆U zero ℓ = tt*
  𝕆U (suc n) ℓ = 𝕆U n ℓ , CellFib 

  Frm↓ {zero} _ = Unit*
  Frm↓ {suc n} (F , S , T) = 
    Σ[ f ∈ Frm↓ F ]
    Σ[ s ∈ Src↓ {X = CellFib} (λ C → C) S f ]
    T f

  postulate

    --
    --  Decoration Computation
    --
    
    λ-dec↓-β : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → (D : Dec {X = 𝕆U n ℓ} Y S)
      → {f : Frm↓ F} {s : Src↓ P S f}
      → (δ : (p : Pos X S) → Q (D ⊛ p) (s ⊚↓ p))
      → (p : Pos X S)
      → λ-dec↓ Q D δ ⊛↓ p ↦ δ p 
    {-# REWRITE λ-dec↓-β #-} 

    λ-dec↓-η : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → (D : Dec {X = 𝕆U n ℓ} Y S)
      → {f : Frm↓ F} {s : Src↓ P S f}
      → (δ : Dec↓ Y Q S D s)
      → λ-dec↓ Q D (λ p → δ ⊛↓ p) ↦ δ
    {-# REWRITE λ-dec↓-η #-}
    
    --
    --  Typing and Inhabitants
    --

    Typ↓-ν↓ : ∀ {n ℓ} 
      → {X Y : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {ϕ : (p : Pos X S) → Y (Typ X S p)}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → (ψ : (p : Pos X S) → Q (ϕ p) (Typ↓ P s p))
      → (p : Pos Y (ν S ϕ))
      → Typ↓ Q (ν↓ s ψ) p ↦ Typ↓ P s (ν-lift S ϕ p)
    {-# REWRITE Typ↓-ν↓ #-}

    ⊚↓-ν↓ : ∀ {n ℓ} 
      → {X Y : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {ϕ : (p : Pos X S) → Y (Typ X S p)}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → (ψ : (p : Pos X S) → Q (ϕ p) (Typ↓ P s p))
      → (p : Pos Y (ν S ϕ))
      → ν↓ {Q = Q} s ψ ⊚↓ p ↦ ψ (ν-lift S ϕ p)
    {-# REWRITE ⊚↓-ν↓ #-}

    Typ↓-η↓ : ∀ {n ℓ} 
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → (C : X F) (x : P C f)
      → (p : Pos X (η X C))
      → Typ↓ P (η↓ P x) p ↦ f
    {-# REWRITE Typ↓-η↓ #-}

    ⊚↓-η↓ : ∀ {n ℓ} 
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → (C : X F) (x : P C f)
      → (p : Pos X (η X C))
      → η↓ P x ⊚↓ p ↦ x
    {-# REWRITE ⊚↓-η↓ #-}

    Typ↓-μ↓ : ∀ {n ℓ} 
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → {S : Src (Src X) F} (s : Src↓ (Src↓ P) S f)
      → (p : Pos X (μ X S))
      → Typ↓ P (μ↓ P s) p ↦ Typ↓ P (s ⊚↓ μ-fst X S p) (μ-snd X S p)
    {-# REWRITE Typ↓-μ↓ #-}

    ⊚↓-μ↓ : ∀ {n ℓ} 
      → (X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → {S : Src (Src X) F} (s : Src↓ (Src↓ P) S f)
      → (p : Pos X (μ X S))
      → μ↓ P s ⊚↓ p ↦ ((s ⊚↓ μ-fst X S p) ⊚↓ μ-snd X S p)
    {-# REWRITE ⊚↓-μ↓ #-}
    
    --
    --  Functoriality of ν↓
    --

    ν↓-id : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → ν↓ {Q = P} s (_⊚↓_ s) ↦ s
    {-# REWRITE ν↓-id #-}

    ν↓-comp : ∀ {n ℓ} 
      → {X Y Z : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
      → {R : {F : Frm (𝕆U n ℓ)} → Z F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {ϕ : (p : Pos X S) → Y (Typ X S p)}
      → {ϕ' : (p : Pos Y (ν S ϕ)) → Z (Typ Y (ν S ϕ) p)}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → (ψ : (p : Pos X S) → Q (ϕ p) (Typ↓ P s p))
      → (ψ' : (p : Pos Y (ν S ϕ)) → R (ϕ' p) (Typ↓ Q (ν↓ s ψ) p))
      → ν↓ {Q = R} (ν↓ {Q = Q} s ψ) ψ' ↦ ν↓ {Q = R} s (λ p → ψ' (ν-pos S ϕ p))
    {-# REWRITE ν↓-comp #-}

    --
    --  Naturality of μ↓ and η↓
    --

    ν↓-η↓ : ∀ {n ℓ} 
      → {X Y : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {C : X F}
      → {ϕ : (p : Pos X (η X C)) → Y (Typ X (η X C) p)}
      → {f : Frm↓ F} (x : P C f)
      → (ψ : (p : Pos X (η X C)) → Q (ϕ p) (Typ↓ P (η↓ P x) p))
      → ν↓ (η↓ P x) ψ ↦ η↓ Q (ψ (η-pos X C))
    {-# REWRITE ν↓-η↓ #-}

    ν↓-μ↓ : ∀ {n ℓ} 
      → {X Y : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {Q : {F : Frm (𝕆U n ℓ)} → Y F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → {S : Src (Src X) F} (s : Src↓ (Src↓ P) S f)
      → (ϕ : (p : Pos X (μ X S)) → Y (Typ X (μ X S) p))
      → (ψ : (p : Pos X (μ X S)) → Q (ϕ p) (Typ↓ P (μ↓ P s) p))
      → ν↓ (μ↓ P s) ψ ↦ μ↓ Q (ν↓ s λ p → ν↓ (s ⊚↓ p) (λ q → ψ (μ-pos X S p q)))
    {-# REWRITE ν↓-μ↓ #-}

    --
    -- Monad Laws
    --

    μ↓-unit-l : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → {S : Src X F} (s : Src↓ P S f)
      → μ↓ P (η↓ (Src↓ P) s) ↦ s
    {-# REWRITE μ↓-unit-l #-}

    μ↓-unit-r : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → {S : Src X F} (s : Src↓ P S f)
      → μ↓ P (ν↓ s (λ p → η↓ P (s ⊚↓ p))) ↦ s 
    {-# REWRITE μ↓-unit-r #-}

    μ↓-assoc : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → {S : Src (Src (Src X)) F}
      → (s : Src↓ (Src↓ (Src↓ P)) S f)
      → μ↓ P (μ↓ (Src↓ P) s) ↦ μ↓ P (ν↓ s λ p → μ↓ P (s ⊚↓ p)) 
    {-# REWRITE μ↓-assoc #-}


  module _ {n ℓ}
    (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) where

    Pd↓ : {F : Frm (𝕆U (suc n) ℓ)} (ρ : Pd X F) → Frm↓ F → Type ℓ

    record Branch↓ {F : Frm (𝕆U n ℓ)} {T : CellFib F} (B : Branch X T)
                   {f : Frm↓ F} (t : T f) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_]↓
      field
        lvs↓ : Src↓ {X = CellFib} (λ C → C) (lvs B) f
        br↓ : Pd↓ (br B) (f , lvs↓ , t)

    open Branch↓ public

    data Pd↓Lf {F : Frm (𝕆U n ℓ)} (C : Frm↓ F → Type ℓ)
      : Frm↓ {suc n} (F , η {X = 𝕆U n ℓ} CellFib C , C) → Type ℓ where

      lf↓ : {f : Frm↓ F} (x : C f) → Pd↓Lf C (f , η↓ (λ C → C) x , x)

    data Pd↓Nd {F : Frm (𝕆U n ℓ)} (S : Src CellFib F) (T : CellFib F)
      (C : X (F , S , T)) (Brs : Dec {X = 𝕆U n ℓ} (Branch X) S)
      : Frm↓ {suc n} (F , μ {X = 𝕆U n ℓ} CellFib (ν {X = 𝕆U n ℓ} S (λ p → lvs (Brs ⊛ p))) , T) → Type ℓ where

      nd↓ : {frm : Frm↓ F} (src : Src↓ {X = CellFib} (λ C → C) S frm) (tgt : T frm)
        → (flr : P C (frm , src , tgt))
        → (brs : Dec↓ (Branch X) Branch↓ S Brs src)
        → Pd↓Nd S T C Brs (frm , μ↓ (λ C → C) (ν↓ src (λ p → lvs↓ (brs ⊛↓ p))) , tgt)

    Pd↓ (lf C) = Pd↓Lf C
    Pd↓ (nd S T C Brs) = Pd↓Nd S T C Brs

    γ↓ : {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} {T : CellFib F}
      → {Upd : Pd X (F , S , T)}
      → {Brs : (p : Pos {X = 𝕆U n ℓ} CellFib S) → Branch X (S ⊚ p)}
      → {f : Frm↓ F} {s : Src↓ {X = CellFib} (λ C → C) S f} {t : T f}
      → (pd : Pd↓ Upd (f , s , t))
      → (brs : (p : Pos {X = 𝕆U n ℓ} CellFib S) → Branch↓ (Brs p) (s ⊚↓ p))
      → Pd↓ (γ X Upd Brs) (f , μ↓ (λ C → C) (ν↓ s (λ p → lvs↓ (brs p))) , t)
    γ↓ {Upd = lf C} (lf↓ x) brs = br↓ (brs (η-pos CellFib C))
    γ↓ {Upd = nd S T C LBrs} {Brs} (nd↓ src tgt flr lbrs) brs =
      nd↓ src tgt flr (λ-dec↓ Branch↓ (λ-dec (Branch X) S (γ-brs X LBrs Brs)) λ p → 
        [ _ , γ↓ (br↓ (lbrs ⊛↓ p)) (λ q → brs (canopy-pos X LBrs p q)) ]↓)

  Src↓ {zero} P S F = P S tt*
  Src↓ {suc n} {X = X} P S F = Pd↓ X P S F 

  Typ↓ {zero} P s p = tt*
  Typ↓ {suc n} P {S = nd S T C Brs} (nd↓ src tgt flr brs) nd-here = _ , src , tgt
  Typ↓ {suc n} P {S = nd S T C Brs} (nd↓ src tgt flr brs) (nd-there p q) = Typ↓ P (br↓ (brs ⊛↓ p)) q

  _⊚↓_ {zero} s p = s
  _⊚↓_ {suc n} {S = nd S T C Brs} (nd↓ src tgt flr brs) nd-here = flr
  _⊚↓_ {suc n} {S = nd S T C Brs} (nd↓ src tgt flr brs) (nd-there p q) = _⊚↓_ (br↓ (brs ⊛↓ p)) q

  Dec↓ {zero} Y Q S D s = Q D s
  Dec↓ {suc n} Y Q (lf tgt) D s = Unit*
  Dec↓ {suc n} {ℓ} {X = X} Y {P = P} Q (nd {F} S T C Brs) (y , D) (nd↓ {frm} src tgt flr brs) =
    Q y flr × Dec↓ {n = n} {X = λ F → Σ (CellFib F) (Branch X)}
              (λ CB → Dec {X = 𝕆U n ℓ , CellFib} Y (br (snd CB)))
              {P = λ pr f → Σ (fst pr f) (Branch↓ X P (snd pr))}
              (λ {F} {CB} D' {f} cb → Dec↓ Y Q (br (snd CB)) D' (br↓ (snd cb)))
              (ν {Q = λ F → Σ (CellFib F) (Branch X)} S (λ p → S ⊚ p , Brs ⊛ p)) D
              (ν↓ {Y = λ F → Σ (CellFib F) (Branch X)} src (λ p → src ⊚↓ p , brs ⊛↓ p))

  _⊛↓_ {zero} δ p = δ
  _⊛↓_ {suc n} {S = nd S T C Brs} {s = nd↓ src tgt flr brs} (q , _) nd-here = q
  _⊛↓_ {suc n} {S = nd S T C Brs} {s = nd↓ src tgt flr brs} (_ , δ) (nd-there p q) =
    (δ ⊛↓ ν-pos S (λ p → (S ⊚ p) , (Brs ⊛ p)) p) ⊛↓ q

  λ-dec↓ {zero} Q {S = S} D {s = s} δ = δ tt*
  λ-dec↓ {suc n} Q {S = lf tgt} D {s = s} δ = tt*
  λ-dec↓ {suc n} {ℓ} {X} {Y} {P} Q {S = nd S T C Brs} D {s = nd↓ src tgt flr brs} δ =
    δ nd-here , λ-dec↓ {n} {X = λ F → Σ (CellFib F) (Branch X)}
                  {Y = λ CB → Dec {X = 𝕆U n ℓ , CellFib} Y (br (snd CB))}
                  {P = λ pr f → Σ (fst pr f) (Branch↓ X P (snd pr))}
                  (λ {F} {CB} D' {f} cb → Dec↓ Y Q (br (snd CB)) D' (br↓ (snd cb))) (snd D) 
                  (λ p → λ-dec↓ Q (snd D ⊛ p) (λ q → δ (nd-there (ν-lift S (λ p → (S ⊚ p) , (Brs ⊛ p)) p) q)))

  ν↓ {zero} {S = S} s ψ = ψ tt*
  ν↓ {suc n} {S = lf C} (lf↓ x) ψ = lf↓ x
  ν↓ {suc n} {S = nd S T C Brs} (nd↓ src tgt flr brs) ψ =
    nd↓ src tgt (ψ nd-here) (λ-dec↓ (Branch↓ _ _) _ λ p →
      [ lvs↓ (brs ⊛↓ p) , (ν↓ {suc n} (br↓ (brs ⊛↓ p)) (λ q → ψ (nd-there p q))) ]↓)

  η↓ {zero} P x = x
  η↓ {suc n} {ℓ} {X} P {F = F , S , T} {f = f , s , t} x =
    nd↓ s t x (λ-dec↓ (Branch↓ X P)
        (η-dec {X = 𝕆U n ℓ} {P = CellFib} X S) 
        (λ p → [ η↓ (λ C → C) {C = S ⊚ p} (s ⊚↓ p) , lf↓ (s ⊚↓ p) ]↓))
  
  μ↓ {zero} P {S = S} s = s
  μ↓ {suc n} P {S = lf tgt} (lf↓ x) = lf↓ x
  μ↓ {suc n} {X = X} P {S = nd S T C Brs} (nd↓ src tgt flr brs) =
    γ↓ X P flr (λ p → [ lvs↓ (brs ⊛↓ p) , μ↓ P (br↓ (brs ⊛↓ p)) ]↓)
