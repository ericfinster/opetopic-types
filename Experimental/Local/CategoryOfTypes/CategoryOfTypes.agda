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
open import Experimental.Local.Universe
open import Experimental.Local.CategoryOfTypes.Lemmas

module Experimental.Local.CategoryOfTypes.CategoryOfTypes where

  UnivComp : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F) → CellFib F
  UnivComp S = Src↓ CellFib (λ C → C) S 

  is-fib : ∀ {n ℓ} {F : Frm (𝕆U (suc n) ℓ)} → CellFib F → Type ℓ
  is-fib {F = F , S , T} C =
      {f : Frm↓ F} (s : Src↓ CellFib (λ C → C) S f)
    → isContr (Σ[ t ∈ T f ] C (f , s , t)) 

  postulate

    η↓-is-equiv : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {C : X F} (f : Frm↓ F)
      → isEquiv (η↓ P {f = f} {C = C})

    μ↓-is-equiv : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {S : Src (Src X) F} (f : Frm↓ F)
      → isEquiv (μ↓ P {f = f} {S = S})

  η↓-inv : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {C : X F} {f : Frm↓ F}
    → Src↓ X P (η X C) f →  P C f
  η↓-inv P {f = f} s = invIsEq (η↓-is-equiv P f) s 

  μ↓-inv : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {S : Src (Src X) F} {f : Frm↓ F}
    → Src↓ X P (μ X S) f → Src↓ (Src X) (Src↓ X P) S f
  μ↓-inv P {f = f} s = invIsEq (μ↓-is-equiv P f) s


