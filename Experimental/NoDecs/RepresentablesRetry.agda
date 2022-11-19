--
--  Representables.agda - Representable Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType 

module Experimental.NoDecs.RepresentablesRetry where

  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Type n ℓ
  𝕋 zero = tt*
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit

  --
  --  Some opetopes 
  --
  
  𝒪 : ℕ → Type
  𝒪 n = Frm (𝕋 n) 

  obj : 𝒪 0
  obj = tt*

  arr : 𝒪 1
  arr = tt* , tt* , tt*

  drop : 𝒪 2
  drop = arr , lf tt* , tt*

  2-globe : 𝒪 2
  2-globe = arr , nd tt* [ tt* , tt* , lf tt* ] tt* , tt* 

  canopy : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π) → Src (const Unit*) π
  canopy {n} π brs = μ (id-map (𝕋 n)) (Branch (const Unit*)) (λ _ → Lift Unit) brs (λ p → lvs (brs ⊚ p))

  --
  --  The codimension 2 part of the representable
  --

  Repr₀ : (n : ℕ) → 𝒪 (suc n) → 𝕆Type n ℓ-zero
  Frm₀ : (n : ℕ) (π : 𝒪 (suc n)) → Frm (Repr₀ n π)

  Inc : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
      → (p : Pos (Branch (const Unit*)) {f = π} brs)
      → (Repr₀ (suc n) ((Typ _ brs p , lvs (brs ⊚ p) , stm (brs ⊚ p)) , br (brs ⊚ p) , tt*))
      ⇒ Repr₀ (suc n) ((π , canopy π brs , tt*) , nd tt* brs tt* , tt*)

  data Face₀ : {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    → Frm (Repr₀ n (π , σ , tt*)) → Type 

  Repr₀ zero _ = tt*
  Repr₀ (suc n) ((π , σ , tt*) , τ , tt*) =
    Repr₀ n (π , σ , tt*) , Face₀ π σ τ 

  data Face₀ where

    new-cell : {n : ℕ} (π : 𝒪 n)
      → (σ : Src (const Unit*) π)
      → (τ : Pd (const Unit*) (π , σ , tt*))
      → Face₀ π σ τ (Frm₀ n (π , σ , tt*)) 

    old-cell : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
      → (p : Pos (Branch (const Unit*)) {f = π} brs)
      → (f : Frm (Repr₀ n (Typ _ brs p , lvs (brs ⊚ p) , stm (brs ⊚ p))))
      → (face : Face₀ (Typ _ brs p) (lvs (brs ⊚ p)) (br (brs ⊚ p)) f)
      → Face₀ π (canopy π brs) (nd tt* brs tt*) (Frm⇒ (Inc π brs p .fst) f) 

  Src₀ : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → Src (Face₀ π σ τ) (Frm₀ n (π , σ , tt*))

  Frm₀ zero π = tt*
  Frm₀ (suc n) ((π , σ , tt*) , τ , tt*) =
    Frm₀ n (π , σ , tt*) , Src₀ π σ τ , new-cell π σ τ

  Src₀ {n} π ._ (lf tt*) =
  
    η (Face₀ π (η (const Unit*) {f = π} tt*) (lf tt*))
      {f = (Frm₀ n (π , η (const Unit*) {f = π} tt* , tt*))}
      (new-cell π (η (const Unit*) {f = π} tt*) (lf tt*))

  -- Can we use the inclusion to solve this quickly?
  Src₀ {n} π ._ (nd tt* brs tt*) = {!!}


  Inc =  {!!}
