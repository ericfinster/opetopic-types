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

module Experimental.NoDecs.RepresentablesFirst where

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


  -- 
  --  Representables
  --

  Repr₀ : (n : ℕ) → 𝒪 (suc n) → 𝕆Type n ℓ-zero

  ext-frm : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → (p : Pos (const Unit*) {f = π} σ)
    → Frm (Repr₀ n (π , σ , tt*))

  int-frm : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → (p : PdPos (const Unit*) {f = (π , σ , tt*)} τ)
    → Frm (Repr₀ n (π , σ , tt*))

  total-frm : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → Frm (Repr₀ n (π , σ , tt*))

  data Face₀ {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    : Frm (Repr₀ n (π , σ , tt*)) → Type where

    ext-face : (p : Pos (const Unit*) {f = π} σ)
      → Face₀ π σ τ (ext-frm π σ τ p)

    int-face : (p : PdPos (const Unit*) {f = (π , σ , tt*)} τ)
      → Face₀ π σ τ (int-frm π σ τ p) 

  src-pd : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → (p : PdPos (const Unit*) {f = (π , σ , tt*)} τ)
    → Src (Face₀ π σ τ) (int-frm π σ τ p)

  total-src : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → Src (Face₀ π σ τ) (total-frm π σ τ)

  total-el : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → Face₀ π σ τ (total-frm π σ τ)

  data Face₁ {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    : Frm (Repr₀ n (π , σ , tt*) , Face₀ π σ τ) → Type where

    src-face : (p : PdPos (const Unit*) {f = (π , σ , tt*)} τ)
      → Face₁ π σ τ (int-frm π σ τ p , src-pd π σ τ p , int-face p)

    tgt-face : Face₁ π σ τ (total-frm π σ τ , total-src π σ τ , total-el π σ τ)

  Repr₀ zero _ = tt*
  Repr₀ (suc n) ((π , σ , tt*) , τ , tt*) =
    Repr₀ n (π , σ , tt*) , Face₀ π σ τ

  ext-frm π ._ (lf tt*) p = {!!}
  ext-frm π ._ (nd tt* brs tt*) p = {!!}
  
  int-frm π σ τ p = {!!} 

  src-pd π σ τ p = {!!}
  
  total-frm = {!!} 
  total-src = {!!} 
  total-el = {!!} 
