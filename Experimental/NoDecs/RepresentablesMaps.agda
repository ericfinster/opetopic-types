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

module Experimental.NoDecs.RepresentablesMaps where

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
  
  data Face₀ : {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    → Frm (Repr₀ n (π , σ , tt*)) → Type 

  Repr₀ zero _ = tt*
  Repr₀ (suc n) ((π , σ , tt*) , τ , tt*) =
    Repr₀ n (π , σ , tt*) , Face₀ π σ τ 

  data Face₁ : (n : ℕ) (π : 𝒪 (suc n))
    → Frm (Repr₀ n π) → Type

  Repr₁ : (n : ℕ) → 𝒪 (suc n) → 𝕆Type (suc n) ℓ-zero
  Repr₁ n π = Repr₀ n π , Face₁ n π 

  TgtFrm : (n : ℕ) (π : 𝒪 (suc n))
    → Frm (Repr₀ n π)

  SrcFrm : (n : ℕ) (π : 𝒪 (suc n))
    → (p : Pos (const Unit*) {f = fst π} (π .snd .fst))
    → Frm (Repr₀ n π)

  ∂Frm : (n : ℕ) (π : 𝒪 (suc n))
    → Frm (Repr₁ n π)

  Inc : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → {f : Frm (Repr₀ n (π , σ , tt*))}
    → Face₁ n (π , σ , tt*) f → Face₀ π σ τ f 

  IncSrc : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → (p : Pos (const Unit*) {f = π , σ , tt*} τ)
    → Repr₁ n (PdTyp (const Unit*) τ p) ⇒ Repr₀ (suc n) ((π , σ , tt*) , τ , tt*)

  IncTgt : {n : ℕ} (π : 𝒪 n)
    → (σ : Src (const Unit*) π)
    → (τ : Pd (const Unit*) (π , σ , tt*))
    → Repr₁ n (π , σ , tt*) ⇒ Repr₀ (suc n) ((π , σ , tt*) , τ , tt*)
  IncTgt π σ τ = id-map (Repr₀ _ (π , σ , tt*)) , Inc π σ τ 

  data Face₀ where

    ext-face : {n : ℕ} (π : 𝒪 n)
      → (σ : Src (const Unit*) π)
      → (τ : Pd (const Unit*) (π , σ , tt*))
      → (p : Pos (const Unit*) {f = π} σ)
      → Face₀ π σ τ (SrcFrm n (π , σ , tt*) p) 

    int-face : {n : ℕ} (π : 𝒪 n)
      → (σ : Src (const Unit*) π)
      → (τ : Pd (const Unit*) (π , σ , tt*))
      → (p : Pos (const Unit*) {f = π , σ , tt*} τ)
      → Face₀ π σ τ (Frm⇒ (IncSrc π σ τ p .fst) (TgtFrm n (PdTyp (const Unit*) τ p)) ) 

  data Face₁ where

    tgt-face : {n : ℕ} (π : 𝒪 (suc n))
      → Face₁ n π (TgtFrm n π)

    src-face : {n : ℕ} (π : 𝒪 (suc n))
      → (p : Pos (const Unit*) {f = fst π} (π .snd .fst))
      → Face₁ n π (SrcFrm n π p) 

  TgtFrm zero π = tt*
  TgtFrm (suc n) ((π , σ , tt*) , τ , tt*) =
    Frm⇒ (IncTgt π σ τ) (∂Frm n (π , σ , tt*))  
  
  SrcFrm zero π tt* = tt*
  SrcFrm (suc n) ((π , σ , tt*) , τ , tt*) p =
    Frm⇒ (IncSrc π σ τ p) (∂Frm n (PdTyp (const Unit*) τ p))


  -- IncSrc : {n : ℕ} (π : 𝒪 n)
  --   → (σ : Src (const Unit*) π)
  --   → (τ : Pd (const Unit*) (π , σ , tt*))
  --   → (p : Pos (const Unit*) {f = π , σ , tt*} τ)
  --   → Repr₁ n (PdTyp (const Unit*) τ p) ⇒ Repr₀ (suc n) ((π , σ , tt*) , τ , tt*)
  IncSrc {zero} π σ τ p = tt* , (λ { (tgt-face ._) → {!!} ;
                                     (src-face ._ p) → {!!} })
  IncSrc {suc n} π σ τ p = {!!} , {!!}

  -- Inc : {n : ℕ} (π : 𝒪 n)
  --   → (σ : Src (const Unit*) π)
  --   → (τ : Pd (const Unit*) (π , σ , tt*))
  --   → {f : Frm (Repr₀ n (π , σ , tt*))}
  --   → Face₁ n (π , σ , tt*) f → Face₀ π σ τ f 
  Inc π σ τ (tgt-face (.π , .σ , .tt*)) = {!!}
  Inc π σ τ (src-face (.π , .σ , .tt*) p) = {!!}


  ∂Frm zero π = tt* , src-face {zero} arr tt* , tgt-face {zero} arr
  ∂Frm (suc n) ((π , σ , tt*) , τ , tt*) =
    Frm⇒ (IncTgt π σ τ) (∂Frm n (π , σ , tt*)) ,
    {!!} ,
    tgt-face {suc n} ((π , σ , tt*) , τ , tt*)


