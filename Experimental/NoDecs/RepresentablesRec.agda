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

module Experimental.NoDecs.RepresentablesRec where

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

  Repr₀ : (n : ℕ) → 𝒪 (suc n) → 𝕆Type n ℓ-zero
  Repr₁ : (n : ℕ) (π : 𝒪 (suc n)) → Frm (Repr₀ n π) → Type

  max-frm : (n : ℕ) (π : 𝒪 (suc n)) → Frm (Repr₀ n π)
  max-pd : (n : ℕ) (π : 𝒪 (suc n)) → Src (Repr₁ n π) (max-frm n π)

  data Face₀ : {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    → Frm (Repr₀ n (π , σ , tt*)) → Type where

    lf-cell : {n : ℕ} (π : 𝒪 n)
      → Face₀ π (η (const Unit*) {f = π} tt*) (lf tt*)
          (max-frm n (π , η (const Unit*) {f = π} tt* , tt*))

    nd-cell : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
      → Face₀ π (canopy π brs) (nd tt* brs tt*)
          (max-frm n (π , canopy π brs , tt*))

  Repr₀ zero _ = tt*
  Repr₀ (suc n) ((π , σ , tt*) , τ , tt*) =
    Repr₀ n (π , σ , tt*) , Face₀ π σ τ 

  data Face₁ : {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    → Frm (Repr₀ n (π , σ , tt*) , Face₀ π σ τ) → Type where

    nd-cell : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
      → Face₁ π (canopy π brs) (nd tt* brs tt*)
              ((max-frm n (π , canopy π brs , tt*)) ,
                {!max-pd n (π , canopy π brs , tt*)!} ,
                (nd-cell π brs))

    tgt-cell : {n : ℕ} (π : 𝒪 n) (σ : Src (const Unit*) π) (τ : Pd (const Unit*) (π , σ , tt*))
      → Face₁ π σ τ (max-frm (suc n) ((π , σ , tt*) , τ , tt*)) 

  Repr₁ zero π _ = Unit ⊎ Unit
  Repr₁ (suc n) ((π , σ , tt*) , τ , tt*) = Face₁ π σ τ

  max-frm zero π = tt*
  max-frm (suc n) ((π , ._ , tt*) , lf .tt* , tt*) =
    max-frm n (π , η (const Unit*) {f = π} tt* , tt*) ,
      η (Face₀ π (η (const Unit*) {f = π} tt*) (lf tt*)) (lf-cell π) ,
        lf-cell π
  max-frm (suc n) ((π , ._ , tt*) , nd .tt* brs tt* , tt*) =
    max-frm n (π , canopy π brs , tt*) ,
      μ (id-map (Repr₀ n (π , canopy π brs , tt*))) _ _
        {f = (max-frm n (π , canopy π brs , tt*))}
          (max-pd n (π , canopy π brs , tt*)) (λ p → {!max-frm (suc n)!})  ,
        nd-cell π brs

  -- So the difficulty now is how to cnnect max pd and brs in order to
  -- be able to use the induction hypothesis.  This suggests that you also
  -- need to know that the underlying shape of the representable is the
  -- opetope it represents....

  -- although I would find that annoying.... any other possibility?
  
    where IH : (p : Pos (Branch (const Unit*)) {f = π} brs) → Frm (Repr₀ (suc n) ((Typ (Branch (const Unit*)) brs p , (lvs (brs ⊚ p)) , tt*) , br (brs ⊚ p) , tt*))
          IH p = max-frm (suc n) ((Typ (Branch (const Unit*)) brs p , (lvs (brs ⊚ p)) , tt*) , br (brs ⊚ p) , tt*)  

  max-pd n π = {!!} 


    -- okay. but how to glue them all together ?
    -- oh, you should also have the "local" induction hypothesis for this node, yeah?
    -- well, yeah, but this is a different dimension.  it's the whole boundary of that
    -- guy, not just the codim 2 part.

    -- Well, okay, but at this point it's pretty clear what you need:
    -- you have to look at the local picture corresponding to this
    -- element at look at tis full representable (or, at least, the
    -- source of it).  And you'll need a map from that guy to this one
    -- so that you can substitute along it.

    -- The only tricky things is that it then seems if you want the
    -- gluing to be type correct that you will need to know that the
    -- image of the frame of this representable is exactly max-frm.
    -- Which means it should somehow be defined that way in order that
    -- everything commute.

    -- I mean, okay.  This is certainly progress because at least now
    -- I see how the proof goes, even if it is going to need some
    -- reorganization.
