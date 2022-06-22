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

module Experimental.NoDecs.Opetopes where


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
  --  An Induction Principle
  --

  record IndData {ℓ} (P : (n : ℕ) (π : 𝒪 n) → Type ℓ) : Type ℓ where
    field
      obj* : P 0 tt*
      arr* : P 1 (tt* , tt* , tt*)
      glob* : {n : ℕ} (π : 𝒪 n) → P (suc (suc n)) ((π , _ , tt*) , lf tt* , tt*)
      ngon* : (χ : Pd (const Unit*) arr) → P 2 (arr , nd tt* [ tt* , tt* , χ ] tt* , tt*)
      glob-on-drop* : {n : ℕ} (π : 𝒪 n) → P (3 + n) (((π , _ , tt*) , lf tt* , tt*) , nd tt* (lf tt*) tt* , tt*)
      -- root-exposed* : {n : ℕ} (π : 𝒪 n) (hbrs : Src (Branch {X = 𝕋 n} {P = snd (𝕋 (suc n))} (Branch {X = 𝕋 (suc n)} {P = snd (𝕋 (suc (suc n)))} (const Unit*))) π)
      --   → P (3 + n) (((π , _ , tt*) , _ , tt*) ,  nd tt* (nd tt* hbrs [ tt* , η (snd (fst (𝕋 (suc (suc (suc n)))))) tt* , lf tt* ]) tt* , tt*)

      climbing* : {n : ℕ} (π : 𝒪 n) (hbrs : Src (Branch {X = 𝕋 n} {P = snd (𝕋 (suc n))} (Branch {X = 𝕋 (suc n)} {P = snd (𝕋 (suc (suc n)))} (const Unit*))) π)
        → (brs : Pd (Branch {X = 𝕋 (suc n)} {P = snd (𝕋 (suc (suc n)))} (const Unit*)) (π , μ (id-map (𝕋 n)) (Branch (Branch (const Unit*)))
                                                  (const Unit*) hbrs (λ p → η (const Unit*) {f = (Typ (Branch (Branch (const Unit*))) hbrs p)} (stm (hbrs ⊚ p))) , tt*))
        → (glue : P (3 + n) (((π , μ (id-map (𝕋 n)) (Branch (Branch (const Unit*))) (const Unit*) hbrs
                         (λ p → η (const Unit*) {f = (Typ (Branch (Branch (const Unit*))) hbrs p)} (stm (hbrs ⊚ p))) , tt*) , _ , tt*) , nd tt* {!!} tt* , tt*))
        → P (3 + n) (((π , _ , tt*) , _ , tt*) , nd tt* (nd tt* hbrs [ tt* , _  , nd tt* brs tt* ]) tt* , tt*)                                                       


-- Pd (Branch (λ _ → Lift Unit)) (π , _fst_473 , tt*)

  open IndData

  -- Can you say exactly what is the point of this principle?  I mean,
  -- I guess it's just a way of avoiding (but we'll see about this)
  -- direct interaction with μ , η , γ.  It expresses the opetopes
  -- entirely in terms of some combinators on previous shapes...

  -- Yeah, so I guess what this is actually doing is exposing enough
  -- of the structure so that you only have to show compatibility of
  -- your induction hypothesis with γ in one particular case.
  -- Compatibility with η and μ is taken care of by exposing the
  -- cases correctly.

  opetopic-induction : ∀ {ℓ} (P : (n : ℕ) (π : 𝒪 n) → Type ℓ)
    → (ihs : IndData P)
    → (n : ℕ) (π : 𝒪 n) → P n π
  opetopic-induction P ihs zero π = obj* ihs
  opetopic-induction P ihs (suc zero) (tt* , tt* , tt*) = arr* ihs
  opetopic-induction P ihs (suc (suc n)) ((π , ._ , tt*) , lf .tt* , tt*) = glob* ihs π
  opetopic-induction P ihs (suc (suc zero)) ((tt* , ._ , tt*) , nd .tt* [ tt* , tt* , χ ] tt* , tt*) = ngon* ihs χ
  opetopic-induction P ihs (suc (suc (suc n))) ((._ , ._ , tt*) , nd .tt* (lf {π} tt*) tt* , tt*) = glob-on-drop* ihs π
  opetopic-induction P ihs (suc (suc (suc n))) ((._ , ._ , tt*) , nd .tt* (nd {π} tt* hbrs [ tt* , ._ , lf .tt* ]) tt* , tt*) = {!hbrs!}
  -- opetopic-induction P ihs (suc (suc (suc n))) ((._ , ._ , tt*) , nd .tt* (nd {π} tt* hbrs [ tt* , ._ , nd .tt* brs tt* ]) tt* , tt*) = {!!}
  opetopic-induction P ihs (suc (suc (suc zero))) ((._ , ._ , tt*) , nd .tt* (nd {π} tt* hbrs [ tt* , ._ , nd .tt* brs tt* ]) tt* , tt*) = {!hbrs!}
  opetopic-induction P ihs (suc (suc (suc (suc n)))) ((._ , ._ , tt*) , nd .tt* (nd {π} tt* hbrs [ tt* , ._ , nd .tt* brs tt* ]) tt* , tt*) = {!hbrs!}


  -- Okay, I think I see.  There's one more case: it's the case where
  -- the root box in codim 2 is a loop.  After this, I feel like you
  -- will have exposed enough that you can just directly graft.

  -- So I can't actually match any more.  Hmm.  But does that mean
  -- there is an upper limit to what you can match on for opetopes?
  -- That woule be surprising, right?

  -- -- Dimension 1
  -- max-frm zero π = tt*

  -- -- Drops (this case is generic. do it first for better computation)
  -- max-frm (suc n) ((π , ._ , tt*) , lf .tt* , tt*) =
  --   max-frm n (π , _ , tt*) ,
  --   (η _ {f = max-frm n (π , _ , tt*)} (lf-cell π)) ,
  --   (lf-cell π)

  -- -- Dimension 2 - ngons for n > 0
  -- max-frm (suc zero) ((π , ._ , tt*) , nd .tt* vbr tt* , tt*) = 
  --   tt* , nd-cell-there tt* vbr tt* (max-frm (suc zero) (_ , br vbr , tt*) .snd .fst) ,
  --         nd-cell-here tt* vbr

  -- -- Globs on Drops
  -- max-frm (suc (suc n)) ((._ , ._ , tt*) , nd .tt* (lf tt*) tt* , tt*) =
  --   _ , lf (lf-cell _) , (nd-cell-here _ (lf tt*))

  -- -- Dimension ≥ 3 - root of source tree is external
  -- max-frm (suc (suc n)) ((._ , ._ , tt*) , nd .tt* (nd tt* hbrs [ tt* , ._ , lf .tt* ]) tt* , tt*) =
  --   {!!} , {!!} , {!!}
  
  -- -- Dimension ≥ 3 - climbing the root box
  -- max-frm (suc (suc n)) ((._ , ._ , tt*) , nd .tt* (nd tt* hbrs [ tt* , ._ , nd .tt* brs tt* ]) tt* , tt*) = {!!}
