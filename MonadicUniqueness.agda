{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import IdentityMonad
open import IdentityMonadOver

module MonadicUniqueness (A : Set) where

  open import SliceUnfold IdMnd (IdMnd↓ A)

  module _ (R : Rel₂) (is-fib-R : unique-action Slc₁ (Idx↓ Slc↓₁) R) 
           (T : Rel₃) (is-fib-T : unique-action Slc₂ (Idx↓ Slc↓₂) T) where

    -- Okay, so is it now true that I can prove R is composition?

    postulate
    
      slc-idx : (i : Idx Slc₁) (σ : Cns Slc₁ i)
        → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
        → Idx↓ Slc↓₁ i

      slc-cns : (i : Idx Slc₁) (σ : Cns Slc₁ i)
        → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
        → Cns↓ Slc↓₁ (slc-idx i σ ϕ) σ

      slc-typ : (i : Idx Slc₁) (σ : Cns Slc₁ i)
        → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
        → (p : Pos Slc₁ σ)
        → Typ↓ Slc↓₁ (slc-cns i σ ϕ) p == ϕ p 

    -- Exactly.  So this is the general version, which specializes to exactly
    -- the case for leaf and node that you would have unfolded below.
    R-is-slc : (i : Idx Slc₁) (σ : Cns Slc₁ i)
      → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
      → R ((i , slc-idx i σ ϕ) , (σ , ϕ)) 
    R-is-slc i σ ϕ = {!!} 

    R-fib-gives : (i : Idx Slc₁) (c : Cns Slc₁ i)
      → (ν : (p : Pos Slc₁ c) → (Idx↓ Slc↓₁) (Typ Slc₁ c p))
      → Σ (Idx↓ Slc↓₁ i) (λ i↓ → R ((i , i↓) , c , ν))
    R-fib-gives i c ν = contr-center (is-fib-R i c ν) 

    R-fib-gives' : (i : Idx Slc₁)
      → (ω : Cns Slc₁ i)
      → (θ : (p : Pos Slc₁ ω) → (Idx↓ Slc↓₁) (Typ Slc₁ ω p))
      → Σ (Idx↓ Slc↓₁ i) (λ i↓ → R ((i , i↓) , ω , θ))
    R-fib-gives' i ω θ = contr-center (is-fib-R i ω θ) 

    R-fib-gives'' : (i : Idxᵢ) (a₀ : A) (c : Cnsᵢ i) (ν : (p : Posᵢ {u = i} c) → A)
      → (ω : Cns Slc₁ ((i , a₀) , c , ν))
      → (θ : (p : Pos Slc₁ ω) → (Idx↓ Slc↓₁) (Typ Slc₁ ω p))
      → Σ (Idx↓ Slc↓₁ ((i , a₀) , c , ν)) (λ i↓ → R ((((i , a₀) , c , ν) , i↓) , ω , θ))
    R-fib-gives'' i a₀ c ν ω θ = contr-center (is-fib-R ((i , a₀) , c , ν) ω θ) 

    -- Right.  This seems totally clear.  So it's definitely not contractible.
    -- So how do I know that, when applying the above to a leaf, I get the right thing?
    slice-fib : (i : Idxᵢ) (a₀ : A) (c : Cnsᵢ i) (ν : (p : Posᵢ {u = i} c) → A)
      → Idx↓ Slc↓₁ ((i , a₀) , c , ν) ≃ (a₀ == ν ttᵢ)
    slice-fib i a₀ c ν = {!!}

    our-index : (a : A) → Idx↓ Slc↓₁ ((ttᵢ , a) , ttᵢ , cst a)
    our-index a = fst (R-fib-gives'' ttᵢ a ttᵢ (cst a) (lf (ttᵢ , a)) ⊥-elim)

    we-have : (a : A) → R ((((ttᵢ , a) , ttᵢ , cst a) , our-index a) , lf (ttᵢ , a) , ⊥-elim)
    we-have a = snd (R-fib-gives'' ttᵢ a ttᵢ (cst a) (lf (ttᵢ , a)) ⊥-elim) 

    we-want : (a : A) → R ((((ttᵢ , a) , ttᵢ , cst a) , (a , idp) , (ttᵢ , cst idp)) , lf (ttᵢ , a) , ⊥-elim)
    we-want a = {!!} 

    -- So.  This seems to be the crux of the problem.  R gives us back a loop on
    -- a in this case.  But where does the null-homotopy come from? 

    -- In this setup, there is nothing more to add to the hypotheses, right?
    -- There's no previous step, nothing like that.  There's only R and what
    -- it gives us.

    -- So the only thing which seems to make sense is that we are going to use
    -- the fundamental theorem to produce a possible non-trivial equivalence
    -- which will "fix" R so that what it thinks is the unit actually becomes
    -- the unit.

    -- Or can you somehow "compose" R with the inverse loop and get a
    -- null homotopy?  In any case, this is clearly where you have to
    -- confront the problem and find a solution.

    -- But you can probably inspect this at the level of the
    -- fundamental theorem: basically, I'm going to get a map sending
    -- one unit to the other, right?  But how does this help?

    -- Okay.  So the above I think gives the idea: the unit element
    -- is forced to be idempotent.  And in an identity type, this
    -- forces it to be the identity.  And that's going to use the
    -- fibrancy in the next dimension.  Okay.  Nice.

    to : (i : Idx Slc₂) → CanonRel₂ i → R i
    to ((((i , a₀) , c , ν) , (a₁ , p) , c↓ , typ-c↓=ν) , ω , θ) ((._ , idp) , ω↓ , θ↓) = {!ν!}
    -- to ((((i , a₀) , ._ , ._) , (a₁ , p) , ._ , ._) , ._ , θ) ((._ , idp) , lf↓ (.a₁ , .p) , θ↓) = {!i!}
    -- to ((((i , a₀) , ._ , ._) , (a₁ , p) , ._ , ._) , ._ , θ) ((._ , idp) , nd↓ (c↓ , ν↓) δ↓ ε↓ , θ↓) = {!!}

    -- So, to prove that R is composition is to prove the following:
    thm : (i : Idx Slc₂) → R i ≃ CanonRel₂ i
    thm ((((i , a₀) , c , ν) , (a₁ , p) , c↓ , typ-c↓=ν) , ω , θ) = {!!} 

    
