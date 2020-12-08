{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import IdentityMonad
open import IdentityMonadOver
open import InftyGroupoid
open import FundamentalThm
open import MonadEqv 

module Uniqueness where

  postulate

    -- Right, so this is what we have to prove.
    uniqueness : (X : ∞Groupoid)
      → X == to-∞Groupoid (Ob (fst X) ttᵢ)

    IdeMnd : (M : 𝕄) → M ≃ₘ M

    from-eqv : (M : 𝕄) (P Q : Idx M → Set)
      → (i : Idx M) → P i ≃ Q i
      → P ≃[ Idx≃ (IdeMnd M) ] Q 
      
    FamEqv : (M : 𝕄) (P : Idx M → Set)
      → P ≃[ Idx≃ (IdeMnd M) ] P

  open _≃ₒ_

  open import SliceUnfold


  framework : (M : 𝕄) (M↓ : 𝕄↓ M) 
    → (is-alg : is-algebraic M M↓)
    → (X : OpetopicType M)
    → (is-fib : is-fibrant X)
    → (eqv : (i : Idx M) → Idx↓ M↓ i ≃ Ob X i)
    → (extreme : (i : Idx M) (c : Cns M i)
                 → (ν : (p : Pos M c) → Ob X (Typ M c p))
                 → Ob (Hom X) ((i , –> (eqv i) (idx (contr-center (is-alg i c (λ p → <– (eqv (Typ M c p)) (ν p)))))) , c , ν))
    → ↓-to-OpType M M↓ ≃ₒ X 
  Ob≃ (framework M M↓ is-alg X is-fib eqv extreme) = eqv
  Hom≃ (framework M M↓ is-alg X is-fib eqv extreme) =
    framework ExtSlc₁ ExtSlc↓₁ {!!}
      (op-transp (Slice≃ (Pb≃' eqv)) (Hom X)) {!!}
      next-eqv  -- So, this equivalence will be the generically
                -- constucted one which operates by simply using the
                -- fibrancy assert that the fillings are the same
                -- since they are both giving the same multiplication.
                
      {!!}      -- And now we are being asked to show that the next level
                -- hom witnesses the composition of relations *under* the
                -- identification we have just given.

      where open ExtUnfold M M↓ 

            next-eqv : (i : Idxₛ (Pb M ↓Rel₀)) →
                       Idx↓ₛ (Pb↓ M↓ ↓Rel₀ (λ i₁ → _==_)) i ≃
                       Ob (Hom X) (fst (Idx≃ (Slice≃ (Pb≃' {M = M} eqv))) i)
            next-eqv i = {!!} 

            next-eqv-to : (i : Idxₛ (Pb M ↓Rel₀)) →
                       Idx↓ₛ (Pb↓ M↓ ↓Rel₀ (λ i₁ → _==_)) i → 
                       Ob (Hom X) (fst (Idx≃ (Slice≃ (Pb≃' {M = M} eqv))) i)
            next-eqv-to ((i , j) , (c , ν)) ((.j , idp) , (d , typ-d=ν)) = {!!} 


  -- This actually looks kind of reasonable.  It seems that "extreme" in
  -- the case where we actually instantiate with the identity monad
  -- and, say, the identity equivalence with some base type will then
  -- ask exactly for a reflexivity relation.

  -- Okay.  So this looks like it has all the essential ideas of what
  -- you have been describing.  We end up in a situation, as you would
  -- have expected, where we are attempting to show this equivalence
  -- but *with respect to a chosen identification of the constructors*.

  -- So, in the analogy, we have
  --
  --   Ob X              --->  Q
  --   Ob (Hom X)        --->  R
  --   Ob (Hom (Hom X))  --->  T
  --
  -- Does this seem right?
  --
  -- I think so.  Hmmm.  Or I'm not sure.  Somehow the idea was to
  -- prove the *previous* obligation using the next.  Whereas here
  -- you're having to prove the next for T.  But I feel like it's
  -- at least in some sense some progress...
  -- 
