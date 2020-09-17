{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import MonadEqv

module Algebras where

  ↓-to-OpType : (M : 𝕄) (M↓ : 𝕄↓ M)
    → OpetopicType M
  Ob (↓-to-OpType M M↓) = Idx↓ M↓ 
  Hom (↓-to-OpType M M↓) =
    ↓-to-OpType (Slice (Pb M (Idx↓ M↓)))
                       (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)))

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    record alg-comp (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) : Set where
      constructor ⟦_∣_∣_⟧
      field
        idx : Idx↓ M↓ i 
        cns : Cns↓ M↓ idx c
        typ : Typ↓ M↓ cns == ν

    is-algebraic : Set
    is-algebraic = (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (alg-comp i c ν) 
    
    open alg-comp public

    alg-comp-= : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j j' : Idx↓ M↓ i} (m : j == j')
      → {d : Cns↓ M↓ j c} {d' : Cns↓ M↓ j' c}
      → (n : d == d' [ (λ x → Cns↓ M↓ x c) ↓ m ])
      → {r : Typ↓ M↓ d == ν} {r' : Typ↓ M↓ d' == ν}
      → (ϕ : (p : Pos M c) → app= r p == ap (λ x → Typ↓ M↓ (snd x) p) (pair= m n) ∙ app= r' p)
      → ⟦ j ∣ d ∣ r ⟧ == ⟦ j' ∣ d' ∣ r' ⟧
    alg-comp-= i c ν {j = j} idp {d = d} idp {r} {r'} ϕ =
      ap (λ x → ⟦ j ∣ d ∣ x ⟧) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r'))


  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    Plbk : 𝕄
    Plbk = Pb M (Idx↓ M↓)

    Plbk↓ : 𝕄↓ Plbk
    Plbk↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)
    
    Slc : 𝕄
    Slc = Slice Plbk

    Slc↓ : 𝕄↓ Slc
    Slc↓ = Slice↓ Plbk↓

    postulate

      slc-algebraic : is-algebraic Slc Slc↓
    
    alg-to-idx↓ : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → alg-comp M M↓ i c ν ≃ Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν)))
    alg-to-idx↓ i c ν = equiv to from to-from from-to

      where to : alg-comp M M↓ i c ν → Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν)))
            to ⟦ j ∣ d ∣ τ ⟧ = j , (j , idp) , d , app= τ

            from : Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν))) → alg-comp M M↓ i c ν
            from (j , (.j , idp) , d , τ) = ⟦ j ∣ d ∣ λ= τ ⟧

            to-from : (x : Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν))))
              → to (from x) == x
            to-from (j , (.j , idp) , d , τ) =
              ap (λ x → j , (j , idp) , d , x) (λ= (λ p → app=-β τ p))

            from-to : (x : alg-comp M M↓ i c ν)
              → from (to x) == x
            from-to ⟦ j ∣ d ∣ τ ⟧ = ap (λ x → ⟦ j ∣ d ∣ x ⟧) (! (λ=-η τ)) 
            
    alg-mnd-has-unique-action : is-algebraic M M↓
      → unique-action M (Idx↓ M↓) (Idx↓ Slc↓) 
    alg-mnd-has-unique-action is-alg i c ν =
      equiv-preserves-level (alg-to-idx↓ i c ν) ⦃ is-alg i c ν ⦄ 

  alg-is-fibrant : (M : 𝕄) (M↓ : 𝕄↓ M)
    → is-algebraic M M↓
    → is-fibrant (↓-to-OpType M M↓)
  base-fibrant (alg-is-fibrant M M↓ is-alg) =
    alg-mnd-has-unique-action M M↓ is-alg
  hom-fibrant (alg-is-fibrant M M↓ is-alg) =
    alg-is-fibrant (Slc M M↓) (Slc↓ M M↓) (slc-algebraic M M↓)

  --
  --  Uniqueness
  --

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓)
    (N : 𝕄) (X : OpetopicType N) (is-fib : is-fibrant X)
    (e : M ≃ₘ N) (E : Idx↓ M↓ ≃[ Idx≃ e ] Ob X)
    where

    -- Hmmm.  But this doesn't seem like quite enough.  We have that
    -- their carrier sets are the same.  But not that the
    -- multiplicative structures are the same.  I see.  So I think we
    -- should *also* need that the Hom's of X are equivalent to the
    -- constructors over of the algebra.  This will say that they
    -- share the same multiplicative structure.

    -- From here, the claim would have to be that the next level,
    -- i.e. Ob (Hom (Hom X)) is determined.  Does this actually seem
    -- plausible?  Dunno .....

    slc-eqv : Slc M M↓ ≃ₘ Slice (Pb N (Ob X))
    slc-eqv = Slice≃ (Pb≃ e E) 

    slc-Eqv : Idx↓ (Slc↓ M M↓) ≃[ Idx≃ slc-eqv ] Ob (Hom X)
    slc-Eqv ((i , j) , (c , ν)) = result 

      where result : Σ (Σ (Idx↓ M↓ i) (λ j₁ → j₁ == j)) (λ i↓ → Σ (Cns↓ M↓ (fst i↓) c) (λ d → (p : Pos M c) → Typ↓ M↓ d p == ν p)) ≃
                     Ob (Hom X) (fst (Idx≃ slc-eqv) ((i , j) , c , ν))
            result = {!!} 

    -- Yeah, it seems like we will need at least two levels.  And then
    -- what's going to happen?  So you can picture the setup: you have
    -- a chain of algebra like multiplications.  And on the other side
    -- you have this decoration.  Now, by fibrancy, you know there is
    -- a unique composite on the X side.  And by the slice-algebraic
    -- theorem, so too on the monad side.  By FTHTT, it follows that
    -- the fillers are an equality type for the multiplication
    -- operation on the two sides.  So it looks like we just need to
    -- show that the identification of constructors is a kind of
    -- homomorphism or something, and we should be okay.
