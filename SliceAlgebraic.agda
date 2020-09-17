{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import SliceLemmas

module SliceAlgebraic where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    open SliceOver M M↓ 
    open import SliceAlg M M↓ 
    open import SliceAlg2 M M↓
    open import SliceAlg3 M M↓
    open import SliceAlg4 M M↓ 

    --
    --  The main theorem
    --

    slc-algebraic : is-algebraic Slc Slc↓
    slc-algebraic i c ν = has-level-in (ctr , unique) 

      where ctr : alg-comp Slc Slc↓ i c ν
            ctr = ⟦ slc-idx i c ν ∣ slc-cns i c ν ∣ λ= (slc-typ i c ν) ⟧

            unique : (α : alg-comp Slc Slc↓ i c ν) → ctr == α
            unique α = alg-comp-= Slc Slc↓ i c ν
                       (slc-idx-unique i c ν α)
                       (slc-cns-unique i c ν α)
                       (λ p → app=-β (slc-typ i c ν) p ∙ slc-typ-unique i c ν α p)

    -- Equivalence between algebraic compositions and indices
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

  --
  --  The opetopic type associated to an algebraic extension is fibrant
  --

  alg-is-fibrant : (M : 𝕄) (M↓ : 𝕄↓ M)
    → is-algebraic M M↓
    → is-fibrant (↓-to-OpType M M↓)
  base-fibrant (alg-is-fibrant M M↓ is-alg) =
    alg-mnd-has-unique-action M M↓ is-alg
  hom-fibrant (alg-is-fibrant M M↓ is-alg) =
    let open SliceOver M M↓ in 
      alg-is-fibrant Slc Slc↓ (slc-algebraic M M↓)

