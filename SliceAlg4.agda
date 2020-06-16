{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Lemmas
open import Algebras

module SliceAlg4 (M : 𝕄) (M↓ : 𝕄↓ M) where

  open SliceOver M M↓ 
  open import SliceAlg M M↓ 
  open import SliceAlg2 M M↓
  open import SliceAlg3 M M↓

  slc-typ-unique : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → (α : alg-comp Slc Slc↓ i σ ϕ)
    → (p : Pos Slc σ)
    → slc-typ i σ ϕ p == ap (λ x → Typ↓ Slc↓ (snd x) p) (pair= (slc-idx-unique i σ ϕ α) (slc-cns-unique i σ ϕ α)) ∙ (app= (typ α) p)
  slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ (inl unit) = 
    let open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open CnsUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open IdxIh i j c ν δ ε ϕ
        open CnsIh i j c ν δ ε ϕ
        open Helpers i j c ν δ ε d' typ-d'=ν
    in slc-typ-cst (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ ε↓' ε↓ (λ= δ↓'=δ↓)
         (λ=ε↓ (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓ ε↓' ε↓ ε↓'=ε↓) 

  slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ (inr (p , q)) = {!!}

