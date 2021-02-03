{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Algebricity
open import SliceAlgebraic

module InftyGroupoid where

  ∞Groupoid : Set₁
  ∞Groupoid = Σ (OpetopicType IdMnd) (is-fibrant)

  ∞grp-carrier : ∞Groupoid → Set  
  ∞grp-carrier (X , is-fib) = Ob X ttᵢ 

  module _ (A : Set) where

    open import IdentityMonadOver A

    -- Some weird reduction with the indices of the identity forces
    -- these two lemmas to be separated out.  A bit fishy, but it works.
    dec-is-typ : (ν : (p : Posᵢ {ttᵢ} ttᵢ) → Idx↓ᵢ ttᵢ)
      → (p : Posᵢ {u = ttᵢ} ttᵢ)
      → Typ↓ IdMnd↓ {i = ttᵢ} {c = ttᵢ} {i↓ = ν ttᵢ} ttᵢ p == ν p
    dec-is-typ ν ttᵢ = idp {a = ν ttᵢ}

    dec-is-typ-is-idp : (ν : (p : Posᵢ {ttᵢ} ttᵢ) → Idx↓ᵢ ttᵢ) (a : A)
      → (p : Posᵢ {u = ttᵢ} ttᵢ) 
      →  app= (λ= (dec-is-typ (Typ↓ IdMnd↓ {i = ttᵢ} {c = ttᵢ} {i↓ = a} ttᵢ))) p == idp {a = a}
    dec-is-typ-is-idp ν a ttᵢ = app=-β (dec-is-typ (Typ↓ IdMnd↓ {i = ttᵢ} {c = ttᵢ} {i↓ = a} ttᵢ)) ttᵢ

    id-is-algebraic : is-algebraic IdMnd IdMnd↓
    id-is-algebraic ttᵢ ttᵢ ν = has-level-in (ctr , unique)

      where ctr : alg-comp IdMnd IdMnd↓ ttᵢ ttᵢ ν
            ctr = ⟦ ν ttᵢ ∣ ttᵢ ∣ λ= (dec-is-typ ν) ⟧  

            unique : (α : alg-comp IdMnd IdMnd↓ ttᵢ ttᵢ ν) → ctr == α
            unique ⟦ a ∣ ttᵢ ∣ idp ⟧ = alg-comp-= IdMnd IdMnd↓ ttᵢ ttᵢ ν idp idp
              (dec-is-typ-is-idp ν a) 

    IdOpType : OpetopicType IdMnd
    IdOpType = ↓-to-OpType IdMnd IdMnd↓

    IdOpType-is-fibrant : is-fibrant IdOpType
    IdOpType-is-fibrant = alg-is-fibrant IdMnd IdMnd↓ id-is-algebraic

  to-∞Groupoid : Set → ∞Groupoid
  to-∞Groupoid A = IdOpType A ,
    IdOpType-is-fibrant A


  
