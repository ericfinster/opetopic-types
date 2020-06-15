{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Algebras

module InftyGroupoid where

  ∞Groupoid : Set₁
  ∞Groupoid = Σ (OpetopicType IdMnd) (is-fibrant)

  underlying : ∞Groupoid → Set  
  underlying (X , is-fib) = Ob X ttᵢ 

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

    X : OpetopicType M
    X = OverToOpetopicType M M↓

    alg-mnd-has-unique-action : is-algebraic M M↓
      → unique-action M (Ob X) (Ob (Hom X))
    alg-mnd-has-unique-action is-alg i c ν = {!is-alg i c ν !} 

    alg-is-fibrant : is-algebraic M M↓ → is-fibrant X
    base-fibrant (alg-is-fibrant is-alg) = alg-mnd-has-unique-action is-alg
    hom-fibrant (alg-is-fibrant is-alg) = {!slc-algebraic!}

  module _ (A : Set) where

    open import IdentityMonadOver A

    id-is-algebraic : is-algebraic IdMnd IdMnd↓
    id-is-algebraic ttᵢ ttᵢ ν = has-level-in (ctr , ctr-unique)

      where ctr : Σ A (λ a → Σ ⊤ᵢ (λ u → Typ↓ IdMnd↓ {f↓ = a} u == ν))
            ctr = ν ttᵢ , ttᵢ , λ= (λ { ttᵢ → idp })

            ctr-unique : (x : Σ A (λ a → Σ ⊤ᵢ (λ u → Typ↓ IdMnd↓ {f↓ = a} u == ν))) → ctr == x
            ctr-unique (a , ttᵢ , idp) = {!!}

    XA : OpetopicType IdMnd
    XA = OverToOpetopicType IdMnd IdMnd↓ 

    XA-is-fibrant : is-fibrant XA
    XA-is-fibrant = alg-is-fibrant IdMnd IdMnd↓ id-is-algebraic 

    _==ₒ_ : A → A → Set
    a₀ ==ₒ a₁ = Ob (Hom XA) ((ttᵢ , a₀) , (ttᵢ , (λ { ttᵢ → a₁ }))) 

    claim : {a₀ a₁ : A} → (a₀ == a₁) ≃ (a₀ ==ₒ a₁)
    claim = {!!} 


  to-∞Groupoid : Set → ∞Groupoid
  to-∞Groupoid A = XA A  , XA-is-fibrant A

