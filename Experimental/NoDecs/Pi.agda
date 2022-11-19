--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.CartesianProduct
open import Experimental.NoDecs.Universe

module Experimental.NoDecs.Pi where

  {-# TERMINATING #-}
  Πₒ : ∀ {n ℓ} (A : 𝕆Type n ℓ) (B : A ⇒ 𝕆U n ℓ) → 𝕆Type n ℓ

  evₒ : ∀ {n ℓ} (A : 𝕆Type n ℓ) (B : A ⇒ 𝕆U n ℓ)
    → prod A (Πₒ A B) ⇒ 𝕆V n ℓ 

  ev≡ : ∀ {n ℓ} (A : 𝕆Type n ℓ) (B : A ⇒ 𝕆U n ℓ)
    → 𝕆π n ℓ ⊙ evₒ A B ≡ B ⊙ Fst

  Πₒ {zero} A B = tt*
  Πₒ {suc n} (A , A') (B , B') = Πₒ A B , λ f →
      (f' : Frm (prod A (Πₒ A B))) (e : Frm⇒ Snd f' ≡ f)
      (a : A' (Frm⇒ Fst f'))
    → B' a (Frm⇒ (evₒ A B) f') (λ i → Frm⇒ (ev≡ A B i) f')

  evₒ {zero} A B = tt*
  evₒ {suc n} (A , A') (B , B') =
    evₒ A B , λ { {f} (a ∣ σ) → (λ f' e → B' a (Frm⇒ (evₒ A B) f) λ i → Frm⇒ (ev≡ A B i) f) ,
                                σ f refl a }

  ev≡ {zero} A B = refl
  ev≡ {suc n} (A , A') (B , B') i =
    ev≡ A B i , λ { {f} (a ∣ σ) → λ f' e → B' a {!e i!} {!!} } 




