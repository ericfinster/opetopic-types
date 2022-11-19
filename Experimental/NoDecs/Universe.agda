{-# OPTIONS --no-positivity-check #-}
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

module Experimental.NoDecs.Universe where

  -- The universe can actually be define just using maps ...
  𝕆U : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝕆V : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝕆π : (n : ℕ) (ℓ : Level) → 𝕆V n ℓ ⇒ 𝕆U n ℓ

  Frm↓ : ∀ {n ℓ} → Frm (𝕆U n ℓ) → Type (ℓ-suc ℓ)
  Frm↓ {n} {ℓ} F = fiber (Frm⇒ (𝕆π n ℓ)) F

  OpRel : ∀ {n ℓ} → Frm (𝕆U n ℓ) → Type (ℓ-suc ℓ)
  OpRel {n} {ℓ} F = Frm↓ F → Type ℓ 

  OpEl : ∀ {n ℓ} → Frm (𝕆V n ℓ) → Type (ℓ-suc ℓ)
  OpEl {n} {ℓ} f = Σ[ P ∈ OpRel (Frm⇒ (𝕆π n ℓ) f) ] P (f , refl)

  𝕆U zero ℓ = tt*
  𝕆U (suc n) ℓ = 𝕆U n ℓ , OpRel
  
  𝕆V zero ℓ = tt*
  𝕆V (suc n) ℓ = 𝕆V n ℓ , OpEl 

  𝕆π zero ℓ = tt*
  𝕆π (suc n) ℓ = 𝕆π n ℓ , fst
  
  -- The fibrant universe.

  Src↓ : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src OpRel F)
    → (f : Frm↓ F) → Type (ℓ-suc ℓ)
  Src↓ {n} {ℓ} S f = Σ[ s ∈ Src OpEl (fst f) ]
                     PathP (λ i → Src OpRel (snd f i))
                       (Src⇒ (𝕆π n ℓ) OpEl OpRel fst s) S

  El↓ : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (T : OpRel F)
    → (f : Frm↓ F) → Type (ℓ-suc ℓ)
  El↓ T f = Σ[ e ∈ OpEl (fst f) ] 
            PathP (λ i → OpRel (snd f i))
              (fst e) T

  mkFrm↓ : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)}
    → {S : Src OpRel F} {T : OpRel F}
    → (f : Frm↓ F) (s : Src↓ S f) (t : El↓ T f)
    → Frm↓ (F , S , T)
  mkFrm↓ f s t = (fst f , fst s , fst t) ,
               λ i → snd f i , snd s i , snd t i

  is-fib-family : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)}
    → OpRel F → Type (ℓ-suc ℓ)
  is-fib-family {zero} {ℓ} {F} C = Unit*
  is-fib-family {suc n} {ℓ} {F , S , T} C = 
    {f : Frm↓ F} (s : Src↓ S f)
      → isContr (Σ[ t ∈ El↓ T f ] C (mkFrm↓ f s t))



  
