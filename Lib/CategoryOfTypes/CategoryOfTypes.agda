{-# OPTIONS --no-positivity-check --no-termination-check #-}
--
--  Universe.agda - The opetopic type of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Core.OpetopicType
open import Core.OpetopicMap
open import Core.Universe

open import Lib.Structures
open import Lib.CategoryOfTypes.Lemmas
open import Lib.CategoryOfTypes.CompositeFibrant
open import Lib.CategoryOfTypes.Uniqueness

module Lib.CategoryOfTypes.CategoryOfTypes where

  𝒮ₙ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮π : (n : ℕ) (ℓ : Level) → 𝒮ₙ n ℓ ⇒ 𝕆U n ℓ

  𝒮ₙ zero ℓ = tt*
  𝒮ₙ (suc n) ℓ = 𝒮ₙ n ℓ , λ f →
    Σ[ C ∈ CellFib (Frm⇒ (𝒮π n ℓ) f) ]
    is-fib-rel C
  
  𝒮π zero ℓ = tt*
  𝒮π (suc n) ℓ = 𝒮π n ℓ , fst

  𝒮Ext : (n : ℕ) (ℓ : Level) → 𝕆Type∞ (𝒮ₙ n ℓ)
  Fill (𝒮Ext n ℓ) = snd (𝒮ₙ (suc n) ℓ)
  Hom (𝒮Ext n ℓ) = 𝒮Ext (suc n) ℓ

  𝒮ₙ-Src-to-U : ∀ {n ℓ} (F : Frm (𝒮ₙ n ℓ))
    → Src (snd (𝒮ₙ (suc n) ℓ)) F
    → USrc (Frm⇒ (𝒮π n ℓ) F)
  𝒮ₙ-Src-to-U {n} {ℓ} F S = Src⇒ {f = F} S (𝒮π n ℓ) (λ p → fst (S ⊚ p))

  𝒮ₙ-Src-is-fib : ∀ {n ℓ} (F : Frm (𝒮ₙ n ℓ))
    → (S : Src (snd (𝒮ₙ (suc n) ℓ)) F)
    → (p : Pos {X = 𝕆U n ℓ} CellFib (𝒮ₙ-Src-to-U F S)) → is-fib-rel (𝒮ₙ-Src-to-U F S ⊚ p)
  𝒮ₙ-Src-is-fib {n} {ℓ} F S p = snd (S ⊚ Pos⇐ S (𝒮π n ℓ) (λ q → fst (S ⊚ q)) p)  

  𝒮ₙ-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (3 + n) ℓ)
  𝒮ₙ-is-fibrant n ℓ F S = 
    ((ucomp S' ϕ , ucomp-is-fib-rel S' ϕ) ,
     (ufill S' ϕ , ufill-is-fib-rel S' ϕ)) ,
     λ hf → uhorn-filler-unique S' ϕ
              (fst (fst hf)) (snd (fst hf))
              (fst (snd hf)) (snd (snd hf))

    where S' : Src CellFib (Frm⇒ (𝒮π (suc n) ℓ) F)
          S' = 𝒮ₙ-Src-to-U F S

          ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S') → is-fib-rel (S' ⊚ p)
          ϕ = 𝒮ₙ-Src-is-fib F S 

  𝒮Ext-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant-ext (𝒮Ext (suc n) ℓ)
  fill-fib (𝒮Ext-is-fibrant n ℓ) = 𝒮ₙ-is-fibrant n ℓ 
  hom-fib (𝒮Ext-is-fibrant n ℓ) = 𝒮Ext-is-fibrant (suc n) ℓ

  𝒮 : (ℓ : Level) → ∞Cat (ℓ-suc ℓ)
  𝒮 ℓ = 𝒮Ext 0 ℓ , 𝒮Ext-is-fibrant 0 ℓ 


