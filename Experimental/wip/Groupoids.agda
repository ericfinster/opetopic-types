{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType
open import OpetopicMap

module Groupoids where
  
  IdType : ∀ {ℓ n} (X : Set ℓ) → 𝕆 ℓ n
  ΔMap : ∀ {ℓ n} (X : Set ℓ) (x : X) → 𝕋 {ℓ} n ⇒ IdType X

  data Cell {ℓ n} (X : Set ℓ) : {o : 𝒪 n} → Frm (IdType X) o → Set ℓ where
    id-cell : (x : X) {o : 𝒪 n} (f : Frm (𝕋 {ℓ} n) o)
      → Cell X (Frm⇒ (ΔMap X x) f)

  IdType {n = O} X = tt
  IdType {n = S n} X =
    IdType X , Cell X 
  
  ΔMap {n = O} X x = tt
  ΔMap {n = S n} X x =
    ΔMap X x , λ {o} {f} _ → id-cell x f

  -- What will it be like to prove such a thing is fibrant? 
  
