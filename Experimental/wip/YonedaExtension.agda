{-# OPTIONS --without-K --rewriting --guardedness #-}

open import MiniHoTT

open import Opetopes
open import OpetopicType
open import OpetopicMap

module YonedaExtension where

  record 𝕆∞ {ℓ n} (X : 𝕆 ℓ n) : Set (ℓ-suc ℓ) where
    coinductive
    field
      Fill : {o : 𝒪 n} → Frm X o → Set ℓ 
      Hom : 𝕆∞ (X , Fill) 

  open 𝕆∞

  record [_⇒_↓_] {ℓ n} {X Y : 𝕆 ℓ n} (X∞ : 𝕆∞ X) (Y∞ : 𝕆∞ Y) (α : X ⇒ Y)  : Set ℓ where
    coinductive
    field
      Fill⇒ : {o : 𝒪 n} {f : Frm X o} → Fill X∞ f → Fill Y∞ (Frm⇒ α f)
      Hom⇒ : [ Hom X∞ ⇒ Hom Y∞ ↓ α , Fill⇒ ]


  OType : (ℓ : Level) → Set (ℓ-suc ℓ)
  OType ℓ = 𝕆∞ tt 

  -- Oh, but maybe this is not general enough for the applications
  -- you have in mind... Should D take values in opetopic types, not
  -- just truncated ones?

  -- truncated version ...
  -- record CoOpetopicDiagram (ℓ : Level) : Set (ℓ-suc ℓ) where
  --   field
  --     D : {n : ℕ} (o : 𝒪 n) → 𝕆 ℓ (S n)
  --     σ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → D (Typ ρ p) ⇒ fst (D (o , ρ))
  --     τ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → D o ⇒ fst (D (o , ρ))

  record CoOpetopicDiagram (ℓ : Level) : Set (ℓ-suc ℓ) where
    field
      D : {n : ℕ} (o : 𝒪 n) → 𝕆∞ {ℓ} tt 
      σ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → [ D (Typ ρ p) ⇒ D (o , ρ) ↓ tt ] 
      τ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → [ D o ⇒ D (o , ρ) ↓ tt ]

  open CoOpetopicDiagram

  Right : ∀ {ℓ} (𝒟 : CoOpetopicDiagram ℓ) (X : 𝕆∞ {ℓ} tt)
    → (n : ℕ) → 𝕆 ℓ n
  
  Restrict : ∀ {ℓ} (𝒟 : CoOpetopicDiagram ℓ) (X : 𝕆∞ {ℓ} tt)
    → {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) → [ D 𝒟 (o , ρ) ⇒ X ↓ tt ] → Frm (Right 𝒟 X n) o
  
  Right 𝒟 X O = tt
  Right 𝒟 X (S O) = {!!}
  Right 𝒟 X (S (S n)) = Right 𝒟 X (S n) , {!!}

  Restrict = {!!} 

  -- Maybe this sould be like a Π in that it comes with a kind of
  -- evaluation function? 

