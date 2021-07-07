{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse
open import AbsoluteOpetopicTypes
open import DependentOpetopicType

module OpetopicAlgebra where

  --
  --  Multiplicative Structures
  --
  
  mult-struct : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n)
    → (Xₛₙ : Frm Xₙ → Set ℓ) → Set ℓ 
  mult-struct {n = O} X₀ X₁ =
      (P : ℙ) (ν : El P → X₀)
    → Σ X₀ (λ x → X₁ ⟪ x , P , ν ⟫) 
  mult-struct {n = S n} (Xₙ , Xₛₙ) Xₛₛₙ =
      (f : Frm Xₙ) (o : Opr Xₙ f)
    → (ν : (p : El (pos o)) → Xₛₙ (typ o p))
    → Σ (Xₛₙ f) (λ x → Xₛₛₙ (f , x , ⟪ o , ν ⟫f))

  record Mult∞ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (X∞ : 𝕆∞ Xₙ) : Set ℓ where
    coinductive
    field
      m : mult-struct Xₙ (Head X∞)
      h : Mult∞ (Xₙ , Head X∞) (Tail X∞)

  open Mult∞

  is-unique : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n}
    → {Xₛₙ : Frm Xₙ → Set ℓ}
    → mult-struct Xₙ Xₛₙ → Set ℓ
  is-unique {n = O} {X₀} {X₁} M =
      (P : ℙ) (ν : El P → X₀)
      (x₀ : X₀) (x₁ : X₁ ⟪ x₀ , P , ν ⟫)
    → (x₀ , x₁) ≡ M P ν
  is-unique {n = S n} {Xₙ , Xₛₙ} {Xₛₛₙ} M =
      (f : Frm Xₙ) (o : Opr Xₙ f)
    → (ν : (p : El (pos o)) → Xₛₙ (typ o p))
    → (xₛₙ : Xₛₙ f) (xₛₛₙ : Xₛₛₙ (f , xₛₙ , ⟪ o , ν ⟫f))
    → (xₛₙ , xₛₛₙ) ≡ M f o ν 

  record UniqueMult∞ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {X∞ : 𝕆∞ Xₙ} (M : Mult∞ Xₙ X∞) : Set ℓ where
    coinductive
    field
      u : is-unique (m M)
      uh : UniqueMult∞ (h M)

  OpetopicType : (ℓ : Level) → Set (ℓ-suc ℓ)
  OpetopicType ℓ = Σ (Set ℓ) 𝕆∞ 

  is-fibrant : ∀ {ℓ} → OpetopicType ℓ → Set ℓ
  is-fibrant (X , X∞) = Σ (Mult∞ X X∞) UniqueMult∞  

  is-unary : ∀ {ℓ} → OpetopicType ℓ → Set ℓ
  is-unary (X , X∞) = (α : Arity X) (x : Head X∞ α)
    → is-contr (El (pos α)) 

  is-finitary : ∀ {ℓ} → OpetopicType ℓ → Set ℓ
  is-finitary (X , X∞) = (α : Arity X) (x : Head X∞ α)
    → is-finite (El (pos α)) 

  --
  --  ∞-Groupoids
  --
  
  record ∞-Groupoid {ℓ} : Set (ℓ-suc ℓ) where
    field
      Obj : Set ℓ
      Hom : 𝕆∞ Obj
      M : Mult∞ Obj Hom
      U : UniqueMult∞ M
      un : is-unary (Obj , Hom)
      
  --
  --  ∞-Categories
  --

  record ∞-Category {ℓ} : Set (ℓ-suc ℓ) where
    field
      Obj : Set ℓ
      Hom : 𝕆∞ Obj
      M : Mult∞ Obj Hom
      U : UniqueMult∞ (h M)
      un : is-unary (Obj , Hom)
    
  --
  --  ∞-operads 
  --

  -- I mean, really these are colored, so ...
  record ∞-Operad {ℓ} : Set (ℓ-suc ℓ) where
    field
      Obj : Set ℓ
      Hom : 𝕆∞ Obj
      M : Mult∞ Obj Hom
      U : UniqueMult∞ (h M)
      un : is-finitary (Obj , Hom)

  --
  --  Things to show:
  --    1. the "homs" of any ∞-cat are ∞-groupids ...
  --    2. extract the comosition operator and show it is associative
  --    3. construct the ∞-cat structure on types
  --    4. a presheaf is a map to the universe
  --

  --
  --  Dependent Definitions
  --

  is-fibration : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → (f : Frm X) (R : Frm↓ X↓ f → Set ℓ↓)
    → Set ℓ↓
  is-fibration {n = O} {X↓ = X↓} A R =
      (ν : (p : El (pos A)) → X↓ (typ A p))
    → is-contr (Σ (X↓ (frm A)) (λ x↓ → R (x↓ , ν)))
  is-fibration {n = S n} {X = Xₙ , Xₛₙ} {X↓ = X↓ₙ , X↓ₛₙ} (f , xₛₙ , fₛₙ) R =
     (f↓ : Frm↓ X↓ₙ f) 
     (o : Opr↓ X↓ₙ f↓ (opr fₛₙ))
     (ν↓ : (p : El (pos (opr fₛₙ))) → X↓ₛₙ (typ↓ o p) (dec fₛₙ p)) → 
     is-contr (Σ (X↓ₛₙ f↓ xₛₙ) (λ x↓ₛₙ → R (f↓ , x↓ₛₙ , ⟪ o , ν↓ ⟫f↓)))


