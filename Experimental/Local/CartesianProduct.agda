--
--  CartsianProduct.agda - Cartesian product of Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Shapes
open import Experimental.Local.Structures

module Experimental.Local.CartesianProduct where

  infixl 60 _×ₒ_
  
  _×ₒ_ : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (Y : 𝕆Type n ℓ₁) → 𝕆Type n (ℓ-max ℓ₀ ℓ₁)

  -- The use of opetopic maps circumvents any need for additional rewrite rules
  Fst : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} → X ×ₒ Y ⇒ X
  Snd : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} → X ×ₒ Y ⇒ Y

  record ×-cell {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    (P : Frm X → Type ℓ₀)
    (Q : Frm Y → Type ℓ₁) (f : Frm (X ×ₒ Y)) : Type (ℓ-max ℓ₀ ℓ₁) where
    constructor _∣_
    field
      fstₒ : P (Frm⇒ Fst f)
      sndₒ : Q (Frm⇒ Snd f)
      
  open ×-cell

  _×ₒ_ {zero} X Y = tt*
  _×ₒ_ {suc n} (X , P) (Y , Q) = X ×ₒ Y , ×-cell P Q

  Fst {zero} = tt*
  Fst {suc n} {X = X , P} {Y , Q} = Fst , fstₒ

  Snd {zero} = tt*
  Snd {suc n} {X = X , P} {Y , Q} = Snd , sndₒ

  -- Fibrancy
  fst-src : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → (P : Frm X → Type ℓ₀) (Q : Frm Y → Type ℓ₁)
    → {f : Frm (X ×ₒ Y)} → Src (×-cell P Q) f → Src P (Frm⇒ Fst f)
  fst-src {n} {ℓ} {X} {Y} P Q {f} s = Src⇒ {P = ×-cell P Q} s Fst (λ p → fstₒ (s ⊚ p))

  snd-src : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → (P : Frm X → Type ℓ₀) (Q : Frm Y → Type ℓ₁)
    → {f : Frm (X ×ₒ Y)} → Src (×-cell P Q) f → Src Q (Frm⇒ Snd f)
  snd-src {n} {ℓ} {X} {Y} P Q {f} s = Src⇒ {P = ×-cell P Q} s Snd (λ p → sndₒ (s ⊚ p))

  -- Since Inhab is defined differently when n=0 or n=(suc k), the following pattern matching is required for agda to type-check
  charac-filler-prod : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type (suc n) ℓ₀} {Y : 𝕆Type (suc n) ℓ₁}
    → (P : Frm X → Type ℓ₀) (Q : Frm Y → Type ℓ₁)
    → {f : Frm (fst X ×ₒ fst Y)} (s : Src (×-cell (snd X) (snd Y)) f) 
    → Iso (horn-filler (×-cell P Q) s)
          (horn-filler P (fst-src (snd X) (snd Y) s) × horn-filler Q (snd-src (snd X) (snd Y) s))
  charac-filler-prod {zero} P Q s = iso g h (λ _ → refl) (λ _ → refl) where
    g : _
    g (tgt , cell) = (fstₒ tgt , fstₒ cell) , (sndₒ tgt , sndₒ cell)
    h : _
    h ((tgt₁ , cell₁) , (tgt₂ , cell₂)) = (tgt₁ ∣ tgt₂) , (cell₁ ∣ cell₂)
  charac-filler-prod {suc n} P Q s = iso g h (λ _ → refl) λ _ → refl where
    g : _
    g (tgt , cell) = (fstₒ tgt , fstₒ cell) , (sndₒ tgt , sndₒ cell)
    h : _
    h ((tgt₁ , cell₁) , (tgt₂ , cell₂)) = (tgt₁ ∣ tgt₂) , (cell₁ ∣ cell₂)

  is-fib-prod : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type (suc (suc n)) ℓ₀} {Y : 𝕆Type (suc (suc n)) ℓ₁}
    → is-fibrant X → is-fibrant Y
    → is-fibrant (X ×ₒ Y)
  is-fib-prod {X = (X , P) , P'} {Y = (Y , Q) , Q'} fibX fibY f s =
    isOfHLevelRespectEquiv 0 (invEquiv (isoToEquiv (charac-filler-prod P' Q' s)))
                             (isContrΣ (fibX _ _) λ _ → fibY _ _)

  prod∞ : ∀ {n ℓ₀ ℓ₁} {Xₙ : 𝕆Type n ℓ₀} {Yₙ : 𝕆Type n ℓ₁}
    → (X : 𝕆Type∞ Xₙ) (Y : 𝕆Type∞ Yₙ)
    → 𝕆Type∞ (Xₙ ×ₒ Yₙ)
  Fill (prod∞ X Y) = ×-cell (Fill X) (Fill Y)
  Hom (prod∞ X Y) = prod∞ (Hom X) (Hom Y)
