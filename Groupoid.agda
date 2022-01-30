--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType
open import OpetopicTerm

module Groupoid where

  Grp : ∀ {n ℓ} (X : Type ℓ) → 𝕆Type (𝕋 n) ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕆Term {n} (Grp X)

  -- The extra units make this sloppy, but okay ...
  data 𝕆Id {n ℓ} (X : Type ℓ) : {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜}
    → Frm↓ (Grp X) f → Lift Unit → Type ℓ where
    op-refl : (x : X) {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜} (γ : Lift Unit)
      → 𝕆Id X (Frm-Tm (Pt x) f) γ

  Grp {zero} X = lift tt
  Grp {suc n} X =
    Grp {n} X , 𝕆Id X

  Pt {zero} x = lift tt
  Pt {suc n} x = Pt {n} x , op-refl x


  -- Here's an idea: what if you can lift any context to be a type in
  -- the terminal context?

  reify : ∀ {n ℓ} (X : 𝕆Ctx n ℓ) → 𝕆Type (𝕋 n) ℓ
  Frm-reify : ∀ {n ℓ} (X : 𝕆Ctx n ℓ)
    → {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜} (f↓ : Frm↓ (reify X) f)
    → Frm X 𝑜
  
  reify {zero} X = lift tt
  reify {suc n} (Xₙ , Xₛₙ) = reify Xₙ , λ f↓ _ → Xₛₙ (Frm-reify Xₙ f↓)

  Frm-reify {zero} X f↓ = lift tt
  Frm-reify {suc n} (Xₙ , Xₛₙ) (f↓ , x↓ , c↓ , y↓) =
    Frm-reify Xₙ f↓ , x↓ , {!!} , {!!} 

  -- I mean, another possibility would be to have a general fiber
  -- construction.

