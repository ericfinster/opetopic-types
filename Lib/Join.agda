--
--  Join.agda - The Join of Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Core.Everything

module Lib.Join where

  Join : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (Y : 𝕆Type n ℓ₁)
    → 𝕆Type n (ℓ-max ℓ₀ ℓ₁)

  join-inl : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → X ⇒ Join X Y

  join-inr : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → Y ⇒ Join X Y

  is-traversing : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type (2 + n) ℓ₀} {Y : 𝕆Type (2 + n) ℓ₁}
    → {𝑜 : 𝒪 (2 + n)} (f : Frm (Join X Y) 𝑜) → Type

  data JoinArrow {ℓ₀ ℓ₁} (X : 𝕆Type 2 ℓ₀) (Y : 𝕆Type 2 ℓ₁) : {𝑜 : 𝒪 1} 
      → WebFrm tt* (λ _ → snd (fst X) tt* ⊎ snd (fst Y) tt*) (snd 𝑜)
      → Type (ℓ-max ℓ₀ ℓ₁) 

  data JoinCell {n ℓ₀ ℓ₁} (X : 𝕆Type (3 + n) ℓ₀) (Y : 𝕆Type (3 + n) ℓ₁)
    : {𝑜 : 𝒪 (2 + n)} → Frm (Join (fst X) (fst Y)) 𝑜 → Type (ℓ-max ℓ₀ ℓ₁) 

  Join {zero} X Y = tt*
  Join {suc zero} X Y =
    Join {0} (fst X) (fst Y) ,
    λ _ → snd X tt* ⊎ snd Y tt*
  Join {suc (suc zero)} X Y =
    Join {1} (fst X) (fst Y) , JoinArrow X Y 
  Join {suc (suc (suc n))} X Y =
    Join {suc (suc n)} (fst X) (fst Y) ,
    JoinCell X Y

  data JoinArrow {ℓ₀ ℓ₁} X Y where

    jarr-inl : (x₀ : snd (fst X) tt*) (x₁ : snd (fst X) tt*)
      → (α : snd X (tt* , x₀ , tt* , λ _ → x₁))
      → JoinArrow X Y (tt* , inl x₀ , tt* , λ _ → inl x₁)

    jarr-inr : (y₀ : snd (fst Y) tt*) (y₁ : snd (fst Y) tt*)
      → (β : snd Y (tt* , y₀ , tt* , λ _ → y₁))
      → JoinArrow X Y (tt* , inr y₀ , tt* , λ _ → inr y₁)

    jarr-inm : (x : snd (fst X) tt*) (y : snd (fst Y) tt*)
      → JoinArrow X Y (tt* , inl x , tt* , λ _ → inr y)

  data JoinCell {n ℓ₀ ℓ₁} X Y where

    jcell-inl : {𝑜 : 𝒪 (2 + n)} {f : Frm (fst X) 𝑜} (x : snd X f)
      → JoinCell X Y (Frm⇒ {Δ = Join (fst X) (fst Y)} join-inl f)

    jcell-inr : {𝑜 : 𝒪 (2 + n)} {f : Frm (fst Y) 𝑜} (y : snd Y f)
      → JoinCell X Y (Frm⇒ {Δ = Join (fst X) (fst Y)} join-inr f)

    jcell-inm : {𝑜 : 𝒪 (2 + n)} (f : Frm (Join (fst X) (fst Y)) 𝑜)
      → is-traversing f 
      → JoinCell X Y f 

  is-traversing {zero} ((.tt* , .(inl x₀) , .tt* , .(λ _ → inl x₁)) , jarr-inl x₀ x₁ α , _ , _) = ⊥
  is-traversing {zero} ((.tt* , .(inr y₀) , .tt* , .(λ _ → inr y₁)) , jarr-inr y₀ y₁ β , _ , _) = ⊥
  is-traversing {zero} ((.tt* , .(inl x) , .tt* , .(λ _ → inr y)) , jarr-inm x y , _ , _) = Unit
  is-traversing {suc n} f = is-traversing (fst f)

  join-inl {zero} = tt*
  join-inl {suc zero} = tt* , λ { {tt} {tt*} x → inl x }
  join-inl {suc (suc zero)} = join-inl {1} , λ { {_} {_ , x₀ , _ , x₁} α → jarr-inl x₀ (x₁ tt) α }
  join-inl {suc (suc (suc n))} = join-inl {2 + n} , jcell-inl

  join-inr {zero} = tt*
  join-inr {suc zero} = tt* , λ { {tt} {tt*} y → inr y }
  join-inr {suc (suc zero)} = join-inr {1} , λ { {_} {_ , y₀ , _ , y₁} β → jarr-inr y₀ (y₁ tt) β }
  join-inr {suc (suc (suc n))} = join-inr {2 + n} , jcell-inr

  --
  --  Obvious theorem: if X and Y are (∞,1)-categories, then so is their join ... 
  -- 
