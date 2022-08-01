--
--  Join.agda - The Join of Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Core.OpetopicType
open import Core.OpetopicMap

module Lib.Join where

  Join : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (Y : 𝕆Type n ℓ₁)
    → 𝕆Type n (ℓ-max ℓ₀ ℓ₁)

  join-inl : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → X ⇒ Join X Y

  join-inr : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → Y ⇒ Join X Y

  is-traversing : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type (2 + n) ℓ₀} {Y : 𝕆Type (2 + n) ℓ₁}
    → Frm (Join X Y) → Type

  data JoinArrow {ℓ₀ ℓ₁} (X : 𝕆Type 2 ℓ₀) (Y : 𝕆Type 2 ℓ₁) :  
    Frm (tt* , λ _ → snd (fst X) tt* ⊎ snd (fst Y) tt*) → Type (ℓ-max ℓ₀ ℓ₁) 

  data JoinCell {n ℓ₀ ℓ₁} (X : 𝕆Type (3 + n) ℓ₀) (Y : 𝕆Type (3 + n) ℓ₁)
    : Frm (Join (fst X) (fst Y)) → Type (ℓ-max ℓ₀ ℓ₁) 

  Join {zero} X Y = tt*
  Join {suc zero} X Y =
    Join {0} (fst X) (fst Y) ,
    λ _ → snd X tt* ⊎ snd Y tt*
  Join {suc (suc zero)} ((X₀ , X₁) , X₂) ((Y₀ , Y₁) , Y₂) =
    Join {1} (X₀ , X₁) (Y₀ , Y₁) , JoinArrow ((X₀ , X₁) , X₂) ((Y₀ , Y₁) , Y₂)
  Join {suc (suc (suc n))} X Y =
    Join {suc (suc n)} (fst X) (fst Y) , JoinCell X Y

  data JoinArrow {ℓ₀ ℓ₁} X Y where

    jarr-inl : (x₀ : snd (fst X) tt*) (x₁ : snd (fst X) tt*)
      → (α : (snd X) (tt* , x₀ , x₁))
      → JoinArrow X Y (tt* , inl x₀ , inl x₁)

    jarr-inr : (y₀ : snd (fst Y) tt*) (y₁ : snd (fst Y) tt*)
      → (β : snd Y (tt* , y₀ ,  y₁))
      → JoinArrow X Y (tt* , inr y₀ , inr y₁)

    jarr-inm : (x : snd (fst X) tt*) (y : snd (fst Y) tt*)
      → JoinArrow X Y (tt* , inl x , inr y)

  data JoinCell {n ℓ₀ ℓ₁} X Y where

    jcell-inl : {f : Frm (fst X)} (x : snd X f)
      → JoinCell X Y (Frm⇒ {Y = Join (fst X) (fst Y)} join-inl f)

    jcell-inr : {f : Frm (fst Y)} (y : snd Y f)
      → JoinCell X Y (Frm⇒ {Y = Join (fst X) (fst Y)} join-inr f)

    jcell-inm : (f : Frm (Join (fst X) (fst Y)))
      → is-traversing f → JoinCell X Y f 

  is-traversing {n = zero} (._ , s , jarr-inl x₀ x₁ α) = ⊥
  is-traversing {n = zero} (._ , s , jarr-inr y₀ y₁ β) = ⊥
  is-traversing {n = zero} (._ , s , jarr-inm x y) = Unit
  is-traversing {n = suc n} (f , s , t) = is-traversing f

  join-inl {zero} = tt*
  join-inl {suc zero} = tt* , inl
  join-inl {suc (suc zero)} {X = (X₀ , X₁) , X₂} {Y = (Y₀ , Y₁) , Y₂} =
    join-inl {1} {X = (X₀ , X₁)} {Y = (Y₀ , Y₁)} , λ { {_ , x₀ , x₁} α → jarr-inl x₀ x₁ α } 
  join-inl {suc (suc (suc n))} = join-inl {2 + n} , jcell-inl

  join-inr {zero} = tt*
  join-inr {suc zero} = tt* , inr
  join-inr {suc (suc zero)} {X = (X₀ , X₁) , X₂} {Y = (Y₀ , Y₁) , Y₂} =
    join-inr {1} {X = (X₀ , X₁)} {Y = (Y₀ , Y₁)} , λ { {_ , y₀ , y₁} β → jarr-inr y₀ y₁ β } 
  join-inr {suc (suc (suc n))} = join-inr {2 + n} , jcell-inr
  
