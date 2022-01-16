{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType
open import OpetopicMap

module TheUniverse where

  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆 ℓ n
  𝕋 O = tt
  𝕋 (S n) = 𝕋 n , λ _ → ⊤ 

  𝕆U : ∀ {ℓ} (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝕆U* : ∀ {ℓ} (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝕦 : ∀ {ℓ} (n : ℕ) → 𝕆U* {ℓ} n ⇒ 𝕆U {ℓ} n

  𝕆U O = tt
  𝕆U {ℓ = ℓ} (S n) = 𝕆U n , λ {o} f →
    (f' : Frm (𝕆U* n) o) (e : Frm⇒ (𝕦 n) f' ≡ f)
    → Set ℓ
  
  𝕆U* O = tt
  𝕆U* {ℓ} (S n) = 𝕆U* n , λ {o} f* →
    Σ ((f' : Frm (𝕆U* n) o) (e : Frm⇒ (𝕦 n) f' ≡ Frm⇒ (𝕦 n) f*) → Set ℓ) (λ F → F f* refl)
  
  𝕦 O = tt
  𝕦 (S n) = 𝕦 n , λ {o} {f} X → fst X

  --
  -- Oh!  And Σ.  What about him?
  --

  -- Σₒ : ∀ {ℓ n} (X : 𝕆 ℓ n) (Y : X ⇒ 𝕆U {ℓ} n) → 𝕆 ℓ n
  -- fstₒ : ∀ {ℓ n} (X : 𝕆 ℓ n) (Y : X ⇒ 𝕆U {ℓ} n) → Σₒ X Y ⇒ X
  -- sndₒ : ∀ {ℓ n} (X : 𝕆 ℓ n) (Y : X ⇒ 𝕆U {ℓ} n) → Σₒ X Y ⇒ 𝕆U* {ℓ} n
  
  -- Σₒ {n = O} X Y = tt
  -- Σₒ {n = S n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
  --   Σₒ Xₙ Yₙ , λ {o} f → Σ (Xₛₙ (Frm⇒ (fstₒ Xₙ Yₙ) f)) (λ x → {!!})
  
  -- fstₒ = {!!}

  -- sndₒ = {!!} 

  --
  --  A first test: suppose I have an opetopic type.  Does this
  --  determine a point of the universe?
  --

  classify : ∀ {ℓ} (n : ℕ) → 𝕆 ℓ n → 𝕋 {ℓ} n ⇒ 𝕆U {ℓ} n

  unclassify : ∀ {ℓ} (n : ℕ) (X : 𝕆 ℓ n) {o : 𝒪 n} 
    → (t : Frm (𝕋 n) o) (f : Frm (𝕆U* n) o)
    → (e : Frm⇒ (𝕦 n) f ≡ Frm⇒ (classify n X) t)
    → Frm X o 

  classify O _ = tt
  classify (S n) (Xₙ , Xₛₙ) = classify n Xₙ ,
    λ {o} {f} _ f' e → Xₛₙ (unclassify n Xₙ f f' e)
  
  unclassify O X t f e = tt
  unclassify (S n) (Xₙ , Xₛₙ) t f e = {!!}

  -- Yeah, so you need to see that pullbacks can be computed pointwise
  -- in trees.  But I think characterizing the identity types of frames
  -- and trees and so on will be done for a fixed n.  So I don't see
  -- that this will necessarily have any coherence problems.

  -- What about the pullback

  -- Pb : ∀ {ℓ n} {X Y Z : 𝕆 ℓ n} (f : X ⇒ Z) (g : Y ⇒ Z) → 𝕆 ℓ n
  
  -- pb-fst : ∀ {ℓ n} {X Y Z : 𝕆 ℓ n} (f : X ⇒ Z) (g : Y ⇒ Z) → Pb f g ⇒ X
  -- pb-snd : ∀ {ℓ n} {X Y Z : 𝕆 ℓ n} (f : X ⇒ Z) (g : Y ⇒ Z) → Pb f g ⇒ Y

  -- I see.  So we need to simultaneously show that the square commutes
  -- in order to finish this.  But this should be completely determined
  -- by the inductive hypothesis and some simple lemmas.  So this seems
  -- fine to me.  I think it will go through.

  -- Pb {n = O} f g = tt
  -- Pb {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (fₙ , fₛₙ) (gₙ , gₛₙ) =
  --   Pb fₙ gₙ , λ {o} f →
  --     Σ (Xₛₙ (Frm⇒ (pb-fst fₙ gₙ) f)) (λ x →
  --     Σ (Yₛₙ (Frm⇒ (pb-snd fₙ gₙ) f)) (λ y →
  --       {!!}))

  -- pb-fst = {!!}
  -- pb-snd = {!!} 

  --  What about just the product?

  infixl 45 _×ₒ_
  
  _×ₒ_ : ∀ {ℓ n} (X Y : 𝕆 ℓ n) → 𝕆 ℓ n
  π₀ : ∀ {ℓ n} {X Y : 𝕆 ℓ n} → X ×ₒ Y ⇒ X
  π₁ : ∀ {ℓ n} {X Y : 𝕆 ℓ n} → X ×ₒ Y ⇒ Y

  _×ₒ_ {n = O} X Y = tt
  _×ₒ_ {n = S n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Xₙ ×ₒ Yₙ , λ f → Xₛₙ (Frm⇒ π₀ f) × Yₛₙ (Frm⇒ π₁ f)

  π₀ {n = O} {X} {Y} = tt
  π₀ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} =
    π₀ {X = Xₙ} {Y = Yₙ} , fst
  
  π₁ {n = O} {X} {Y} = tt
  π₁ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} = 
    π₁ {X = Xₙ} {Y = Yₙ} , snd

  -- Easy peasy!

  -- So, why was I thinking about this?  Ah, right.  Because then you
  -- should be able to define internal identity types, right? As the
  -- fiber of the diagonal?

  -- Although now that I think of it, there's probably just a direct
  -- definition as well.  You have two "points' of an opetopic type,
  -- and you do what?  Have to think about it....

  -- But in any case, you now have 𝕌, Σ, Π and Id!  So you have a whole
  -- copy of Martin-Löf type theory!
