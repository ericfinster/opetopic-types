--
-- PositionlessMap.agda - Maps between opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.Prelude
open import Experimental.Positionless

module Experimental.PositionlessMap where
  _⇒_ : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ → Type ℓ
  Frm⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} → X ⇒ Y → Frm X → Frm Y
  Src⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
    → {Xₛₙ : Frm Xₙ → Type ℓ}
    → {Yₛₙ : Frm Yₙ → Type ℓ}
    → (σₙ : Xₙ ⇒ Yₙ)
    → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f ))
    → {f : Frm Xₙ}
    → Src Xₙ Xₛₙ f → Src Yₙ Yₛₙ (Frm⇒ σₙ f)
  
  _⇒_ {zero} X Y = Lift Unit
  _⇒_ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) = Σ[ fun ∈ Xₙ ⇒ Yₙ ] ((f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ fun f))

  Frm⇒ {zero} {ℓ} {X} {Y} fun f = tt*
  Frm⇒ {suc n} {ℓ} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (funₙ , funₛₙ) (f , t , s) =
    (Frm⇒ funₙ f) , (funₛₙ _ t) , Src⇒ Xₙ Yₙ funₙ funₛₙ s
      {-smap Yₙ funₛₙ* {!!} where
      data Xₛₙ* : Frm Yₙ → Type ℓ where
        test : {f : Frm Xₙ} (x : Xₛₙ f) → Xₛₙ* (Frm⇒ funₙ f)

      funₛₙ* : (f : Frm Yₙ) → Xₛₙ* f → Yₛₙ f
      funₛₙ* .(Frm⇒ funₙ _) (test x) = funₛₙ _ x-}

  postulate
    η⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
      → {Xₛₙ : Frm Xₙ → Type ℓ}
      → {Yₛₙ : Frm Yₙ → Type ℓ}
      → (σₙ : Xₙ ⇒ Yₙ)
      → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f))
      → {f : Frm Xₙ} (x : Xₛₙ f)
      → Src⇒ Xₙ Yₙ σₙ σₛₙ (η Xₙ Xₛₙ x) ↦ η Yₙ Yₛₙ (σₛₙ f x)
    {-# REWRITE η⇒ #-}

    {-μ⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
      → {Xₛₙ : Frm Xₙ → Type ℓ}
      → {Yₛₙ : Frm Yₙ → Type ℓ}
      → (σₙ : Xₙ ⇒ Yₙ)
      → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f))
      → {f : Frm Xₙ} (x : Xₛₙ f)
      → (ih : {!Src Xₙ ? (Frm⇒ σₙ f)!})
      → Src⇒ Xₙ Yₙ σₙ σₛₙ (μ Xₙ Xₛₙ (smap Xₙ (λ _ x → fst (snd x)) ih)) ↦ μ Yₙ Yₛₙ (smap Yₙ (λ f x → fst (snd x)) (Src⇒ Xₙ Yₙ σₙ {!σₛₙ!} ih))-}

  Src⇒ {zero} Xₙ Yₙ σₙ σₛₙ {f} s = σₛₙ f s
  Src⇒ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) (σₙ , σₛₙ) σₛₛₙ {.(f , tgt , η Xₙ Xₛₙ tgt)} (lf f tgt) = lf (Frm⇒ σₙ f) (σₛₙ f tgt)
  Src⇒ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) (σₙ , σₛₙ) σₛₛₙ {.(f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ z → fst ∘ snd) ih))} (nd f tgt ih filler) =
    nd (Frm⇒ σₙ f) (σₛₙ f tgt) (Src⇒ {!!} {!!} σₙ {!σₛₙ!} {!!}) {!!}
  
