open import Cubical.Foundations.Everything

open import Core.Prelude
open import Experimental.LessPositions.OpetopicType

open import Cubical.Data.Nat

module Experimental.LessPositions.Structures where
  record 𝕆Type∞ {n ℓ} (Xₙ : 𝕆Type n ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      Fill : Frm Xₙ → Type ℓ
      Hom : 𝕆Type∞ (Xₙ , Fill)

  open 𝕆Type∞ public

  horn-filler : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ) {f : Frm Xₙ} → Src Xₛₙ f → Type ℓ
  horn-filler {n} {ℓ} {Xₙ} {Xₛₙ} Xₛₛₙ {f} s = Σ[ tgt ∈ Xₛₙ f ] Xₛₛₙ (f , tgt , s)

  is-fibrant : ∀ {n ℓ} → 𝕆Type (suc (suc n)) ℓ → Type ℓ
  is-fibrant ((Xₙ , Xₛₙ) , Xₛₛₙ) = (f : Frm Xₙ) (s : Src Xₛₙ f) → isContr (horn-filler Xₛₛₙ s)

  record is-fibrant-ext {n ℓ} {Xₙ : 𝕆Type n ℓ} (X : 𝕆Type∞ Xₙ) : Type ℓ where
    coinductive
    field
      fill-fib : is-fibrant ((Xₙ , (Fill X)) , (Fill (Hom X)))
      hom-fib : is-fibrant-ext (Hom X)

  open is-fibrant-ext

  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Type n ℓ
  𝕋 zero = tt*
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit

  𝕋Ext : ∀ {n ℓ} (X : 𝕆Type n ℓ) → 𝕆Type∞ X
  Fill (𝕋Ext X) = λ _ → Lift Unit
  Hom (𝕋Ext X) = 𝕋Ext _

  is-fib-ext-𝕋Ext : ∀ {n ℓ} {X : 𝕆Type n ℓ} → is-fibrant-ext (𝕋Ext X)
  fill-fib is-fib-ext-𝕋Ext f s = (tt* , tt*) , λ (tt* , tt*) → refl
  hom-fib is-fib-ext-𝕋Ext = is-fib-ext-𝕋Ext

  hom→path : ∀ {ℓ} {X : 𝕆Type∞ (𝕋 {ℓ} 0)} → is-fibrant-ext X → (x y : X .Fill tt*) → X .Hom .Fill (tt* , y , x) → x ≡ y
  hom→path {ℓ} {X} fib x y σ = sym (transportRefl x) ∙ cong fst (isContr→isProp (fib .fill-fib tt* x) (Id x x refl) b) where
    Id : (x y : X .Fill tt*) → (x ≡ y) → horn-filler (Fill (Hom X)) x
    Id x y = J (λ y p → horn-filler (Fill (Hom X)) x) (x , fib .hom-fib .fill-fib (tt* , x , x) (lf x) .fst .fst)

    b : horn-filler (Fill (Hom X)) x
    b = y , σ





    μ' : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} {f : Frm Xₙ}
      → Src (Src Xₛₙ) f → Src Xₛₙ f
    μ' {Xₛₙ = Q} s = μ Q s (s ⊚_ )
