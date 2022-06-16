--
--  Category.agda - Equivalence between categories and 1-truncated (∞,1)-categories
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Shapes
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.Category where

module _ {ℓ} (C : Category ℓ ℓ) where
  open Category C renaming (id to C-id ; _⋆_ to _⨀_)

  n-comp : {n : ℕ} {t : ob ** (suc n)} → path-chain Hom[_,_] n t → Hom[ last t , fstt t ]
  n-comp {zero} {x} _ = C-id
  n-comp {suc zero} {y , x} f = f
  n-comp {suc (suc n)} {y , x , t} (f , l) = n-comp {suc n} {x , t} l ⨀ f

  private
    X₀ : Frm (𝕋 {ℓ = ℓ} 0) → Type ℓ
    X₀ _ = ob

    X₁ : Frm (tt* , X₀) → Type ℓ
    X₁ (_ , x , y) = Hom[ x , y ]

    C-src-comp : {f : Frm (tt* , X₀)} → Src X₁ f → X₁ f
    C-src-comp (lf x) = C-id {x = x}
    C-src-comp (nd tgt [ stm₁ , lvs₁ , br₁ ] flr) = (C-src-comp br₁) ⨀ flr

    X₂ : Frm ((tt* , X₀) , X₁) → Type ℓ
    X₂ (f , s , t) = C-src-comp s ≡ t

    C-2-src-comp : {f : Frm ((tt* , X₀) , X₁)} → Src X₂ f → X₂ f
    C-2-src-comp (lf tgt) = ⋆IdL tgt
    C-2-src-comp (nd tgt (lf tgt₁) flr) = flr
    C-2-src-comp (nd tgt (nd tgt₁ brs flr₁) flr) = {!!}

  Cat→𝕆Type : 𝕆Type∞ {ℓ = ℓ} tt*
  Fill Cat→𝕆Type = X₀
  Fill (Hom Cat→𝕆Type) = X₁
  Fill (Hom (Hom Cat→𝕆Type)) = X₂
  Hom (Hom (Hom Cat→𝕆Type)) = 𝕋Ext _

  open is-fibrant-ext

  lemma : ∀ {ℓ} {A : Type ℓ} {a : A} → isContr (Σ[ b ∈ A ] a ≡ b)
  lemma {a = a} = (a , refl) , (λ (b , p) i → (p i , λ j → p (i ∧ j)))

  module _ (isGroupoidC : isGroupoid ob) where
    isInfCatCat : is-fibrant-ext (Hom Cat→𝕆Type)
    fill-fib isInfCatCat f s = lemma
    hom-fib (hom-fib isInfCatCat) = is-fib-ext-𝕋Ext
    fill-fib (hom-fib isInfCatCat) (f , s , t) s' = (C-2-src-comp s' , tt*) , λ y → Σ≡Prop (λ _ _ _ → refl) (isSetHom _ _ _ _)

