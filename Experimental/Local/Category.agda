--
--  Category.agda - Equivalence between categories and 1-truncated (∞,1)-categories
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.Shapes
open import Experimental.Local.Structures
open import Experimental.Local.Terminal

module Experimental.Local.Category where

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
    C-src-comp (lf tgt) = C-id {x = tgt}
    C-src-comp (nd src tgt flr brs) = C-src-comp (br brs) ⨀ flr

    X₂ : Frm ((tt* , X₀) , X₁) → Type ℓ
    X₂ (f , s , t) = C-src-comp s ≡ t

    {-# TERMINATING #-}
    big-lemma : {f : Frm (tt* , X₀)} (brs : Src (Src X₁) f) →
      C-src-comp (μ X₁ brs) ≡
      C-src-comp (ν {Q = X₁} brs λ p → C-src-comp (brs ⊚ p))
    big-lemma (lf tgt) = refl
    big-lemma (nd src .src (lf .src) brs) = big-lemma (br brs) ∙ sym (⋆IdR _)
    big-lemma (nd ._ tgt (nd src .tgt flr lbrs) brs) =
      cong (_⨀ flr) (big-lemma (nd (lvs lbrs) src (br lbrs) brs)) ∙
      (⋆Assoc _ (C-src-comp (br lbrs)) flr)

    {-# TERMINATING #-}
    C-2-src-comp : {f : Frm ((tt* , X₀) , X₁)} → Src X₂ f → X₂ f
    C-2-src-comp (lf tgt) = ⋆IdL tgt
    C-2-src-comp (nd src tgt flr brs) =
      big-lemma (ν {Q = Pd X₁} src (λ p → lvs (brs ⊛ p))) ∙ IH ∙ flr

      where IH : C-src-comp (ν {Q = X₁} src (λ p → C-src-comp (lvs (brs ⊛ p)))) ≡ 
                 C-src-comp src
            IH i =  C-src-comp (ν {Q = X₁} src (λ p → C-2-src-comp (br (brs ⊛ p)) i))

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


