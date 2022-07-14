--
--  Category.agda - Equivalence between categories and 1-truncated (∞,1)-categories
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Core.Prelude
open import Experimental.NoDecs.Revised.OpetopicType
open import Experimental.NoDecs.Revised.Shapes
open import Experimental.NoDecs.Revised.Structures

module Experimental.NoDecs.Revised.Category where

module _ {ℓ} (C : Category ℓ ℓ) where
  lemma-that-should-be-refl : ∀ {n ℓ₀} {X : 𝕆Type n ℓ₀}
      → (P : Frm X → Type ℓ₀)
      → (Q : Frm X → Type ℓ₀)
      → (R : Frm X → Type ℓ₀)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (ψ : (q : Pos Q (ν s (id-map X) ϕ)) → R (Typ Q (ν s (id-map X) ϕ) q))
      → ν {Q = R} (ν s (id-map X) ϕ) (id-map X) ψ ≡ ν s (id-map X) (λ p → ψ (ν-pos s (id-map X) ϕ p))
  lemma-that-should-be-refl P Q R s ϕ ψ = refl

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

    -- lemma relating C-src-comp to μ
    {-# TERMINATING #-}
    big-lemma : {f : Frm (tt* , X₀)} (brs : Src (Src X₁) f) →
      C-src-comp (μ X₁ brs) ≡
      C-src-comp (ν {Q = X₁} brs (id-map _) λ p → C-src-comp (brs ⊚ p))
    big-lemma (lf tgt) = refl
    big-lemma (nd _ brs (lf _)) = big-lemma (br brs) ∙ sym (⋆IdR _)
    big-lemma (nd tgt brs (nd _ [ stm₁ , _ , br₁ ] flr)) = (cong (_⨀ flr) (big-lemma (nd stm₁ brs br₁))) ∙ ⋆Assoc _ (C-src-comp br₁) flr

    {-# TERMINATING #-}
    C-2-src-comp : {f : Frm ((tt* , X₀) , X₁)} → Src X₂ f → X₂ f
    C-2-src-comp (lf tgt) = ⋆IdL tgt
    C-2-src-comp (nd tgt brs flr) =
      big-lemma (ν brs (id-map (tt* , X₀)) (λ p → lvs (brs ⊚ p))) ∙
      {!cong C-src-comp lemma0!} ∙ IH ∙ flr where -- This last hole should be refl if the rewrite rules worked correctly
      IH :
         C-src-comp (ν brs (id-map (tt* , X₀)) λ p → C-src-comp (lvs (brs ⊚ p))) ≡
         C-src-comp (understory X₂ brs)
      IH i = C-src-comp (ν brs (id-map (tt* , X₀)) (λ p → C-2-src-comp (br (brs ⊚ p)) i))

      {-aaaah = lemma-that-should-be-refl (Branch X₂) (Src X₁) X₁ brs (λ p → lvs (brs ⊚ p)) (λ p →
        C-src-comp
        (ν brs (tt* , (λ p₁ → p₁))
         (λ p₁ → lvs (brs ⊚ p₁))
         ⊚ p))

      lemma0 :
        ν (ν {Q = Src X₁} brs (id-map _) (λ p → lvs (brs ⊚ p)))
        (id-map (tt* , X₀))
        (λ p →
           C-src-comp
           (ν brs (id-map (tt* , X₀)) (λ p₁ → lvs (brs ⊚ p₁)) ⊚ p))
           ≡
         ν brs (id-map (tt* , X₀)) λ p → C-src-comp (lvs (brs ⊚ p))
      lemma0 = aaaah ∙ {!!} where
        {-test : (p : Pos (Branch X₂) brs) → 
          (ν {Q = Src X₁} brs (tt* , (λ p₁ → p₁))
           (λ p₁ → lvs (brs ⊚ p₁))) ⊚
          (ν-pos brs (tt* , (λ p₁ → p₁))
           (λ p₁ → lvs (brs ⊚ p₁)) p) ≡
           (lvs (brs ⊚ p))
        test p = {!!}-}

-}
      

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


