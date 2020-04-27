{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import RelationMonad
open import OpetopicType
open import FundamentalThm

module InfinityGroupoid where

  ∞-Rel : (A : Set) → Set₁
  ∞-Rel A = OpetopicType (RelMnd A)

  module _ {A : Set} (R : ∞-Rel A) (is-fib : is-fibrant R) where

    rel : A → A → Set
    rel a₀ a₁ = Flr R a₀ a₁

    refl : (a : A) → rel a a
    refl a = fst (fst (has-level-apply (base-fibrant (hom-fibrant is-fib) (unit , a , a) (lf a)))) 

    rel-is-id : (a₀ : A) (a₁ : A) → rel a₀ a₁ ≃ (a₀ == a₁)
    rel-is-id a₀ a₁ = fundamental-thm A (λ a → rel a₀ a) a₀ (refl a₀)
      (base-fibrant is-fib unit a₀) a₁

  -- A lemma about path spaces needed below
  module _ {i} {A : Type i} where
    
    lemma-to : {a₀ a₁ : A}
      → (p : a₀ == a₁) (aut : a₁ == a₁)
      → (q : a₀ == a₁)
      → p == q → p ∙ aut == q
    lemma-to p aut q α = {!!}


  module _ {M : 𝕄} (F : Filler M) where

    postulate

      F-unique : has-unique-comps M F 

      G₀ : Filler (Slice M F)
      G₁ : Filler (Slice M F)

      G₀-unique : has-unique-comps (Slice M F) G₀
      G₁-unique : has-unique-comps (Slice M F) G₁

    tgt-auto : {f : Frm M} {σ : Tree M f} {τ : Cell M f}
      → (θ₀ θ₁ : Cell (Slice M F) (f , σ , τ)) → τ == τ
    tgt-auto {f} {σ} {τ} θ₀ θ₁ = fst= (contr-has-all-paths ⦃ F-unique f σ ⦄ (τ , θ₀) (τ , θ₁))

    cell-over : {f : Frm M} {σ : Tree M f} {τ : Cell M f}
      → (θ₀ θ₁ : Cell (Slice M F) (f , σ , τ))
      → θ₀ == θ₁ [ (λ x → Cell (Slice M F) (f , σ , x)) ↓ tgt-auto θ₀ θ₁ ]
    cell-over {f} {σ} {τ} θ₀ θ₁ = snd= (contr-has-all-paths ⦃ F-unique f σ ⦄ (τ , θ₀) (τ , θ₁))

    claim : {f : Frm (Slice M F)}
      → (σ : Tree (Slice M F) f) (τ : Cell (Slice M F) f)
      → G₀ σ τ ≃ G₁ σ τ
    claim {f = f , σ₀ , τ₀} σ τ = (G₁-nf)⁻¹ ∘e left-with ∘e G₀-nf

      where G₀-nf : G₀ σ τ ≃ (comp-fun (Slice M F) G₀ G₀-unique σ == τ)
            G₀-nf = fillers-are-pths (Slice M F) G₀ G₀-unique σ τ

            G₁-nf : G₁ σ τ ≃ (comp-fun (Slice M F) G₁ G₁-unique σ == τ)
            G₁-nf = fillers-are-pths (Slice M F) G₁ G₁-unique σ τ

            θ₀ : F σ₀ τ₀
            θ₀ = comp-fun (Slice M F) G₀ G₀-unique σ
            
            θ₁ : F σ₀ τ₀
            θ₁ = comp-fun (Slice M F) G₁ G₁-unique σ

            left-with : (θ₀ == τ) ≃ (θ₁ == τ)
            left-with = {!!}

    -- Hmmm.  We're getting stuck here.  What happens is that the
    -- filling spaces are equivalent up to a kind of conjugation.
    -- There must be some kind of way to generalize so that this is
    -- sufficient for what you want.

    -- Okay, here is a possibility: maybe fibrant is not enough, and
    -- you want to be looking at some kind of restricted space of
    -- extensions.  Then the idea is that the identity types lie in
    -- this restricted space.

    -- And I think there is a kind of candidate: the idea is that you
    -- should look at *natural* extensions.  I'm not sure what I mean
    -- by this in the general case, but I'm thinking about what
    -- characterizes composition, and I think the point is that it is
    -- sufficient to have naturality because then Yoneda kicks in and
    -- says that it must be given by composition with a fixed path,
    -- namely, the image of the identity.

    -- So you should give a quick sketch of the low dimensional yoneda
    -- guy, because I think this is the dimension 1 case of saying
    -- that the extension is unique.  At least it's not completely far
    -- fetched ...
