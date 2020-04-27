{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import OpetopicType
open import FundamentalThm

module IdRels where

  -- Okay, I'd like to do the lowest dimensional case of the thing you
  -- want to prove.  Because it seems to be actually true in dimension
  -- 1.  So I'd like to understand the proof and what exactly goes
  -- wrong in higher dimensions.

  module _ {i} (A : Type i)
    (R₀ R₁ : A → A → Type i)
    (r₀ : (a : A) → R₀ a a)
    (r₁ : (a : A) → R₁ a a)
    (u₀ : (a : A) → is-contr (Σ A (R₀ a)))
    (u₁ : (a : A) → is-contr (Σ A (R₁ a))) where

    short-proof : (a₀ a₁ : A) → R₀ a₀ a₁ ≃ R₁ a₀ a₁
    short-proof a₀ a₁ = F ⁻¹ ∘e E

      where E : R₀ a₀ a₁ ≃ (a₀ == a₁)
            E = fundamental-thm A (R₀ a₀) a₀ (r₀ a₀) (u₀ a₀) a₁

            F : R₁ a₀ a₁ ≃ (a₀ == a₁)
            F = fundamental-thm A (R₁ a₀) a₀ (r₁ a₀) (u₁ a₀) a₁

    J₀ : (a₀ : A) (P : Σ A (R₀ a₀) → Type i)
      → (d : P (a₀ , r₀ a₀))
      → (pr : Σ A (R₀ a₀)) → P pr
    J₀ a₀ P d pr = transport P {x = a₀ , r₀ a₀} {y = pr} (contr-has-all-paths ⦃ u₀ a₀ ⦄ (a₀ , r₀ a₀) pr) d

    to : (a₀ a₁ : A) → R₀ a₀ a₁ → R₁ a₀ a₁
    to a₀ a₁ r = J₀ a₀ (λ { (a , _) → R₁ a₀ a }) (r₁ a₀) (a₁ , r)
    
  -- Exactly.  You should probably write out a longer version.  And
  -- actually, this equivalence is not the whole story: to show that
  -- the type of extensions is contractible, you also need to know
  -- that the given equivalence takes r₀ to r₁ and similarly for u₀
  -- to u₁.  I don't think this is a major obstruction.

  -- So, what is the analog of being unital?  I guess that, if we
  -- have a monad M, and a space of fillers for it

  module _ (M : 𝕄) (F : Filler M) (c : has-unique-comps M F) where

    postulate

      unital : {f : Frm M} (τ : Cell M f) → F (η M τ) τ 

   -- Yeah, I see.  So this axiom is missing in general since the
   -- fact that F has compositions doesn't imply that the composition
   -- of η M τ is in fact τ.  Of course, if you do this, it's hard not
   -- to see why you wouldn't also put one for μ.
