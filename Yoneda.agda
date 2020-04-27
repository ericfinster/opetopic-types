{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import OpetopicType

module Yoneda where

  module _ {i} (A : Type i) where

    rep : (a : A) → A → Type i
    rep a b = a == b

    nat-trans : (P Q : A → Type i) → Type i
    nat-trans P Q = (a : A) → P a → Q a

    nat-is-nat : (P Q : A → Type i)
      → (ϕ : (a : A) → P a → Q a)
      → {a₀ a₁ : A} (p : a₀ == a₁)
      → (x : P a₀)
      → (ϕ a₁ ∘ transport P p) x == (transport Q p ∘ ϕ a₀) x
    nat-is-nat P Q ϕ idp x = idp

  module _ {M : 𝕄} (F G : Filler M) where

    filler-trans : Set
    filler-trans = {f : Frm M} (σ : Tree M f) (τ : Cell M f)
      → F σ τ → G σ τ

    -- Okay.  So it clearly makes sense to ask if this is
    -- "natural in τ".  And of course, it will be if we take
    -- paths between cells.

    -- Let's see. Another natural condition is the one that
    -- came up in thinking about opetopictt, which is that
    -- path-overs in the fibration of fillers are commutative
    -- triangles.

    -- But isn't this condition satisfied automatically? 



  -- module _ {i} {M : 𝕄} (F : Filler M) (uc : has-unique-comps M F) where

  --   mnd-trans : (P Q : {f : Frm M} (σ : Tree M f) → Type i) → Type i
  --   mnd-trans P Q = {f : Frm M} (σ : Tree M f) → P σ → Q σ

  --   mnd-transport : (P : {f : Frm M} (σ : Tree M f) → Type i)
  --     → {f : Frm M} (σ : Tree M f) (τ : Cell M f) (θ : F σ τ)
  --     → P σ → P (η M τ)
  --   mnd-transport P σ τ θ p = {!!}

  --   -- Yeah, this doesn't even typecheck.  What if we actually
  --   -- try to keep the two variables and ask for someone who
  --   -- is, say, natural in one of them


  --   mnd-is-natural : (P Q : {f : Frm M} (σ : Tree M f) → Type i)
  --     → (ϕ : mnd-trans P Q)
  --     → {f : Frm M} (σ : Tree M f) (τ : Cell M f) (θ : F σ τ)
  --     → (x : P σ)
  --     → {!!}
  --   mnd-is-natural = {!!}
