{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver

module Pi where

  -- Is there a dependent product of monads over?
  Frm-Π : (M : 𝕄) (M↓ : 𝕄↓ M) → Set
  Frm-Π M M↓ = (f : Frm M) → Frm↓ M↓ f

  Tree-Π : (M : 𝕄) (M↓ : 𝕄↓ M)
    (f : Frm-Π M M↓) → Set
  Tree-Π M M↓ ϕ = (f : Frm M) (σ : Tree M f) → Tree↓ M↓ (ϕ f) σ 

  Pos-Π : (M : 𝕄) (M↓ : 𝕄↓ M)
    → (f : Frm-Π M M↓) (σ : Tree-Π M M↓ f)
    → Set
  Pos-Π M M↓ ϕ ψ = (f : Frm M) → Σ (Tree M f) (λ σ → Pos M σ)

  Typ-Π : (M : 𝕄) (M↓ : 𝕄↓ M)
    → (f : Frm-Π M M↓) (σ : Tree-Π M M↓ f)
    → (p : Pos-Π M M↓ f σ) → Frm-Π M M↓
  Typ-Π M M↓ ϕ ψ χ f = {!Typ↓ M↓ (ϕ f) (ψ f σ) p!}

    where σ : Tree M f
          σ = fst (χ f)

          p : Pos M σ
          p = snd (χ f)


  -- Frm-Π : (M : 𝕄) (M↓ : 𝕄↓ M) → Set
  -- Frm-Π M M↓ = Frm M
  
  -- Tree-Π : (M : 𝕄) (M↓ : 𝕄↓ M)
  --   (f : Frm-Π M M↓) → Set
  -- Tree-Π M M↓ f = (f↓ : Frm↓ M↓ f) (σ : Tree M f) → Tree↓ M↓ f↓ σ

  -- Pos-Π : (M : 𝕄) (M↓ : 𝕄↓ M)
  --   → (f : Frm-Π M M↓) (σ : Tree-Π M M↓ f)
  --   → Set
  -- Pos-Π M M↓ f ϕ = {!!}

  -- Typ-Π : (M : 𝕄) (M↓ : 𝕄↓ M)
  --   → (f : Frm-Π M M↓) (σ : Tree-Π M M↓ f)
  --   → (p : Pos-Π M M↓ f σ) → Frm-Π M M↓
  -- Typ-Π M M↓ f ϕ p = {!!}


  -- Hmmm.  But if this doesn't seem to be working, how does one
  -- define the opetopic type of sections, which you have seen from
  -- other work, definitely works ...

  -- Perhaps it relies on the following observation: given just the
  -- data of an extension of *polynomials*, it need not be the case
  -- that the total space is a monad.  But it's *slice* is always a
  -- monad.  So if you pass to taking a space of sections, you
  -- probably have to compensate with a slice in order to have a
  -- monad again ...
