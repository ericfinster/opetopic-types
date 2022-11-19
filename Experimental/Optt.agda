--
--  Optt - Some ideas about opetopic type theory
--

open import Core.Prelude

module Experimental.Optt where

  Frm : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ 
  Pd : ∀ {ℓ} (n : ℕ) (A : Type ℓ) 
    → Frm n A → Type ℓ 

  postulate

    Cell : ∀ {ℓ} (n : ℕ) (A : Type ℓ) 
      → Frm n A → Type ℓ 

  Frm {ℓ} zero A = 𝟙 ℓ
  Frm (suc n) A =
    Σ[ f ∈ Frm n A ]
    Σ[ ρ ∈ Pd n A f ]
    Cell n A f

  Pd zero A  u = A
  Pd (suc n) A (f , s , t) = {!!}

  -- Terms.

  postulate
    frm : ∀ {ℓ} (n : ℕ) (A : Type ℓ)
      → A → Frm n A
    pd : ∀ {ℓ} (n : ℕ) (A : Type ℓ)
      → (a : A) → Pd n A (frm n A a)
    refl : ∀ {ℓ} (n : ℕ) (A : Type ℓ)
      → (a : A) → Cell n A (frm n A a)
  
