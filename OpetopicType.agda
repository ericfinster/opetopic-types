{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import PiUniverse

module OpetopicType where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ

  postulate 

    Cns : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (f : Frm X) (P : ℙ) (t : πₚ P (cst (Frm X)))
      → Set ℓ

  record Opr {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (f : Frm X) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_,_⟫ₒₚ
    field
      pos : ℙ
      typ : πₚ pos (cst (Frm X))
      cns : Cns X f pos typ

  open Opr public

  record Frmₛ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} (Xₛₙ : Frm Xₙ → Set ℓ) (f : Frm Xₙ) (x : Xₛₙ f) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫f
    field
      opr : Opr Xₙ f
      dec : πₚ (pos opr) (λ p → Xₛₙ (app (typ opr) p))
      
  open Frmₛ public

  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ X → (f : Frm X) → Set ℓ)

  Frm {n = O} X = Σ X (λ x → Σ ℙ (λ P → πₚ P (cst X)))
  Frm {n = S n} (Xₙ , Xₛₙ) = Σ (Frm Xₙ) (λ f → Σ (Xₛₙ f) (λ x → Frmₛ Xₛₙ f x))

  postulate

    obj : ∀ {ℓ} {X : Set ℓ}
      → (x : X) {P : ℙ} (δ : πₚ P (cst X))
      → Cns {n = O} X (x , P , δ) {!!} {!!}


