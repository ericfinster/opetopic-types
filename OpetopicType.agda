{-# OPTIONS --without-K --rewriting #-}

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

  -- These should be reindexed to start at -1 ...
  𝕆 ℓ O = ⊤ 
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ X → (f : Frm X) → Set ℓ)

  Frm {n = O} X = ⊤
  Frm {n = S n} (Xₙ , Xₛₙ) =
    Σ (Frm Xₙ) (λ f →
    Σ (Xₛₙ f) (λ x → 
    Σ ℙ (λ P →
    Σ (πₚ P (cst (Frm Xₙ))) (λ δf →
    Σ (πₚ P (λ p → Xₛₙ (app δf p))) (λ δx → 
    Cns Xₙ f P δf)))))

  postulate

    η-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
      → Cns X f ⊤ₚ (π-⊤ (cst (Frm X)) f)

    μ-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {f : Frm X} (c : Opr X f)
      → (δ : πₚ (pos c) (λ p → Opr X (app (typ c) p)))
      → Cns X f (Σₚ (pos c) {!!})
          {!!}


    -- the trivial object constructor...
    obj : ∀ {ℓ} (P : ℙ) → Cns {ℓ = ℓ} {n = O} tt tt P (cstₚ P tt)




