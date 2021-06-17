{-# OPTIONS --without-K --rewriting #-}

open import Prelude
open import MiniUniverse
open import AbsoluteOpetopicTypes
open import DependentOpetopicType

module Sigma where

  Σₒ : ∀ {ℓ ℓ↓} {n : ℕ} (X : 𝕆 ℓ n) (X↓ : 𝕆↓ ℓ↓ X) → 𝕆 (ℓ-max ℓ ℓ↓) n

  fst-frm : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → Frm (Σₒ X X↓) → Frm X

  snd-frm : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → (f : Frm (Σₒ X X↓)) → Frm↓ X↓ (fst-frm f)

  fst-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm (Σₒ X X↓)} {P : ℙ} {t : El P → Frm (Σₒ X X↓)}
    → (c : Cns (Σₒ X X↓) f P t)
    → Cns X (fst-frm f) P (λ p → fst-frm (t p))

  snd-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm (Σₒ X X↓)} {P : ℙ} {t : El P → Frm (Σₒ X X↓)}
    → (c : Cns (Σₒ X X↓) f P t)
    → Cns↓ X↓ (fst-cns c) (snd-frm f) (λ p → snd-frm (t p))

  Σₒ {n = O} X X↓ = Σ X X↓
  Σₒ {n = S n} (Xₙ , Xₛₙ) (X↓ₙ , X↓ₛₙ) =
    Σₒ Xₙ X↓ₙ , λ f → Σ (Xₛₙ (fst-frm f)) (λ x → X↓ₛₙ (snd-frm f) x)

  fst-frm {n = O} {X = X} {X↓ = X↓} ⟪ f , P , t ⟫ =
    ⟪ fst f , P , (λ p → fst (t p)) ⟫
  fst-frm {n = S n} {X = (Xₙ , Xₛₙ)} {X↓ = (X↓ₙ , X↓ₛₙ)} (f , (x , x↓) , xₛₙ) =
    let fst-op = ⟪ pos (opr xₛₙ) , (λ p → fst-frm (typ (opr xₛₙ) p)) , fst-cns (cns (opr xₛₙ)) ⟫ₒₚ
    in fst-frm f , x , ⟪ fst-op , (λ p → fst (dec xₛₙ p)) ⟫f

  snd-frm {n = O} {X = X} {X↓ = X↓} ⟪ f , P , t ⟫ =
    snd f , λ p → snd (t p)
  snd-frm {n = S n} {X = X} {X↓ = X↓} (f , (x , x↓) , xₛₙ) =
    let snd-op = ⟪ (λ p → snd-frm (typ (opr xₛₙ) p)) , snd-cns (cns (opr xₛₙ)) ⟫ₒₚ↓ 
    in snd-frm f , x↓ , ⟪ snd-op , (λ p → snd (dec xₛₙ p)) ⟫f↓

  fst-cns {n = O} c = tt
  fst-cns {n = S n} (lf f (x , x↓)) = {!lf (fst-frm f) x!}
  fst-cns {n = S n} (nd x fₛₙ δ ε) = {!!}

  --
  -- So, fundamentally, we don't have:
  --   frm-frm (⊤ₚ-Frm-rec f p) =/= ⊤ₚ-Frm-rec (fst-frm f) p
  --

  -- So I guess this would be solved by η-expansion in the mini
  -- universe.

  -- Hmmm.  But even after η-expansion we need:
  -- η-cns (fst-frm f) = fst-cns (η-cns f)

  -- Shit.  I thought we would get everything we needed.
  -- Okay, going to have to think more about this....

  snd-cns = {!!} 
