{-# OPTIONS --without-K --rewriting --type-in-type --guardedness #-}

open import MiniHoTT
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

  postulate

    fst-η : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → (f : Frm (Σₒ X X↓))
      → η-cns (fst-frm f) ↦ fst-cns (η-cns f) 

  Σₒ {n = O} X X↓ = Σ X X↓
  Σₒ {n = S n} (Xₙ , Xₛₙ) (X↓ₙ , X↓ₛₙ) =
    Σₒ Xₙ X↓ₙ , λ f → Σ (Xₛₙ (fst-frm f)) (λ x → X↓ₛₙ (snd-frm f) x)

  fst-frm {n = O} {X = X} {X↓ = X↓} ⟪ f , P , t ⟫ = 
    ⟪ fst f , P , (λ p → fst (t p)) ⟫
  fst-frm {n = S n} {X = (Xₙ , Xₛₙ)} {X↓ = (X↓ₙ , X↓ₛₙ)} (f , (x , x↓) , fₛₙ) = 
    let fst-op = ⟪ pos (opr fₛₙ) , (λ p → fst-frm (typ (opr fₛₙ) p)) , fst-cns (cns (opr fₛₙ)) ⟫ₒₚ
    in fst-frm f , x , ⟪ fst-op , (λ p → fst (dec fₛₙ p)) ⟫f

  snd-frm {n = O} {X = X} {X↓ = X↓} ⟪ f , P , t ⟫ =
    snd f , λ p → snd (t p)
  snd-frm {n = S n} {X = X} {X↓ = X↓} (f , (x , x↓) , fₛₙ) =
    let snd-op = ⟪ (λ p → snd-frm (typ (opr fₛₙ) p)) , snd-cns (cns (opr fₛₙ)) ⟫ₒₚ↓ 
    in snd-frm f , x↓ , ⟪ snd-op , (λ p → snd (dec fₛₙ p)) ⟫f↓

  fst-cns {n = O} c = tt
  fst-cns {n = S n} {X = Xₙ , Xₛₙ} {X↓ = X↓ₙ , X↓ₛₙ} (lf f (x , x↓)) = {!lf {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} (fst-frm f) x!} -- 
  fst-cns {n = S n} (nd x fₛₙ δ ε) = {!!}


-- Tree Xₙ Xₛₙ
-- (fst-frm f ,
--  x ,
--  ⟪ ⟪ ⊤ₚ , ⊤ₚ-Frm-rec (fst-frm f) , fst-cns (η-cns f) ⟫ₒₚ ,
--  ⊤ₚ-elim (λ p → Xₛₙ (fst-frm f)) x ⟫f)
-- ⊥ₚ ⊥ₚ-Frm-rec


  -- Xₛₙ (typ (η (fst-frm f)) p) !=
  -- Σ (Xₛₙ (fst-frm (typ (η f) p))) (X↓ₛₙ (snd-frm (typ (η f) p))) of

  -- Cns (Xₙ , Xₛₙ) (fst-frm (f , (x , x↓) , η-frm f (x , x↓))) ⊥ₚ
  -- (λ p → fst-frm (⊥ₚ-Frm-rec p))

  -- fst-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
  --   → {f : Frm (Σₒ X X↓)} {P : ℙ} {t : El P → Frm (Σₒ X X↓)}
  --   → (c : Cns (Σₒ X X↓) f P t)
  --   → Cns X (fst-frm f) P (λ p → fst-frm (t p))


  snd-cns = {!!} 
