{-# OPTIONS --without-K --rewriting --type-in-type #-}

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

  postulate

    fst-frm-dec : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {P : ℙ} → FrmDec (Σₒ X X↓) P → FrmDec X P 

    fst-frm-dec-app : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {P : ℙ} (d : FrmDec (Σₒ X X↓) P) (p : El P)
      → app (fst-frm-dec d) p ↦ fst-frm (app d p)
    {-# REWRITE fst-frm-dec-app #-} 

    fst-frm-dec-⊥-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → fst-frm-dec {X = X} {X↓ = X↓} ⊥-dec ↦ ⊥-dec
    {-# REWRITE fst-frm-dec-⊥-β #-}
      
    fst-frm-dec-⊤-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → (f : Frm (Σₒ X X↓))
      → fst-frm-dec (⊤-dec f) ↦ ⊤-dec (fst-frm f)
    {-# REWRITE fst-frm-dec-⊤-β #-}

    snd-frm-dec : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {P : ℙ} → (d : FrmDec (Σₒ X X↓) P) → FrmDec↓ X↓ (fst-frm-dec d)

  fst-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm (Σₒ X X↓)} {P : ℙ} {t : FrmDec (Σₒ X X↓) P}
    → (c : Cns (Σₒ X X↓) f P t)
    → Cns X (fst-frm f) P (fst-frm-dec t) 

  snd-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm (Σₒ X X↓)} {P : ℙ} {t : FrmDec (Σₒ X X↓) P} 
    → (c : Cns (Σₒ X X↓) f P t)
    → Cns↓ X↓ (fst-cns c) (snd-frm f) (snd-frm-dec t)

  postulate

    fst-η : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → (f : Frm (Σₒ X X↓))
      → η-cns (fst-frm f) ↦ fst-cns (η-cns f) 
    {-# REWRITE fst-η #-}

  Σₒ {n = O} X X↓ = Σ X X↓
  Σₒ {n = S n} (Xₙ , Xₛₙ) (X↓ₙ , X↓ₛₙ) =
    Σₒ Xₙ X↓ₙ , λ f → Σ (Xₛₙ (fst-frm f)) (λ x → X↓ₛₙ (snd-frm f) x)

  -- So, it looks like what is happening is that in the last clause,
  -- the abstraction (λ p → fst (t p)) is getting instantiated with
  -- t and eliminator.  But we don't get that this commutes with fst
  -- and so we're stuck.  Hmmm.

  -- So again, this could be solved with exactly the same idea: the
  -- decorations are algebraic data and we can have algebraic projection
  -- operators which extract the relevant data from them.

  -- Shit.  I thought we would get away without needing that ....

  fst-frm {n = O} {X = X} {X↓ = X↓} (f , P , t) = 
    (fst f , P , (λ p → fst (t p)))
  fst-frm {n = S n} {X = (Xₙ , Xₛₙ)} {X↓ = (X↓ₙ , X↓ₛₙ)} (f , (x , x↓) , fₛₙ) = 
    let fst-op = ⟪ pos (opr fₛₙ) , fst-frm-dec (typ (opr fₛₙ)) , fst-cns (cns (opr fₛₙ)) ⟫ₒₚ 
    in fst-frm f , x , ⟪ fst-op , (λ p → fst (dec fₛₙ p)) ⟫f

  snd-frm {n = O} {X = X} {X↓ = X↓} (f , P , t) = 
    snd f , λ p → snd (t p)
  snd-frm {n = S n} {X = X} {X↓ = X↓} (f , (x , x↓) , fₛₙ) = {!!} 
    -- let snd-op = ⟪ (λ p → snd-frm (typ (opr fₛₙ) p)) , snd-cns (cns (opr fₛₙ)) ⟫ₒₚ↓ 
    -- in snd-frm f , x↓ , ⟪ snd-op , (λ p → snd (dec fₛₙ p)) ⟫f↓

  fst-cns {n = O} c = tt
  fst-cns {n = S n} {X = Xₙ , Xₛₙ} {X↓ = X↓ₙ , X↓ₛₙ} (lf f (x , x↓)) =
    {!lf {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} (fst-frm f) x!} 

  fst-cns {n = S n} (nd x fₛₙ δ ε) = {!!}

  snd-cns = {!!} 
