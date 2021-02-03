{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver

module FreeAlg (M : 𝕄) (X : Idx M → Set) where

  record CnsFreeAlg {i : Idx M} (α : ⟦ M ⟧ X i) (c : Cns M i) : Set where
    constructor ⟦_∥_∥_⟧
    field
      δ-fr : (p : Pos M c) → Cns M (Typ M c p)
      ν-fr : (p : Pos M c) (q : Pos M (δ-fr p)) → X (Typ M (δ-fr p) q)
      -- f-fr : fst α == μ M c δ-fr
      -- o-fr : snd α == (λ p → ν-fr (μ-pos-fst M c δ-fr p) (μ-pos-snd M c δ-fr p)) 
      --        [ (λ x → (p : Pos M x) → X (Typ M x p)) ↓ f-fr ]
      e-fr : α == μ M c δ-fr , λ p → ν-fr (μ-pos-fst M c δ-fr p) (μ-pos-snd M c δ-fr p) 

  open CnsFreeAlg
  
  FreeAlgTyp : {i : Idx M} {α : ⟦ M ⟧ X i} (c : Cns M i)
    → CnsFreeAlg α c
    → (p : Pos M c) → ⟦ M ⟧ X (Typ M c p)
  FreeAlgTyp c cns p = δ-fr cns p , ν-fr cns p 

  -- Free-η↓ : {i : Idx M} (α : ⟦ M ⟧ X i)
  --   → CnsFreeAlg α (η M i)
  -- Free-η↓ (c , ν) = ⟦ η-dec M (Cns M) c ∥ {!!} ∥ {!!} ⟧

  Free-μ↓ : {i : Idx M} {c : Cns M i}
    → {δ : (p : Pos M c) → Cns M (Typ M c p)}
    → {α : ⟦ M ⟧ X i} (c↓ : CnsFreeAlg α c)
    → (δ↓ : (p : Pos M c) → CnsFreeAlg (FreeAlgTyp c c↓ p) (δ p))
    → CnsFreeAlg α (μ M c δ)
  Free-μ↓ {c = c} {δ = δ} ⟦ δ' ∥ ν' ∥ idp ⟧ δ↓ =
    ⟦ (λ p → δ-fr (δ↓ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p)) ∥
      (λ p q → ν-fr (δ↓ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p) q) ∥
      {!!} ⟧

      where claim : δ' == (λ p → μ M (δ p) (λ q → δ-fr (δ↓ p) q))
            claim = λ= (λ p → fst= (e-fr (δ↓ p))) 

  -- Indeed.  So this is essentially the right setup, but naively
  -- strictifying these equations looks dubious.  Well, I guess you
  -- could avoid the funext application by expandng out the actual
  -- equalities necessary here.  Maybe that's a first step....

  -- Gets a bit messy.
