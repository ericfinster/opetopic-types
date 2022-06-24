{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicFamily.agda - Opetopic Families (dependent opetopic types)
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType

module Experimental.NoDecs.OpetopicFamily where

--
--  Opetopic families
--

𝕆Fam : ∀ {n ℓ₀} (X : 𝕆Type n ℓ₀) (ℓ : Level) → Type (ℓ-max ℓ₀ (ℓ-suc ℓ))

Frm↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (X↓ : 𝕆Fam X ℓ) (f : Frm X) → Type ℓ

Src↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
  {X↓ : 𝕆Fam X ℓ} (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ) {f : Frm X} (f↓ : Frm↓ X↓ f) (s : Src P f) → Type ℓ

Typ↓ : ∀ {n ℓ₀ ℓ}
  {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
  {X↓ : 𝕆Fam X ℓ} (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
  {f : Frm X} {f↓ : Frm↓ X↓ f}
  {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
  (p : Pos P s) → Frm↓ X↓ (Typ P s p)

_⊚↓_ : ∀ {n ℓ₀ ℓ}
  {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
  {X↓ : 𝕆Fam X ℓ} {P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ}
  {f : Frm X} {f↓ : Frm↓ X↓ f}
  {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
  (p : Pos P s)
  → P↓ (Typ↓ P↓ s↓ p) (s ⊚ p)

--
-- Maps of Opetopic Types
--

infixl 50 _⊙↓_

_⇒[_]_ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} → 𝕆Fam X ℓ → (X ⇒ Y) → 𝕆Fam Y ℓ → Type (ℓ-max ℓ₀ ℓ)

id-map↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (X↓ : 𝕆Fam X ℓ) → X↓ ⇒[ id-map X ] X↓

_⊙↓_ : ∀ {n ℓ₀ ℓ} {X Y Z : 𝕆Type n ℓ₀}
  {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ} {Z↓ : 𝕆Fam Z ℓ}
  {σ : Y ⇒ Z} {σ' : X ⇒ Y}
  → (Y↓ ⇒[ σ ] Z↓) → (X↓ ⇒[ σ' ] Y↓) → (X↓ ⇒[ σ ⊙ σ' ] Z↓)

Frm↓⇒ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} {σ : X ⇒ Y}
  {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ} (σ↓ : X↓ ⇒[ σ ] Y↓)
  {f : Frm X} (f↓ : Frm↓ X↓ f)
  → Frm↓ Y↓ (Frm⇒ σ f)

--
--  Monadic Structure
--

η↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀} {X↓ : 𝕆Fam X ℓ}
   → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
   → {f : Frm X} {f↓ : Frm↓ X↓ f} {x : P f} (x↓ : P↓ f↓ x)
   → Src↓ {X↓ = X↓} P↓ f↓ (η P x)

postulate
  μ↓ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} {σ : X ⇒ Y}
    → {P : Frm X → Type ℓ₀} {Q : Frm Y → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ}
    → (σ↓ : X↓ ⇒[ σ ] Y↓)
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm Y} (f↓ : Frm↓ Y↓ f) → Q f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
    → {ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p))}
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Frm↓⇒ σ↓ (Typ↓ P↓ s↓ p)) (ϕ p))
    → Src↓ Q↓ (Frm↓⇒ σ↓ f↓) (μ σ P Q s ϕ)


--
--  Equational Structure (updated as needed)
--

postulate
  --
  --  Laws for maps
  --

  Frm↓⇒-id : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (X↓ : 𝕆Fam X ℓ)
    → {f : Frm X} (f↓ : Frm↓ X↓ f)
    → Frm↓⇒ (id-map↓ X↓) f↓ ↦ f↓
  {-# REWRITE Frm↓⇒-id #-}

  Frm↓⇒-⊙ : ∀ {n ℓ₀ ℓ} {X Y Z : 𝕆Type n ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ} {Z↓ : 𝕆Fam Z ℓ}
    → {σ : Y ⇒ Z} {σ' : X ⇒ Y}
    → (σ↓ : Y↓ ⇒[ σ ] Z↓) (σ↓' : X↓ ⇒[ σ' ] Y↓)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → Frm↓⇒ (σ↓ ⊙↓ σ↓') f↓ ↦ Frm↓⇒ σ↓ (Frm↓⇒ σ↓' f↓)
  {-# REWRITE Frm↓⇒-⊙ #-}

  map-unit-l↓ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ}
    → {σ : X ⇒ Y}
    → (σ↓ : X↓ ⇒[ σ ] Y↓)
    → id-map↓ Y↓ ⊙↓ σ↓ ↦ σ↓
  {-# REWRITE map-unit-l↓ #-}

  map-unit-r↓ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ}
    → {σ : X ⇒ Y}
    → (σ↓ : X↓ ⇒[ σ ] Y↓)
    → σ↓ ⊙↓ id-map↓ X↓ ↦ σ↓
  {-# REWRITE map-unit-r↓ #-}

  map-assoc↓ : ∀ {n ℓ₀ ℓ} {X Y Z W : 𝕆Type n ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ} {Z↓ : 𝕆Fam Z ℓ} {W↓ : 𝕆Fam W ℓ}
    → {σ : Z ⇒ W} {σ' : Y ⇒ Z} {σ'' : X ⇒ Y}
    → (σ↓ : Z↓ ⇒[ σ ] W↓) (σ↓' : Y↓ ⇒[ σ' ] Z↓) (σ↓'' : X↓ ⇒[ σ'' ] Y↓)
    → σ↓ ⊙↓ (σ↓' ⊙↓ σ↓'') ↦ σ↓ ⊙↓ σ↓' ⊙↓ σ↓''
  {-# REWRITE map-assoc↓ #-}


  --
  --  Laws for types and inhabitants
  --

  -- Typing and inhabitants of μ and η
  Typ-η↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀} {X↓ : 𝕆Fam X ℓ}
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f} {x : P f} (x↓ : P↓ f↓ x)
    → (p : Pos P (η P x))
    → Typ↓ P↓ (η↓ P↓ x↓) p ↦ f↓
  {-# REWRITE Typ-η↓ #-}

  Typ-μ↓ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} {σ : X ⇒ Y}
    → {P : Frm X → Type ℓ₀} {Q : Frm Y → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ}
    → (σ↓ : X↓ ⇒[ σ ] Y↓)
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm Y} (f↓ : Frm↓ Y↓ f) → Q f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
    → {ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p))}
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Frm↓⇒ σ↓ (Typ↓ P↓ s↓ p)) (ϕ p))
    → (p : Pos Q (μ σ P Q s ϕ))
    → Typ↓ Q↓ (μ↓ σ↓ P↓ Q↓ s↓ ϕ↓) p ↦ Typ↓ Q↓ (ϕ↓ (μ-fst σ P Q s ϕ p)) (μ-snd σ P Q s ϕ p)
  {-# REWRITE Typ-μ↓ #-}

  Typ-μ-idmap↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀}
    → {P Q : Frm X → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ}
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → Q f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
    → {ϕ : (p : Pos P s) → Src Q (Frm⇒ (id-map X) (Typ P s p))}
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Frm↓⇒ (id-map↓ X↓) (Typ↓ P↓ s↓ p)) (ϕ p))
    → (p : Pos Q (μ (id-map X) P Q s ϕ))
    → Typ↓ Q↓ (μ↓ (id-map↓ X↓) P↓ Q↓ s↓ ϕ↓) p ↦ Typ↓ Q↓ (ϕ↓ (μ-fst (id-map X) P Q s ϕ p)) (μ-snd (id-map X) P Q s ϕ p)
  {-# REWRITE Typ-μ-idmap↓ #-}

  ⊚-η↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀} {X↓ : 𝕆Fam X ℓ}
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f} {x : P f} (x↓ : P↓ f↓ x)
    → (p : Pos P (η P x))
    → η↓ P↓ x↓ ⊚↓ p ↦ x↓
  {-# REWRITE ⊚-η↓ #-}

  ⊚-μ↓ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} {σ : X ⇒ Y}
    → {P : Frm X → Type ℓ₀} {Q : Frm Y → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ}
    → (σ↓ : X↓ ⇒[ σ ] Y↓)
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm Y} (f↓ : Frm↓ Y↓ f) → Q f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
    → {ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p))}
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Frm↓⇒ σ↓ (Typ↓ P↓ s↓ p)) (ϕ p))
    → (p : Pos Q (μ σ P Q s ϕ))
    → μ↓ σ↓ P↓ Q↓ s↓ ϕ↓ ⊚↓ p ↦ (ϕ↓ (μ-fst σ P Q s ϕ p) ⊚↓ μ-snd σ P Q s ϕ p)
  {-# REWRITE ⊚-μ↓ #-}

  ⊚-μ-idmap↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀}
    → {P Q : Frm X → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ}
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → Q f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
    → {ϕ : (p : Pos P s) → Src Q (Frm⇒ (id-map X) (Typ P s p))}
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Frm↓⇒ (id-map↓ X↓) (Typ↓ P↓ s↓ p)) (ϕ p))
    → (p : Pos Q (μ (id-map X) P Q s ϕ))
    → μ↓ (id-map↓ X↓) P↓ Q↓ s↓ ϕ↓ ⊚↓ p ↦ (ϕ↓ (μ-fst (id-map X) P Q s ϕ p) ⊚↓ μ-snd (id-map X) P Q s ϕ p)
  {-# REWRITE ⊚-μ-idmap↓ #-}

  --
  --  Monad laws
  --
  μ↓-unit-l : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} {σ : X ⇒ Y}
    → {P : Frm X → Type ℓ₀} {Q : Frm Y → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {Y↓ : 𝕆Fam Y ℓ}
    → (σ↓ : X↓ ⇒[ σ ] Y↓)
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm Y} (f↓ : Frm↓ Y↓ f) → Q f → Type ℓ)
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {x : P f} (x↓ : P↓ f↓ x)
    → {ϕ : (p : Pos P (η P x)) → Src Q (Frm⇒ σ f)}
    → (ϕ↓ : (p : Pos P (η P x)) → Src↓ Q↓ (Frm↓⇒ σ↓ f↓) (ϕ p))
    → μ↓ σ↓ P↓ Q↓ (η↓ P↓ x↓) ϕ↓ ↦ ϕ↓ (η-pos P x)
  {-# REWRITE μ↓-unit-l #-}

  μ↓-unit-r : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
    → {X↓ : 𝕆Fam X ℓ} {P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ}
    → {f : Frm X} {f↓ : Frm↓ X↓ f}
    → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
    → μ↓ (id-map↓ X↓) P↓ P↓ s↓ (λ p → η↓ P↓ (s↓ ⊚↓ p)) ↦ s↓
  {-# REWRITE μ↓-unit-r #-}
  
  μ↓-assoc : ∀ {n ℓ₀ ℓ} {X Y Z : 𝕆Type n ℓ₀}
    → (P : Frm X → Type ℓ₀) (Q : Frm Y → Type ℓ₀) (R : Frm Z → Type ℓ₀)
    → (σ : X ⇒ Y) (τ : Y ⇒ Z) 
    → (f : Frm X) (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
    → (ψ : (pq : Pos Q (μ σ P Q s ϕ)) → Src R (Frm⇒ τ (Typ Q (μ σ P Q s ϕ) pq)))
    → (X↓ : 𝕆Fam X ℓ) (Y↓ : 𝕆Fam Y ℓ) (Z↓ : 𝕆Fam Z ℓ)
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm Y} (f↓ : Frm↓ Y↓ f) → Q f → Type ℓ)
    → (R↓ : {f : Frm Z} (f↓ : Frm↓ Z↓ f) → R f → Type ℓ)
    → (σ↓ : X↓ ⇒[ σ ] Y↓) (τ↓ : Y↓ ⇒[ τ ] Z↓) 
    → (f↓ : Frm↓ X↓ f) (s↓ : Src↓ P↓ f↓ s)
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Frm↓⇒ σ↓ (Typ↓ P↓ s↓ p)) (ϕ p))
    → (ψ↓ : (pq : Pos Q (μ σ P Q s ϕ)) → Src↓ R↓ (Frm↓⇒ τ↓ (Typ↓ Q↓ (μ↓ σ↓ P↓ Q↓ s↓ ϕ↓) pq)) (ψ pq))
    → μ↓ τ↓ Q↓ R↓ (μ↓ σ↓ P↓ Q↓ s↓ ϕ↓) ψ↓ ↦ μ↓ (τ↓ ⊙↓ σ↓) P↓ R↓ s↓ λ p → μ↓ τ↓ Q↓ R↓ (ϕ↓ p) (λ q → ψ↓ (μ-pos σ P Q s ϕ p q))
  {-# REWRITE μ↓-assoc #-}

  μ↓-assoc-idmap-l : ∀ {n ℓ₀ ℓ} {X Z : 𝕆Type n ℓ₀}
    → (P : Frm X → Type ℓ₀) (Q : Frm X → Type ℓ₀) (R : Frm Z → Type ℓ₀)
    → (τ : X ⇒ Z) 
    → (f : Frm X) (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
    → (ψ : (pq : Pos Q (μ (id-map X) P Q s ϕ)) → Src R (Frm⇒ τ (Typ Q (μ (id-map X) P Q s ϕ) pq)))
    → (X↓ : 𝕆Fam X ℓ) (Z↓ : 𝕆Fam Z ℓ)
    → (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
    → (Q↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → Q f → Type ℓ)
    → (R↓ : {f : Frm Z} (f↓ : Frm↓ Z↓ f) → R f → Type ℓ)
    → (τ↓ : X↓ ⇒[ τ ] Z↓) 
    → (f↓ : Frm↓ X↓ f) (s↓ : Src↓ P↓ f↓ s)
    → (ϕ↓ : (p : Pos P s) → Src↓ Q↓ (Typ↓ P↓ s↓ p) (ϕ p))
    → (ψ↓ : (pq : Pos Q (μ (id-map X) P Q s ϕ)) → Src↓ R↓ (Frm↓⇒ τ↓ (Typ↓ Q↓ (μ↓ (id-map↓ X↓) P↓ Q↓ s↓ ϕ↓) pq)) (ψ pq))
    → μ↓ τ↓ Q↓ R↓ (μ↓ (id-map↓ X↓) P↓ Q↓ s↓ ϕ↓) ψ↓ ↦ μ↓ τ↓ P↓ R↓ s↓ λ p → μ↓ τ↓ Q↓ R↓ (ϕ↓ p) (λ q → ψ↓ (μ-pos (id-map X) P Q s ϕ p q))
  {-# REWRITE μ↓-assoc-idmap-l #-}

--
--  Definitions of opetopic families and frames
𝕆Fam {zero} X ℓ = Lift Unit
𝕆Fam {suc n} (X ,  P) ℓ = Σ[ X↓ ∈ (𝕆Fam X ℓ) ] ({f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)

Frm↓ {zero} X↓ f = Lift Unit
Frm↓ {suc n} (X↓ , P↓) (f , s , t) = Σ[ f↓ ∈ Frm↓ X↓ f ] Σ[ s↓ ∈ Src↓ P↓ f↓ s ] P↓ f↓ t

--
--  Pasting diagrams
--

module _ {n ℓ₀ ℓ}
  {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀} {U : Frm (X , P) → Type ℓ₀}
  {X↓ : 𝕆Fam X ℓ} {P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ}
  (U↓ : {f : Frm (X , P)} (f↓ : Frm↓ (X↓ , P↓) f) → U f → Type ℓ)
  where

  Pd↓ : {f : Frm (X , P)} (f↓ : Frm↓ (X↓ , P↓) f) → Src U f → Type ℓ

  record Branch↓ {f : Frm X} (f↓ : Frm↓ X↓ f) (b : Branch U f) : Type ℓ where
    inductive
    eta-equality
    constructor [_,_,_]↓
    field
      stm↓ : P↓ f↓ (stm b)
      lvs↓ : Src↓ P↓ f↓ (lvs b)
      br↓ : Pd↓ (f↓ , lvs↓ , stm↓) (br b)
  open Branch↓ public

  data PdLf↓ {f : Frm X} {x : P f} : (f↓ : Frm↓ (X↓ , P↓) (f , η P x , x)) → Type ℓ where
    lf↓ : {f↓ : Frm↓ X↓ f} (x↓ : P↓ f↓ x) → PdLf↓ (f↓ , η↓ P↓ x↓ , x↓)

  data PdNd↓ {f : Frm X} {tgt : P f} {brs : Src (Branch U) f}
             {flr : U (f , μ (id-map X) (Branch U) P brs (λ p → η P (stm (brs ⊚ p))) , tgt)}
             : (f↓ : Frm↓ (X↓ , P↓) (f , μ (id-map X) (Branch U) P brs (λ p → lvs (brs ⊚ p)) , tgt)) → Type ℓ where
    nd↓ : {f↓ : Frm↓ X↓ f} (tgt↓ : P↓ f↓ tgt) (brs↓ : Src↓ Branch↓ f↓ brs)
          (flr↓ : U↓ (f↓ , μ↓ (id-map↓ X↓) Branch↓ P↓ brs↓ (λ p → η↓ P↓ (stm↓ (brs↓ ⊚↓ p))) , tgt↓) flr)
          → PdNd↓ (f↓ , μ↓ (id-map↓ X↓) Branch↓ P↓ brs↓ (λ p → lvs↓ (brs↓ ⊚↓ p)) , tgt↓)

  Pd↓ f↓ (lf tgt) = PdLf↓ f↓
  Pd↓ f↓ (nd tgt brs flr) = PdNd↓ {brs = brs} {flr = flr} f↓

  PdTyp↓ : {f : Frm (X , P)} {f↓ : Frm↓ (X↓ , P↓) f} {s : Src U f}
    (pd : Pd↓ f↓ s) (p : Pos U s)
    → Frm↓ (X↓ , P↓) (Typ U s p)
  PdTyp↓ (nd↓ {f↓ = f↓} tgt↓ brs↓ flr↓) nd-here = f↓ , μ↓ (id-map↓ X↓) Branch↓ P↓ brs↓ (λ p → η↓ P↓ (stm↓ (brs↓ ⊚↓ p))) , tgt↓
  PdTyp↓ (nd↓ tgt↓ brs↓ flr↓) (nd-there p q) = PdTyp↓ (br↓ (brs↓ ⊚↓ p)) q

  PdInhab↓ : {f : Frm (X , P)} {f↓ : Frm↓ (X↓ , P↓) f} {s : Src U f}
    (pd : Pd↓ f↓ s) (p : Pos U s) → U↓ (PdTyp↓ pd p) (PdInhab U s p)
  PdInhab↓ (nd↓ tgt↓ brs↓ flr↓) nd-here = flr↓
  PdInhab↓ (nd↓ tgt↓ brs↓ flr↓) (nd-there p q) = PdInhab↓ (br↓ (brs↓ ⊚↓ p)) q

  --γ↓ : ?


Src↓ {zero} P↓ f↓ s = P↓ f↓ s
Src↓ {suc n} P↓ f↓ s = Pd↓ P↓ f↓ s

Typ↓ {zero} P↓ s↓ p = tt*
Typ↓ {suc n} = PdTyp↓

_⊚↓_ {zero} x p = x
_⊚↓_ {suc n} {P↓ = P↓} = PdInhab↓ P↓

_⇒[_]_ {zero} X↓ σ Y↓ = Lift Unit
_⇒[_]_ {suc n} {X = X , P} {Y = Y , Q} (X↓ , P↓) (σ , σₛ) (Y↓ , Q↓) =
  Σ[ σ↓ ∈ X↓ ⇒[ σ ] Y↓ ]
  ({f : Frm X} {f↓ : Frm↓ X↓ f} {x : P f} → P↓ f↓ x → Q↓ (Frm↓⇒ σ↓ f↓) (σₛ x))

Frm↓⇒ {zero} σ↓ f↓ = tt*
Frm↓⇒ {suc n} {Y↓ = Y↓ , Q↓} (σ↓ , σₛ↓) (f↓ , s↓ , t↓) = Frm↓⇒ σ↓ f↓ , μ↓ σ↓ _ _ s↓ (λ p → η↓ Q↓ (σₛ↓ (s↓ ⊚↓ p))) , σₛ↓ t↓

id-map↓ {zero} X↓ = tt*
id-map↓ {suc n} (X↓ , P↓) = id-map↓ X↓ , λ x → x

_⊙↓_ {zero} σ↓ σ'↓ = tt*
_⊙↓_ {suc n} (σ↓ , σₛ) (σ↓' , σₛ') = σ↓ ⊙↓ σ↓' , λ x↓ → σₛ (σₛ' x↓)

η↓ {zero} P↓ x↓ = x↓
η↓ {suc n} {X↓ = X↓ , P↓} U↓ {f↓ = f↓ , s↓ , t↓} x↓ =
  let brs = μ↓ (id-map↓ X↓) P↓ (Branch↓ U↓) s↓ (λ p → η↓ (Branch↓ U↓) [ s↓ ⊚↓ p , η↓ P↓ (s↓ ⊚↓ p) , lf↓ (s↓ ⊚↓ p) ]↓)
  in nd↓ t↓ brs x↓

_⇛[_]_ : ∀ {n ℓ₀ ℓ} (X : 𝕆Type n ℓ₀) {Y : 𝕆Type n ℓ₀} → (X ⇒ Y) → 𝕆Fam Y ℓ → Type (ℓ-max ℓ₀ ℓ)

postulate
  Frm⇛ : ∀ {n ℓ₀ ℓ} {X Y : 𝕆Type n ℓ₀} {σ : X ⇒ Y}
    {Y↓ : 𝕆Fam Y ℓ} (σ↓ : X ⇛[ σ ] Y↓)
    (f : Frm X)
    → Frm↓ Y↓ (Frm⇒ σ f)

_⇛[_]_ {zero} X σ Y↓ = Lift Unit
_⇛[_]_ {suc n} (X , P) (σ , σₛ) (Y↓ , Q↓) = Σ[ σ↓ ∈ (X ⇛[ σ ] Y↓)] ({f : Frm X} (x : P f) → Q↓ (Frm⇛ σ↓ f) (σₛ x))
