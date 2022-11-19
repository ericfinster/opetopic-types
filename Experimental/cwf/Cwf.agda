{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.cwf.Cwf where


  --
  --  Opetopic Types
  --

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)

  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  postulate

    Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → Frm X → Type ℓ

    Pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ 

    Typ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s) → Frm X 

    _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s)
      → P (Typ P s p)

    --
    --  Opetopic Families
    --

    𝕆Fam : ∀ {n ℓ₀} (X : 𝕆Type n ℓ₀)
      → (ℓ : Level) → Type (ℓ-max ℓ₀ (ℓ-suc ℓ))

    Frm↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (X↓ : 𝕆Fam X ℓ)
      → (f : Frm X) → Type ℓ

    Src↓ : ∀ {n ℓ₀ ℓ}
      → {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
      → {X↓ : 𝕆Fam X ℓ} (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
      → {f : Frm X} (f↓ : Frm↓ X↓ f) (s : Src P f)
      → Type ℓ

    Typ↓ : ∀ {n ℓ₀ ℓ}
      → {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
      → {X↓ : 𝕆Fam X ℓ} (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
      → {f : Frm X} {f↓ : Frm↓ X↓ f}
      → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
      → (p : Pos P s) → Frm↓ X↓ (Typ P s p)

    _⊚↓_ : ∀ {n ℓ₀ ℓ}
      → {X : 𝕆Type n ℓ₀} {P : Frm X → Type ℓ₀}
      → {X↓ : 𝕆Fam X ℓ} {P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ}
      → {f : Frm X} {f↓ : Frm↓ X↓ f}
      → {s : Src P f} (s↓ : Src↓ P↓ f↓ s)
      → (p : Pos P s) → P↓ (Typ↓ P↓ s↓ p) (s ⊚ p)

    --
    --  Opetopic Terms
    --

    𝕆Term : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (X↓ : 𝕆Fam X ℓ₁)
      → Type (ℓ-max ℓ₀ ℓ₁) 

    Term-frm : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (X↓ : 𝕆Fam X ℓ₁)
      → (f : Frm X) → Frm↓ X↓ f

    Term-src : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) {P : Frm X → Type ℓ₀}
      → {X↓ : 𝕆Fam X ℓ₁} (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ₁)
      → {f : Frm X} (s : Src  P f)
      → Src↓ P↓ (Term-frm X X↓ f) s 
  
    --
    --  Opetopic Substitutions
    --

    𝕆Sub : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (Y : 𝕆Type n ℓ₁)
      → Type (ℓ-max ℓ₀ ℓ₁)

    --
    --  Weakening
    --

    wk : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (Y : 𝕆Type n ℓ₁)
      → 𝕆Fam X ℓ₁

    Δ-term : ∀ {n ℓ} (X : 𝕆Type n ℓ) 
      → 𝕆Term X (wk X X)
  

    --
    --  Monadic Structure
    --

    η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → Src P f


  --
  --  Definitions of opeotpic types and frames
  --

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ src ∈ Src P f ] 
    P f

  module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ} (U : Frm (X , P) → Type ℓ) where

    data Pd : Frm (X , P) → Type ℓ where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (lvs : Src (Src P) f) (tgt : P f)
        → (br : Src↓ (λ {f} f↓ s → Σ (P f) (λ x → Pd (f , s , x))) (Term-frm X (wk X X) f) lvs)
        → (flr : U (f , {!!} , tgt))
        → Pd (f , μ P lvs , tgt)



