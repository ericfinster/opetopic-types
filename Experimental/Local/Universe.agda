{-# OPTIONS --no-positivity-check #-}
--
--  Universe.agda - The opetopic type of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType

module Experimental.Local.Universe where

  𝕆U : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)

  Frm↓ : ∀ {n ℓ} → Frm (𝕆U n ℓ) → Type ℓ

  CellFib : ∀ {n ℓ} → Frm (𝕆U n ℓ) → Type (ℓ-suc ℓ)
  CellFib {ℓ = ℓ} F = Frm↓ F → Type ℓ

  Src↓ : ∀ {n ℓ} 
    → (Q : (F' : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (E : {F' : Frm (𝕆U n ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src Q F)
    → (f : Frm↓ F) → Type ℓ 

  Typ↓ : ∀ {n ℓ} 
    → (Q : (F' : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (E : {F' : Frm (𝕆U n ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F} 
    → (S : Src Q F) (s : Src↓ Q E S f)
    → (p : Pos {X = 𝕆U n ℓ} Q S)
    → Frm↓ (Typ Q S p)

  _⊚↓_ : ∀ {n ℓ} 
    → (Q : (F' : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (E : {F' : Frm (𝕆U n ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F} 
    → (S : Src Q F) (s : Src↓ Q E S f)
    → (p : Pos {X = 𝕆U n ℓ} Q S)
    → E (S ⊚ p) (Typ↓ Q E S s p) 

  𝕆U zero ℓ = tt*
  𝕆U (suc n) ℓ = 𝕆U n ℓ , CellFib 

  Frm↓ {zero} F = Unit*
  Frm↓ {suc n} (F , S , T) = 
    Σ[ f ∈ Frm↓ F ]
    Σ[ s ∈ Src↓ CellFib (λ C → C) S f ]
    T f 

  postulate

    ν↓ : ∀ {n ℓ} 
      → (P Q : (F' : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (A : {F' : Frm (𝕆U n ℓ)} → P F' → (f' : Frm↓ F') → Type ℓ)
      → (B : {F' : Frm (𝕆U n ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F)
      → (ϕ : (p : Pos P S) → Q (Typ P S p))
      → {f : Frm↓ F} (s : Src↓ P A S f)
      → (ψ : (p : Pos P S) → B (ϕ p) (Typ↓ P A S s p))
      → Src↓ Q B (ν S ϕ) f 

    η↓ : ∀ {n ℓ} 
      → (Q : (F' : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (E : {F' : Frm (𝕆U n ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → (q : Q F) (e : E q f)
      → Src↓ Q E (η Q q) f 

    μ↓ : ∀ {n ℓ} 
      → (Q : (F' : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (E : {F' : Frm (𝕆U n ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {f : Frm↓ F}
      → (S : Src (Src Q) F) (s : Src↓ (Src Q) (Src↓ Q E) S f)
      → Src↓ Q E (μ Q S) f 

    Dec↓ : ∀ {n ℓ} 
      → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (Q : {F : Frm (𝕆U n ℓ)} → P F → Type (ℓ-suc ℓ))
      → (E : {F : Frm (𝕆U n ℓ)} → P F → (f : Frm↓ F) → Type ℓ)
      → (R : {F : Frm (𝕆U n ℓ)} (p : P F) (f : Frm↓ F) → Q p → E p f → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F) (D : Dec {X = 𝕆U n ℓ} Q S)
      → {f : Frm↓ F} (s : Src↓ P E S f)
      → Type ℓ

  module _ {n ℓ}
    (Q : (F' : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    (E : {F' : Frm (𝕆U (suc n) ℓ)} → Q F' → (f' : Frm↓ F') → Type ℓ) where

    data Pd↓Lf {F : Frm (𝕆U n ℓ)} (C : Frm↓ F → Type ℓ)
      : Frm↓ {suc n} (F , η {X = 𝕆U n ℓ} CellFib C , C) → Type ℓ where

      lf↓ : {f : Frm↓ F} (c : C f) → Pd↓Lf C (f , η↓ CellFib (λ C → C) C c , c)

    data Pd↓Nd {F : Frm (𝕆U n ℓ)} (S : Src CellFib F) (T : CellFib F)
      (flr : Q (F , S , T)) (brs : Dec {X = 𝕆U n ℓ} (Branch Q) S)
      : Frm↓ {suc n} (F , μ {X = 𝕆U n ℓ} CellFib (ν {X = 𝕆U n ℓ} S (λ p → lvs (brs ⊛ p))) , T) → Type ℓ where

      nd↓ : {f : Frm↓ F} (src : Src↓ CellFib (λ C → C) S f) (tgt : T f)
        → (el : E flr (f , src , tgt))
        → (ebr : Dec↓ CellFib (Branch Q) (λ C → C)
            (λ C f b e → Σ[ s' ∈ Src↓ CellFib (λ C → C) (lvs b) f ]
                          Src↓ {suc n} Q E (br b) (f , s' , e)) S brs src)
        → Pd↓Nd S T flr brs (f , {!!} , tgt)

  Src↓ {zero} Q E S F = Unit*
  Src↓ {suc n} Q E (lf tgt) = Pd↓Lf Q E tgt
  Src↓ {suc n} Q E (nd src tgt flr brs) = Pd↓Nd Q E src tgt flr brs

  Typ↓ = {!!}
  _⊚↓_ = {!!} 
