--
--  Decorations.agda - Lemmas about Decorations
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Core.OpetopicType
open import Core.Universe

module Lib.Decorations where

  --
  --  Decorations are equivalent to functions
  --

  Dec-fun-iso : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Iso (Dec Q {f} s) ((p : Pos P s) → Q (s ⊚ p))
  Dec-fun-iso P Q {f} s = iso (λ d p → d ⊛ p) (λ-dec {P = P} Q {f} s)
                              (λ ϕ → refl) (λ d → refl)

  Dec-fun-equiv : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Dec Q {f} s
    ≃ ((p : Pos P s) → Q (s ⊚ p))
  Dec-fun-equiv P Q {f} s = isoToEquiv (Dec-fun-iso P Q s)

  --
  --  Equality of decorations can be computed pointwise
  --

  Dec-≡ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (d₀ d₁ : Dec Q {f} s)
    → (ϕ : (p : Pos P s) → d₀ ⊛ p ≡ d₁ ⊛ p) → d₀ ≡ d₁
  Dec-≡ P Q s d₀ d₁ ϕ = isoFunInjective
    (Dec-fun-iso P Q s) d₀ d₁ (λ i p → ϕ p i) 

  --
  --  Equivalence of families induces and equivalence on Src's
  --

  Src-emap-to : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P Q : Frm X → Type ℓ)
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} 
    → Src P f → Src Q f
  Src-emap-to P Q ϕ {f} s = ν {Q = Q} {f} s (λ p → fst (ϕ {_}) (s ⊚ p))

  Src-emap-from : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P Q : Frm X → Type ℓ)
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} 
    → Src Q f → Src P f 
  Src-emap-from P Q ϕ {f} s = ν {Q = P} {f} s (λ p → invEq (ϕ {_}) (s ⊚ p))

  Src-emap-sec : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P Q : Frm X → Type ℓ)
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} (s : Src Q f)
    → Src-emap-to P Q ϕ (Src-emap-from P Q ϕ s) ≡ s
  Src-emap-sec P Q ϕ {f} s i = ν {Q = Q} {f} s (λ p → secEq (ϕ {_}) (s ⊚ p) i)

  Src-emap-ret : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P Q : Frm X → Type ℓ)
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} (s : Src P f)
    → Src-emap-from P Q ϕ (Src-emap-to P Q ϕ s) ≡ s
  Src-emap-ret P Q ϕ {f} s i = ν {Q = P} {f} s (λ p → retEq (ϕ {_}) (s ⊚ p) i)

  Src-emap : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → {P Q : Frm X → Type ℓ}
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} → Src P f ≃ Src Q f
  Src-emap {P = P} {Q} ϕ = isoToEquiv
    (iso (Src-emap-to P Q ϕ)
         (Src-emap-from P Q ϕ)
         (Src-emap-sec P Q ϕ)
         (Src-emap-ret P Q ϕ)) 

  --
  --  Dependent version of previous
  --

  -- postulate
  
  --   Src↓-emap-to : ∀ {n ℓ} 
  --     → {P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
  --     → (U : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
  --     → (V : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
  --     → (ϕ : {F : Frm (𝕆U n ℓ)} → P F ≃ Q F)
  --     → {F : Frm (𝕆U n ℓ)} (S : Src P F)
  --     → (f : Frm↓ F)
  --     → Src↓ U S f → Src↓ V (Src-emap-to {P = P} {Q} ϕ S) f

  --
  --  Src and Dec is equivalent to a Src with Σ's
  --

  Dec-Σ-equiv-to : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (sd : Σ[ s ∈ Src P f ] (Dec Q {f} s))
    → Src (λ f → Σ (P f) (Q {f})) f
  Dec-Σ-equiv-to P Q (s , d) = ν {Q = λ f → Σ (P f) Q} s (λ p → s ⊚ p , d ⊛ p)

  Dec-Σ-equiv-from : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (ss : Src (λ f → Σ (P f) (Q {f})) f)
    → Σ[ s ∈ Src P f ] (Dec Q {f} s)
  Dec-Σ-equiv-from P Q {f} ss =
    let s = ν {Q = P} ss (λ p → fst (ss ⊚ p))
    in (s , λ-dec Q {f} s (λ p → snd (ss ⊚ ν-lift ss (λ p → fst (ss ⊚ p)) p)))

  Dec-Σ-equiv-sec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (ss : Src (λ f → Σ (P f) (Q {f})) f)
    → Dec-Σ-equiv-to P Q (Dec-Σ-equiv-from P Q ss) ≡ ss
  Dec-Σ-equiv-sec P Q ss = refl 

  Dec-Σ-equiv-ret : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (sd : Σ[ s ∈ Src P f ] (Dec Q {f} s))
    → Dec-Σ-equiv-from P Q (Dec-Σ-equiv-to P Q sd) ≡ sd
  Dec-Σ-equiv-ret P Q {f} (s , d) = refl

  Dec-Σ-equiv : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} 
    → (Σ[ s ∈ Src P f ] (Dec Q {f} s))
    ≃ Src (λ f → Σ (P f) (Q {f})) f
  Dec-Σ-equiv {P = P} Q {f} = isoToEquiv
    (iso (Dec-Σ-equiv-to P Q)
         (Dec-Σ-equiv-from P Q)
         (Dec-Σ-equiv-sec P Q)
         (Dec-Σ-equiv-ret P Q)) 

  --
  --  A Decoration gives a source tree decorated in Σ-types
  --

  --
  --  Dependent Verison of Dec-Σ-equiv
  --
  
  -- postulate
  
  --   Dec↓-Σ-equiv : ∀ {n ℓ} 
  --     → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
  --     → (Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ))
  --     → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
  --     → (Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ)
  --     → {F : Frm (𝕆U n ℓ)} (S : Src X F) (D : Dec {X = 𝕆U n ℓ} Y S)
  --     → {f : Frm↓ F}
  --     → (Σ[ s ∈ Src↓ P S f ] (Dec↓ Y Q S D s))
  --     ≃ Src↓ {!!} {!!} {!!}


