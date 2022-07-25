{-# OPTIONS --no-positivity-check --no-termination-check #-}
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
open import Experimental.Local.Universe
open import Experimental.Local.CategoryOfTypes.Lemmas

module Experimental.Local.CategoryOfTypes.CategoryOfTypes where

  UnivComp : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F) → CellFib F
  UnivComp S = Src↓ CellFib (λ C → C) S 

  is-fib : ∀ {n ℓ} {F : Frm (𝕆U (suc n) ℓ)} → CellFib F → Type ℓ
  is-fib {F = F , S , T} C =
      {f : Frm↓ F} (s : Src↓ CellFib (λ C → C) S f)
    → isContr (Σ[ t ∈ T f ] C (f , s , t)) 

  postulate

    η↓-is-equiv : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {C : X F} (f : Frm↓ F)
      → isEquiv (η↓ P {f = f} {C = C})

    μ↓-is-equiv : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} {S : Src (Src X) F} (f : Frm↓ F)
      → isEquiv (μ↓ P {f = f} {S = S})

  η↓-inv : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {C : X F} {f : Frm↓ F}
    → Src↓ X P (η X C) f →  P C f
  η↓-inv P {f = f} s = invIsEq (η↓-is-equiv P f) s 

  μ↓-inv : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} {S : Src (Src X) F} {f : Frm↓ F}
    → Src↓ X P (μ X S) f → Src↓ (Src X) (Src↓ X P) S f
  μ↓-inv P {f = f} s = invIsEq (μ↓-is-equiv P f) s


  --
  --  I'm going to try to write a proof based on the above
  --  equivalences, and then we can try to fill in the details.
  --

  comp-fib-thm : ∀ {n ℓ} {F : Frm (𝕆U (suc n) ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S) → is-fib (S ⊚ p))
    → is-fib (UnivComp S)
  comp-fib-thm (lf {F} C) ϕ {f} s = {!!}

    where lemma = (Σ[ c ∈ C f ] (Src↓ CellFib (λ C → C) (lf C) (f , s , c)))   ≡⟨ {!!} ⟩
                  (Σ[ c ∈ C f ] (s ≡ η↓ (λ P → P) {C = C} c))                  ≡⟨ {!!} ⟩
                  (Σ[ c ∈ C f ] η↓-inv (λ P → P) {C = C} s ≡ c)                ∎ 
              
    -- Now, the result follows because the last is the homotopy fiber
    -- of an equivalence.

  comp-fib-thm (nd {F} S T C Brs) ϕ {f} cnpy = {!!}

    where lemma = (Σ[ t ∈ T f ] Src↓ CellFib (λ C → C) (nd S T C Brs) (f , cnpy , t))                                      ≡⟨ {!!} ⟩

                  -- By matching  ... 
                  (Σ[ t ∈ T f ] Σ[ s ∈ Src↓ CellFib (λ C → C) S f ] Σ[ c ∈ C (f , s , t) ]
                   Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S Brs s ]
                     canopy↓ CellFib (λ C → C) {S = S} {D = Brs} {f = f} {s = s} brs ≡ cnpy)                               ≡⟨ {!!} ⟩

                  -- Using the fibrancy of C ...
                  (Σ[ s ∈ Src↓ CellFib (λ C → C) S f ] 
                   Σ[ brs ∈ Dec↓ (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S Brs s ]
                       canopy↓ CellFib (λ C → C) {S = S} {D = Brs} {f = f} {s = s} brs ≡ cnpy)                             ≡⟨ {!!} ⟩

                  -- By the inductive hypothesis ... though you have to be more specific ...
                  (Σ[ σ  ∈ Src↓ (Src CellFib) (Src↓ CellFib (λ C₁ → C₁)) (ν {f = F} S (λ p → lvs (Brs ⊛ p))) f ]
                      μ↓ (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))} σ ≡ cnpy)                               ≡⟨ {!!} ⟩

                  -- General facts about equivalences...
                  (Σ[ σ  ∈ Src↓ (Src CellFib) (Src↓ CellFib (λ C₁ → C₁)) (ν {f = F} S (λ p → lvs (Brs ⊛ p))) f ]
                      σ ≡ μ↓-inv (λ C → C) {F = F} {S = ν {f = F} S (λ p → lvs (Brs ⊛ p))} cnpy) ∎





