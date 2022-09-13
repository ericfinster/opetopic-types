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

  Src-emap : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → {P Q : Frm X → Type ℓ}
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} → Src P f ≃ Src Q f
  Src-emap {P = P} {Q} ϕ {f} = isoToEquiv
    (iso (λ s → ν {Q = Q} {f} s (λ p → fst (ϕ {_}) (s ⊚ p)))
         (λ s → ν {Q = P} {f} s (λ p → invEq (ϕ {_}) (s ⊚ p)))
         (λ s i → ν {Q = Q} {f} s (λ p → secEq (ϕ {_}) (s ⊚ p) i))
         (λ s i → ν {Q = P} {f} s (λ p → retEq (ϕ {_}) (s ⊚ p) i)))

  --
  --  Src↓ version of previous
  --
  
  -- Src↓-emap : ∀ {n ℓ} 
  --   → {P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
  --   → (U : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
  --   → (V : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
  --   → (ϕ : {F : Frm (𝕆U n ℓ)} → P F ≃ Q F)
  --   → {F : Frm (𝕆U n ℓ)} (S : Src P F)
  --   → (f : Frm↓ F)
  --   → Src↓ U S f ≃ Src↓ V (fst (Src-emap {P = P} {Q} ϕ) S) f
  -- Src↓-emap = {!!} 

  --
  --  Src and Dec is equivalent to a Src with Σ's
  --

  module DecΣEquiv {n ℓ}
    {X : 𝕆Type n ℓ}
    (P : Frm X → Type ℓ)
    (Q : {f : Frm X} → P f → Type ℓ) where

    ΣPQ : Frm X → Type ℓ
    ΣPQ f = Σ (P f) (Q {f})

    to : {f : Frm X} → Σ[ s ∈ Src P f ] (Dec Q {f} s) → Src ΣPQ f
    to (s , d) = ν {Q = ΣPQ} s (λ p → s ⊚ p , d ⊛ p) 

    from : {f : Frm X} → Src ΣPQ f → Σ[ s ∈ Src P f ] (Dec Q {f} s)
    from {f} ss = let s = ν {Q = P} ss (λ p → fst (ss ⊚ p))
                  in (s , λ-dec Q {f} s (λ p → snd (ss ⊚ ν-lift ss (λ p → fst (ss ⊚ p)) p)))

    eqv : {f : Frm X} → (Σ[ s ∈ Src P f ] (Dec Q {f} s)) ≃ Src ΣPQ f
    eqv {f} = isoToEquiv (iso to from (λ ss → refl {x = ss}) λ sd → refl {x = sd}) 

  --
  --  Dependent Verison of Dec-Σ-equiv
  --

  module Dec↓ΣEquiv {n ℓ} 
    (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    (Q : {F : Frm (𝕆U n ℓ)} → P F → Type (ℓ-suc ℓ))
    (U : {F : Frm (𝕆U n ℓ)} → P F → (f : Frm↓ F) → Type ℓ)
    (V : {F : Frm (𝕆U n ℓ)} {C : P F} → Q C → {f : Frm↓ F} → U C f → Type ℓ)
    {F : Frm (𝕆U n ℓ)}  (f : Frm↓ F) where

    module D = DecΣEquiv {X = 𝕆U n ℓ} P Q

    ΣUV : {F : Frm (𝕆U n ℓ)} → Σ (P F) Q → Frm↓ F → Type ℓ 
    ΣUV {F} (x , y) f' = Σ (U x f') (V y)
    
    to : (S : Src P F) (D : Dec {X = 𝕆U n ℓ} Q S)
      → Σ[ s ∈ Src↓ U S f ] (Dec↓ Q V S D s)
      → Src↓ ΣUV (D.to (S , D)) f
    to S D (s , d) = ν↓ {Q = ΣUV} {F} {S} {λ p → S ⊚ p , D ⊛ p} s
                           (λ p → s ⊚↓ p , d ⊛↓ p)

    from : (s : Src D.ΣPQ F)
      → (ss : Src↓ ΣUV s f)
      → Σ[ s↓ ∈ Src↓ U (D.from s .fst) f ] (Dec↓ Q V (D.from s .fst) (D.from s .snd) s↓)
    from s ss = let s↓ = ν↓ {Q = U} {F} {s} {λ p → fst (s ⊚ p)} {f} ss (λ p → fst (ss ⊚↓ p))
                in s↓ , λ-dec↓ {X = P} {Q} {U} V {F} {D.from s .fst} (D.from s .snd) {f} {s↓}
                         (λ p → snd (ss ⊚↓ ν-lift s (λ q → fst (s ⊚ q)) p))

    sec' : (s : Src D.ΣPQ F)
      → (ss : Src↓ ΣUV s f)
      → (to (D.from s .fst) (D.from s .snd) (from s ss)) ≡ ss
    sec' s ss = refl 

    eqv : (S : Src P F) (D : Dec {X = 𝕆U n ℓ} Q S)
      → (Σ[ s ∈ Src↓ U S f ] (Dec↓ Q V S D s))
      ≃ Src↓ ΣUV (D.to (S , D)) f
    eqv S D = isoToEquiv (iso (to S D) (from (D.to (S , D)))
                (sec' (D.to (S , D))) (λ sd → refl {x = sd})) 
