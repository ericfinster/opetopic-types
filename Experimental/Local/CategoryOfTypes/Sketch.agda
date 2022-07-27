--
--  Sketch.agda - sketch of cat of types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Structures
open import Experimental.Local.Terminal
open import Experimental.Local.Universe

open import Experimental.Local.CategoryOfTypes.Lemmas

module Experimental.Local.CategoryOfTypes.Sketch where

  ∞Cat : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞Cat ℓ = Σ[ X ∈ 𝕆Type∞ tt* ] is-fibrant-ext (Hom X)

  is-fib-rel : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} → CellFib F → Type ℓ
  is-fib-rel {zero} C = Unit*
  is-fib-rel {suc n} {F = F , S , T} C = 
      {f : Frm↓ F} (s : Src↓ (λ C → C) S f)
    → isContr (Σ[ t ∈ T f ] C (f , s , t)) 

  𝒮ₙ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮π : (n : ℕ) (ℓ : Level) → 𝒮ₙ n ℓ ⇒ 𝕆U n ℓ

  𝒮ₙ zero ℓ = tt*
  𝒮ₙ (suc n) ℓ = 𝒮ₙ n ℓ , λ f →
    Σ[ C ∈ CellFib (Frm⇒ (𝒮π n ℓ) f) ]
    is-fib-rel C
  
  𝒮π zero ℓ = tt*
  𝒮π (suc n) ℓ = 𝒮π n ℓ , fst

  𝒮Ext : (n : ℕ) (ℓ : Level) → 𝕆Type∞ (𝒮ₙ n ℓ)
  Fill (𝒮Ext n ℓ) = snd (𝒮ₙ (suc n) ℓ)
  Hom (𝒮Ext n ℓ) = 𝒮Ext (suc n) ℓ

  postulate

    comp-fib-thm : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
      → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
      → is-fib-rel (USrc↓ {F = F} S)

  𝒮ₙ-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (2 + n) ℓ)
  𝒮ₙ-is-fibrant n ℓ f s = ((C , C-is-fib-rel) , (R , R-is-fib-rel)) , {!!} 

    where C : CellFib (Frm⇒ (𝒮π n ℓ) f)
          C = USrc↓ {F = Frm⇒ (𝒮π n ℓ) f} (Src⇒ {f = f} s (𝒮π n ℓ) λ p → fst (s ⊚ p))
  
          C-is-fib-rel : is-fib-rel C
          C-is-fib-rel = comp-fib-thm {n} {ℓ} (Src⇒ {f = f} s (𝒮π n ℓ) λ p → fst (s ⊚ p))
                         (λ p → snd (s ⊚ Pos⇐ s (𝒮π n ℓ) (λ p₁ → fst (s ⊚ p₁)) p))

          R : CellFib (Frm⇒ (𝒮π n ℓ) f , Src⇒ s (𝒮π n ℓ) (λ p → fst (s ⊚ p)) , C)
          R (frm , src , tgt) = src ≡ tgt

          R-is-fib-rel : is-fib-rel R
          R-is-fib-rel src = isContrSingl src 

  𝒮Ext-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant-ext (𝒮Ext n ℓ)
  fill-fib (𝒮Ext-is-fibrant n ℓ) = 𝒮ₙ-is-fibrant n ℓ 
  hom-fib (𝒮Ext-is-fibrant n ℓ) = 𝒮Ext-is-fibrant (suc n) ℓ

  𝒮 : (ℓ : Level) → ∞Cat (ℓ-suc ℓ)
  𝒮 ℓ = 𝒮Ext 0 ℓ , 𝒮Ext-is-fibrant 1 ℓ 

