--
--  Families.agda - The opetopic type of opetopic families
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
open import Experimental.Local.Universe
open import Experimental.Local.UniversalFib
open import Experimental.Local.Sigma

module Experimental.Local.Families where

  𝕆² : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)

  base : (n : ℕ) (ℓ : Level) → 𝕆² n ℓ ⇒ 𝕆U n ℓ 
  fam : (n : ℕ) (ℓ : Level) → Σₒ (𝕆² n ℓ) (base n ℓ) ⇒ 𝕆U n ℓ 

  𝕆² zero ℓ = tt*
  𝕆² (suc n) ℓ = 𝕆² n ℓ , λ f →
    Σ[ C ∈ CellFib (Frm⇒ (base n ℓ) f) ]
    ((fp : Frm (Σₒ (𝕆² n ℓ) (base n ℓ)))
     (e : Frm⇒ (fstₒ (𝕆² n ℓ) (base n ℓ)) fp ≡ f)
     → C (transport (λ i → Frm↓ (Frm⇒ (base n ℓ) (e i)))
         (transport (λ i → Frm↓ (Frm⇒ (Σₒ-≡ (𝕆² n ℓ) (base n ℓ) i) fp))
           (π-Frm (Frm⇒ (sndₒ (𝕆² n ℓ) (base n ℓ)) fp))))  
     → Frm↓ (Frm⇒ (fam n ℓ) fp) → Type ℓ)

  base zero ℓ = tt*
  base (suc n) ℓ = base n ℓ , fst 
  
  fam zero ℓ = tt*
  fam (suc n) ℓ = fam n ℓ , λ {fp} pr f↓ → snd (fst pr) fp refl {!snd pr!} f↓ 

  -- Okay, messy, but this actually looks like it is doable.
  -- If that is actually the case, what does that imply? 
