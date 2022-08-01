--
--  Sigma.agda - Sigma of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Core.OpetopicType
open import Core.OpetopicMap
open import Core.Universe
open import Core.UniversalFib

module Lib.Sigma where

  Σₒ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → 𝕆Type n (ℓ-max ℓ₀ ℓ₁)

  fstₒ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → Σₒ A B ⇒ A

  sndₒ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → Σₒ A B ⇒ 𝕆V n ℓ₁

  Σₒ-≡ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → 𝕆π n ℓ₁ ⊙ sndₒ A B ≡ B ⊙ fstₒ A B 

  Σₒ {zero} A B = tt*
  Σₒ {suc n} (A , A') (B , B') = Σₒ A B , λ f →
    Σ[ a ∈ A' (Frm⇒ (fstₒ A B) f) ]
    transport⁻ (λ i → CellFib (Frm⇒ (Σₒ-≡ A B i) f)) (B' a) (π-Frm (Frm⇒ (sndₒ A B) f))   

  fstₒ {zero} A B = tt*
  fstₒ {suc n} (A , A') (B , B') = fstₒ A B , fst

  sndₒ {zero} A B = tt*
  sndₒ {suc n} (A , A') (B , B') = sndₒ A B ,
    λ {f} pr → transport⁻ (λ i → CellFib (Frm⇒ (Σₒ-≡ A B i) f)) (B' (fst pr)) , snd pr 

  Σₒ-≡ {zero} A B = refl
  Σₒ-≡ {suc n} (A , A') (B , B') i = Σₒ-≡ A B i , 
    λ {f} pr → transport⁻-filler (λ i → CellFib (Frm⇒ (Σₒ-≡ A B i) f)) (B' (fst pr)) (~ i)


