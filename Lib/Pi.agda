--
--  Pi.agda - Pi of opetoip types
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

open import Lib.CartesianProduct

module Lib.Pi where

  Πₒ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → 𝕆Type n (ℓ-max ℓ₀ ℓ₁)

  apₒ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → A ×ₒ Πₒ A B ⇒ 𝕆V n ℓ₁

  Πₒ-≡ : ∀ {n ℓ₀ ℓ₁} (A : 𝕆Type n ℓ₀) (B : A ⇒ 𝕆U n ℓ₁)
    → 𝕆π n ℓ₁ ⊙ apₒ A B ≡ B ⊙ Fst {Y = Πₒ A B}

  Πₒ {zero} A B = tt*
  Πₒ {suc n} (A , A') (B , B') = Πₒ A B , λ f →
      (fp : Frm (A ×ₒ Πₒ A B)) (e : Frm⇒ Snd fp ≡ f)
    → (a : A' (Frm⇒ Fst fp))
    → transport⁻ (λ i → CellFib (Frm⇒ (Πₒ-≡ A B i) fp)) (B' a) (π-Frm (Frm⇒ (apₒ A B) fp))

  apₒ {zero} A B = tt*
  apₒ {suc n} (A , A') (B , B') = apₒ A B , λ {fp} pr →
    transport⁻ (λ i → CellFib (Frm⇒ (Πₒ-≡ A B i) fp)) (B' (fstₒ pr)) ,
    sndₒ pr fp refl (fstₒ pr)

  Πₒ-≡ {zero} A B = refl
  Πₒ-≡ {suc n} (A , A') (B , B') i = Πₒ-≡ A B i ,
    λ {fp} pr → transport⁻-filler (λ i → CellFib (Frm⇒ (Πₒ-≡ A B i) fp)) (B' (fstₒ pr)) (~ i)
