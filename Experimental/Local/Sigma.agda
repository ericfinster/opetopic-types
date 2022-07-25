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
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Universe
open import Experimental.Local.UniversalFib

module Experimental.Local.Sigma where

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
      B' a (transp (λ i → Frm↓ (Frm⇒ (Σₒ-≡ A B i) f)) i0 (π-Frm (Frm⇒ (sndₒ A B) f))) 

  fstₒ {zero} A B = tt*
  fstₒ {suc n} (A , A') (B , B') = fstₒ A B , fst

  sndₒ {zero} A B = tt*
  sndₒ {suc n} (A , A') (B , B') = sndₒ A B ,
    λ {f} pr → (λ f' → B' (fst pr) (transp (λ i → Frm↓ (Frm⇒ (Σₒ-≡ A B i) f)) i0 (π-Frm (Frm⇒ (sndₒ A B) f)))) , snd pr

  Σₒ-≡ {zero} A B = refl
  Σₒ-≡ {suc n} (A , A') (B , B') i = Σₒ-≡ A B i ,
    λ {f} pr → (λ f' → {!!})


-- ———— Constraints ———————————————————————————————————————————
-- B' (fst pr) f' = ?0 (i = i1) : Type ℓ₁ (blocked on _164)
-- B' (fst pr) (transp (λ i₁ → Frm↓ (Frm⇒ (Σₒ-≡ A B i₁) f)) i0 (π-Frm (Frm⇒ (sndₒ A B) f)))

-- So here you could also transport B' itself, right?
-- and then the equality you are looking for would just
-- be somehow the canonical path over? 
