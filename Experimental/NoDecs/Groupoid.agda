--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty 
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.Groupoid where
  Grp : ∀ {ℓ} (X : Type ℓ) → (n : ℕ) → 𝕆Type n ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕋 n ⇒ (Grp X n)

  data GrpCell {n ℓ} (X : Type ℓ) : Frm (Grp X n) → Type ℓ where
    reflₒ : (x : X) {f : Frm (𝕋 n)} → GrpCell X (Frm⇒ (Pt x) f)

  Grp X zero = tt*
  Grp X (suc n) = Grp X n , GrpCell X

  Pt {zero} x = tt*
  Pt {suc n} x = Pt x , λ _ → reflₒ x

