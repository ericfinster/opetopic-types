--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty 
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.OpetopicType
open import Core.OpetopicMap

open import Lib.Structures
open import Lib.Terminal
open import Lib.Opetopes

module Lib.Groupoid where

  Grp : ∀ {ℓ} (X : Type ℓ) → (n : ℕ) → 𝕆Type n ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕋 {ℓ-zero} n ⇒ (Grp X n)

  data GrpCell {n ℓ} (X : Type ℓ) : Frm (Grp X n) → Type ℓ where
    reflₒ : (x : X) (𝑜 : 𝒪 n) → GrpCell X (Frm⇒ (Pt x) 𝑜)

  Grp X zero = tt*
  Grp X (suc n) = Grp X n , GrpCell X

  Pt {zero} x = tt*
  Pt {suc n} x = Pt {n} x , λ {f} _ → reflₒ x f

