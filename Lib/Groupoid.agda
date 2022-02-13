--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.Everything
open import Lib.Structures

module Lib.Groupoid where

  Grp : ∀ {ℓ} (X : Type ℓ) → (n : ℕ) → 𝕆Type n ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → El (Grp X n)

  data GrpCell {n ℓ} (X : Type ℓ) : {𝑜 : 𝒪 n}  → Frm (Grp X n) 𝑜 → Type ℓ where
    reflₒ : (x : X) (𝑜 : 𝒪 n) → GrpCell X (Frm-El (Pt x) 𝑜)

  Grp X zero = tt*
  Grp X (suc n) = Grp X n , GrpCell X

  Pt {zero} x = tt*
  Pt {suc n} x = Pt {n} x , reflₒ x

  
