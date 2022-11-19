--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType

module Lib.Bind where

  bind : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P Q : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
    → Src Q f
  bind P Q f s ϕ = μ Q (ν s ϕ) 
