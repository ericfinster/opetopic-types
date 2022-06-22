--
--  CartsianProduct.agda - Cartesian product of Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType

module Experimental.NoDecs.CartesianProduct where

prod : ∀ {n ℓ} (X Y : 𝕆Type n ℓ) → 𝕆Type n ℓ

-- The use of opetopic maps circumvents any need for additional rewrite rules
Fst : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} → prod X Y ⇒ X
Snd : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} → prod X Y ⇒ Y

record prod-cell {n ℓ} {X Y : 𝕆Type n ℓ} (P : Frm X → Type ℓ) (Q : Frm Y → Type ℓ) (f : Frm (prod X Y)) : Type ℓ where
  constructor _∣_
  field
    fstₒ : P (Frm⇒ Fst f)
    sndₒ : Q (Frm⇒ Snd f)
open prod-cell

prod {zero} X Y = tt*
prod {suc n} (X , P) (Y , Q) = prod X Y , prod-cell P Q

Fst {zero} = tt*
Fst {suc n} {ℓ} {X , P} {Y , Q} = Fst , fstₒ

Snd {zero} = tt*
Snd {suc n} {ℓ} {X , P} {Y , Q} = Snd , sndₒ


---------- Tests
test1 : 𝕆Type 2 ℓ-zero
test1 = (tt* , (λ _ → Unit)) , λ _ → ℕ

test2 : 𝕆Type 2 ℓ-zero
test2 = prod test1 test1

open import Experimental.NoDecs.Shapes

test3 : snd test2 _ -- since we use records everywhere, agda understands there is only one frame in the product
test3 = 3 ∣ 4
