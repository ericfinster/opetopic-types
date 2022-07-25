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
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Shapes
open import Experimental.Local.Structures

module Experimental.Local.CartesianProduct where

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


test3 : snd test2 _ -- since we use records everywhere, agda understands there is only one frame in the product
test3 = 3 ∣ 4


-- Fibrancy
fst-src : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (P : Frm X → Type ℓ) (Q : Frm Y → Type ℓ) {f : Frm (prod X Y)} → Src (prod-cell P Q) f → Src P (Frm⇒ Fst f)
fst-src {n} {ℓ} {X} {Y} P Q {f} s = Src⇒ {P = prod-cell P Q} s Fst (λ p → fstₒ (s ⊚ p))

snd-src : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (P : Frm X → Type ℓ) (Q : Frm Y → Type ℓ) {f : Frm (prod X Y)} → Src (prod-cell P Q) f → Src Q (Frm⇒ Snd f)
snd-src {n} {ℓ} {X} {Y} P Q {f} s = Src⇒ {P = prod-cell P Q} s Snd (λ p → sndₒ (s ⊚ p))

-- Since Inhab is defined differently when n=0 or n=(suc k), the following pattern matching is required for agda to type-check
charac-filler-prod : ∀ {n ℓ} {X Y : 𝕆Type (suc n) ℓ} (P : Frm X → Type ℓ) (Q : Frm Y → Type ℓ)
  {f : Frm (prod (fst X) (fst Y))} (s : Src (prod-cell (snd X) (snd Y)) f) →
  Iso
    (horn-filler (prod-cell P Q) s)
    (horn-filler P (fst-src (snd X) (snd Y) s) × horn-filler Q (snd-src (snd X) (snd Y) s))
charac-filler-prod {zero} P Q s = iso g h (λ _ → refl) (λ _ → refl) where
  g : _
  g (tgt , cell) = (fstₒ tgt , fstₒ cell) , (sndₒ tgt , sndₒ cell)
  h : _
  h ((tgt₁ , cell₁) , (tgt₂ , cell₂)) = (tgt₁ ∣ tgt₂) , (cell₁ ∣ cell₂)
charac-filler-prod {suc n} P Q s = iso g h (λ _ → refl) λ _ → refl where
  g : _
  g (tgt , cell) = (fstₒ tgt , fstₒ cell) , (sndₒ tgt , sndₒ cell)
  h : _
  h ((tgt₁ , cell₁) , (tgt₂ , cell₂)) = (tgt₁ ∣ tgt₂) , (cell₁ ∣ cell₂)

is-fib-prod : ∀ {n ℓ} {X Y : 𝕆Type (suc (suc n)) ℓ} → is-fibrant X → is-fibrant Y → is-fibrant (prod X Y)
is-fib-prod {X = (X , P) , P'} {Y = (Y , Q) , Q'} fibX fibY f s =
  -- I'm sure there's a proof in the library that isos/equivs respect HLevel, but I can't find it anymore, so instead I used isContrRetract
  isContrRetract (Iso.fun charac) (Iso.inv charac) (Iso.leftInv charac) (isContrΣ (fibX _ _) λ _ → fibY _ _)
  where
  charac = charac-filler-prod P' Q' s

prod∞ : ∀ {n ℓ} {Xₙ Yₙ : 𝕆Type ℓ n} (X : 𝕆Type∞ Xₙ) (Y : 𝕆Type∞ Yₙ) → 𝕆Type∞ (prod Xₙ Yₙ)
Fill (prod∞ X Y) = prod-cell (Fill X) (Fill Y)
Hom (prod∞ X Y) = prod∞ (Hom X) (Hom Y)
