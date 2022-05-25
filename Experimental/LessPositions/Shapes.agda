{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Core.Prelude
open import Experimental.LessPositions.OpetopicType

module Experimental.LessPositions.Shapes where
  globe-Frm : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} (Xₛₙ : Frm Xₙ → Type ℓ) {f : Frm Xₙ} (x y : Xₛₙ f) → Frm (Xₙ , Xₛₙ)
  globe-Frm Xₛₙ {f} x y = f , y , η Xₛₙ x

  _**_ : ∀ {ℓ} → Type ℓ → ℕ → Type ℓ
  X ** zero = Lift Unit
  X ** suc zero = X
  X ** suc (suc n) = X × (X ** (suc n))

  fstt : ∀ {ℓ n} {X : Type ℓ} → X ** (suc n) → X
  fstt {n = zero} x = x
  fstt {n = suc n} (x , _) = x
                                 
  last : ∀ {ℓ n} {X : Type ℓ} → X ** (suc n) → X
  last {n = zero} x = x
  last {n = suc n} (fst , snd) = last snd

  path-chain : ∀ {ℓ} {X : Type ℓ} (Y : X → X → Type ℓ) (n : ℕ) (t : X ** (suc n)) → Type ℓ
  path-chain Y zero _ = Lift Unit
  path-chain Y (suc zero) (x , y) = Y y x
  path-chain Y (suc (suc n)) (x , t) = Y (fstt t) x × path-chain Y (suc n) t

  -- Sequences of arrows
  n-path : ∀ {ℓ} {X : 𝕆Type 2 ℓ} (n : ℕ) {t : (X .fst .snd tt*) ** suc n}
    → path-chain (λ x y → X .snd (tt* , y , x)) n t
    → Src (X .snd) (tt* , fstt t , last t)
  n-path zero {x} _ = lf x
  n-path (suc zero) {y , x} f = nd y [ x , x , lf x ] f
  n-path (suc (suc n)) {y , x , t} (f , l) = nd y [ x , last t , (n-path (suc n) l) ] f

  -- Sequences of unary higher cells
  n-path' : ∀ {ℓ} {m : ℕ} {X : 𝕆Type m ℓ} (n : ℕ) {P : Frm X → Type ℓ} (Q : Frm (X , P) → Type ℓ) {f : Frm X}
    {t : P f ** (suc n)}
    → path-chain (λ x y → Q (globe-Frm P x y)) n t
    → Src Q (globe-Frm P (last t) (fstt t))
  n-path' zero {P} Q {f} {x} _ = lf x
  n-path' (suc zero) {P} Q {f} {y , x} p = nd y (η (Branch Q) [ x , _ , (lf x) ]) p
  n-path' (suc (suc n)) {P} Q {f} {y , x , t} (p , l) = nd y (η (Branch Q) [ x , (η P (last t)) , (n-path' (suc n) Q l) ]) p

  module _ (X : 𝕆Type 3 ℓ-zero) where
    X₀ = X .fst .fst .snd tt*
    X₁ = X .fst .snd
    X₂ = X .snd

    hom-Frm : X₀ → X₀ → Frm (X .fst .fst)
    hom-Frm x y = tt* , y , x

    hom : X₀ → X₀ → Type
    hom x y = X₁ (hom-Frm x y)


    simplex-Frm : {x y z : X₀} (f : hom x y) (g : hom y z) (h : hom x z) → Frm (X .fst)
    simplex-Frm {x} {y} {z} f g h = hom-Frm x z , h , n-path 2 (g , f) -- nd z [ y , x , nd y [ x , x , lf x ] f ] g

    2-drop-Frm : (x : X₀) (f : hom x x) → Frm (X .fst)
    2-drop-Frm x f = hom-Frm x x , f , lf x

    unitor-Frm : (x y : X₀) (f : hom x x) (g : hom x y) (h : hom x y)
      → (Δ : X₂ (simplex-Frm f g h))
      → (Γ : X₂ (2-drop-Frm x f))
      → (O : X₂ (globe-Frm X₁ g h))
      → Frm X
    unitor-Frm x y f g h Δ Γ O = _ , O , nd h (nd y [ x , x , nd x [ x , η _ x , lf x ] [ f , lf x , nd f (lf x) Γ ] ] [ g , _ , lf g ]) Δ

    associator1 : (x y z t : X₀) (f : hom x y) (g : hom y z) (h : hom z t) (i : hom x z) (j : hom x t)
      → (Δ₁ : X₂ (simplex-Frm f g i))
      → (Δ₂ : X₂ (simplex-Frm i h j))
      → Src X₂ (hom-Frm x t , j , n-path 3 (h , g , f)) --nd t [ _ , _ , (nd _ [ _ , _ , (nd _ [ _ , _ , (lf _) ] f) ] g) ] h)
    associator1 x y z t f g h i j Δ₁ Δ₂ = nd j (nd t [ z , x , (nd z [ x , x , (lf x) ] [ i , nd z [ y , x , (nd _ _ _) ] g , nd i (nd z [ y , x , nd y [ x , x , (lf x) ] [ f , _ , lf f ] ] [ g , _ , (lf g) ]) Δ₁ ]) ] [ h , _ , (lf h) ]) Δ₂

