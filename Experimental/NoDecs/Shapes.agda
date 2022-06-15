{-# OPTIONS --no-positivity-check #-}
--
--  Shapes.agda - General shapes in opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Experimental.NoDecs.OpetopicType

module Experimental.NoDecs.Shapes where
  globe-Frm : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} (Xₛₙ : Frm Xₙ → Type ℓ) {f : Frm Xₙ} (x y : Xₛₙ f) → Frm (Xₙ , Xₛₙ)
  globe-Frm Xₛₙ {f} x y = f , η Xₛₙ x , y

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
    → path-chain (λ x y → X .snd (tt* , x , y)) n t
    → Src (X .snd) (tt* , last t , fstt t)
  n-path zero {x} f = lf x
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


  module _ {ℓ} (X₀ : 𝕆Type 1 ℓ) where
    Obj : Type ℓ
    Obj = snd X₀ tt* 

    module _ (X₁ : Frm X₀ → Type ℓ) where

      Hom : Obj → Obj → Type ℓ
      Hom x y = X₁ (tt* , x , y)

      module _ (X₂ : Frm (X₀ , X₁) → Type ℓ) where

        Null : (x : Obj) (f : Hom x x) → Type ℓ
        Null x f = X₂ ((tt* , x , x) , lf x , f)

        2Glob : {x y : Obj} (f g : Hom x y) → Type ℓ
        2Glob {x} {y} f g = X₂ ((tt* , x , y) , nd y [ x , x , lf x ] f , g)

        Simplex : {x y z : Obj} (f : Hom x y) (g : Hom y z)
          → (h : Hom x z) → Type ℓ
        Simplex {x} {y} {z} f g h = X₂ ((tt* , x , z) , nd z [ y , x , nd y [ x , x , lf x ] f ] g , h) 

  module _ (X : 𝕆Type 3 ℓ-zero) where
    X₀ = X .fst .fst .snd tt*
    X₁ = X .fst .snd
    X₂ = X .snd

    hom-Frm : X₀ → X₀ → Frm (X .fst .fst)
    hom-Frm x y = tt* , x , y

    hom : X₀ → X₀ → Type
    hom x y = X₁ (hom-Frm x y)

    simplex-Frm : {x y z : X₀} (f : hom x y) (g : hom y z) (h : hom x z) → Frm (X .fst)
    simplex-Frm {x} {y} {z} f g h = hom-Frm x z , n-path 2 (g , f) , h -- nd z [ y , x , nd y [ x , x , lf x ] f ] g

    2-drop-Frm : (x : X₀) (f : hom x x) → Frm (X .fst)
    2-drop-Frm x f = hom-Frm x x , lf x , f

    unitor-Frm : (x y : X₀) (f : hom x x) (g : hom x y) (h : hom x y)
      → (Δ : X₂ (simplex-Frm f g h))
      → (Γ : X₂ (2-drop-Frm x f))
      → (O : X₂ (globe-Frm X₁ g h))
      → Frm X
    unitor-Frm x y f g h Δ Γ O = _ , nd h (nd y [ x , x , nd x [ x , η _ x , lf x ] [ f , lf x , nd f (lf x) Γ ] ] [ g , _ , lf g ]) Δ , O

    associator1 : (x y z t : X₀) (f : hom x y) (g : hom y z) (h : hom z t) (i : hom x z) (j : hom x t)
      → (Δ₁ : X₂ (simplex-Frm f g i))
      → (Δ₂ : X₂ (simplex-Frm i h j))
      → Src X₂ (hom-Frm x t , n-path 3 (h , g , f) , j) --nd t [ _ , _ , (nd _ [ _ , _ , (nd _ [ _ , _ , (lf _) ] f) ] g) ] h)
    associator1 x y z t f g h i j Δ₁ Δ₂ = nd j (nd t [ z , x , (nd z [ x , x , (lf x) ] [ i , nd z [ y , x , (nd _ _ _) ] g , nd i (nd z [ y , x , nd y [ x , x , (lf x) ] [ f , _ , lf f ] ] [ g , _ , (lf g) ]) Δ₁ ]) ] [ h , _ , (lf h) ]) Δ₂
