{-# OPTIONS --no-positivity-check #-}
--
--  Shapes.agda - General shapes in opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Experimental.Local.OpetopicType

module Experimental.Local.Shapes where

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

  cons : ∀ {n ℓ} {X : Type ℓ} → X → X ** n → X ** (suc n)
  cons {zero} x l = x
  cons {suc n} x l = x , l

  path-chain : ∀ {ℓ} {X : Type ℓ} (Y : X → X → Type ℓ) (n : ℕ) (t : X ** (suc n)) → Type ℓ
  path-chain Y zero _ = Lift Unit
  path-chain Y (suc zero) (y , x) = Y x y
  path-chain Y (suc (suc n)) (x , t) = Y (fstt t) x × path-chain Y (suc n) t

  chain-cons : ∀ {ℓ} {X : Type ℓ} (Y : X → X → Type ℓ) {n : ℕ} {y : X} {t : X ** (suc n)} (p : path-chain Y n t) → Y (fstt t) y → path-chain Y (suc n) (y , t)
  chain-cons Y {zero} {y} {t} _ f = f
  chain-cons Y {suc n} {y} {t} p f = f , p

 -- Sequences of arrows
  n-path : ∀ {ℓ} {X₀ : 𝕆Type 1 ℓ} (X₁ : Frm X₀ → Type ℓ) (n : ℕ) {t : (X₀ .snd tt*) ** suc n}
    → path-chain (λ x y → X₁ (tt* , x , y)) n t
    → Src X₁ (tt* , last t , fstt t)
  n-path X₁ zero {x} f = lf x
  n-path X₁ (suc zero) {y , x} f = nd x y f [ x , lf x ] 
  n-path X₁ (suc (suc n)) {y , x , t} (f , l) = nd x y f [ last t , n-path X₁ (suc n) l ]

--   -- Sequences of unary higher cells
--   n-path' : ∀ {ℓ} {m : ℕ} {X : 𝕆Type m ℓ} (n : ℕ) {P : Frm X → Type ℓ} (Q : Frm (X , P) → Type ℓ) {f : Frm X}
--     {t : P f ** (suc n)}
--     → path-chain (λ x y → Q (globe-Frm P x y)) n t
--     → Src Q (globe-Frm P (last t) (fstt t))
--   n-path' zero {P} Q {f} {x} _ = lf x
--   n-path' (suc zero) {P} Q {f} {y , x} p = nd y (η (Branch Q) [ x , _ , (lf x) ]) p
--   n-path' (suc (suc n)) {P} Q {f} {y , x , t} (p , l) = nd y (η (Branch Q) [ x , (η P (last t)) , (n-path' (suc n) Q l) ]) p

  module _ {ℓ} (X₀ : 𝕆Type 1 ℓ) where
    Obj : Type ℓ
    Obj = snd X₀ tt*

    hom-Frm : Obj → Obj → Frm X₀
    hom-Frm x y = (tt* , x , y)

    module _ (X₁ : Frm X₀ → Type ℓ) where
      hom : Obj → Obj → Type ℓ
      hom x y = X₁ (hom-Frm x y)

      simplex-Frm : {x y z : Obj} (f : hom x y) (g : hom y z) (h : hom x z) → Frm (X₀ , X₁)
      simplex-Frm {x} {y} {z} f g h = hom-Frm x z , n-path X₁ 2 (g , f) , h 

      2-drop-Frm : (x : Obj) (f : hom x x) → Frm (X₀ , X₁)
      2-drop-Frm x f = hom-Frm x x , lf x , f

--       {-
--       src→chain : {f : Frm X₀} → Src X₁ f → Σ[ n ∈ ℕ ] Σ[ t ∈ (Obj ** n) ] (path-chain hom n (cons (snd (snd f)) t))
--       src→chain (lf tgt) = 0 , tt* , tt*
--       src→chain (nd tgt [ stm₁ , .(η (λ f → snd X₀ tt*) stm₁) , _ ] flr) = ?
--       src→chain (nd tgt [ stm₁ , .(μ (id-map tt*) (Branch X₁) (λ f → snd X₀ tt*) brs (λ p → lvs (brs ⊚ p))) , nd .stm₁ brs flr₁ ] flr) = ?
--       -}

      module _ (X₂ : Frm (X₀ , X₁) → Type ℓ) where

        Null : (x : Obj) (f : hom x x) → Type ℓ
        Null x f = X₂ (2-drop-Frm x f)

        2Glob : {x y : Obj} (f g : hom x y) → Type ℓ
        2Glob {x} {y} f g = X₂ ((tt* , x , y) , (nd x y f [ x , lf x ]) , g)

        Simplex : {x y z : Obj} (f : hom x y) (g : hom y z)
          → (h : hom x z) → Type ℓ
        Simplex {x} {y} {z} f g h = X₂ (simplex-Frm f g h)

        left-unitor-Src : (x y : Obj) (f : hom y y) (g h : hom x y)
          → (Δ : X₂ (simplex-Frm g f h))
          → (Γ : X₂ (2-drop-Frm y f))
          → Src X₂ (globe-Frm X₁ g h)
        left-unitor-Src x y f g h Δ Γ = nd (n-path X₁ 2 (f , g)) h Δ ([ lf y , nd (lf y) f Γ tt* ] , [ η X₁ g , (lf g) ] , tt*)

        right-unitor-Src : (x y : Obj) (f : hom x x) (g h : hom x y)
          → (Δ : X₂ (simplex-Frm f g h))
          → (Γ : X₂ (2-drop-Frm x f))
          → Src X₂ (globe-Frm X₁ g h)
        right-unitor-Src x y f g h Δ Γ = nd (n-path X₁ 2 (g , f)) h Δ ([ η X₁ g , (lf g) ] , [ lf x , nd (lf x) f Γ tt* ] , tt*)


        -- (h | g | f) → ((h ∘ g) | f) → ((h ∘ g) ∘ f)
        left-associator-Src : (x y z w : Obj) (f : hom x y) (g : hom y z) (h : hom z w) (i : hom y w) (j : hom x w)
          → (Δ₁ : X₂ (simplex-Frm f i j))
          → (Δ₂ : X₂ (simplex-Frm g h i))
          → Src X₂ (_ , n-path X₁ 3 (h , g , f) , j)
        left-associator-Src x y z w f g h i j Δ₁ Δ₂ = nd (n-path X₁ 2 (i , f)) j Δ₁ (
          [ _ {-"n-path X₁ 2 (h , g)" here should work but doesn't-} , (nd (n-path X₁ 2 (h , g)) i Δ₂ ([ _ , lf h ] , [ _ , lf g ] , tt*)) ] ,
          [ _ , lf f ] ,
          tt*)

        -- (h | g | f) → (h | (g ∘ f)) → (h ∘ (g ∘ f))
        right-associator-Src : (x y z w : Obj) (f : hom x y) (g : hom y z) (h : hom z w) (i : hom x z) (j : hom x w)
          → (Δ₁ : X₂ (simplex-Frm  i h j))
          → (Δ₂ : X₂ (simplex-Frm f g i))
          → Src X₂ (_ , n-path X₁ 3 (h , g , f) , j)
        right-associator-Src x y z w f g h i j Δ₁ Δ₂ = nd (n-path X₁ 2 (h , i)) j Δ₁ (
          [ _ , lf h ] ,
          [ _ , nd (n-path X₁ 2 (g , f)) i Δ₂ ([ _ , lf g ] , [ _ , lf f ] , tt*) ] ,
          tt*)
