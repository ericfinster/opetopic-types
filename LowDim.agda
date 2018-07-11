{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import StrictPoly

module LowDim where

  postulate

    Cell₀ : Type₀
    Cell₁ : Idx (slc (pb (id ⊤) (cst Cell₀))) → Type₀
    Cell₂ : Idx (slc (pb (slc (pb (id ⊤) (cst Cell₀))) Cell₁)) → Type₀

  -- niche : ∀ {ℓ} {M : Mnd ℓ} (X : OpType M) → Idx M → Type ℓ
  -- niche {M = M} X i = ⟪ M ⟫ (Ops X) i

  -- filler : ∀ {ℓ} {M : Mnd ℓ} (X : OpType M) {i : Idx M} (n : niche X i) → Type ℓ
  -- filler X {i = i} n = Σ (Ops X i) (λ x → Ops (Rels X) ((i , x) , n))

  M₀ = id ⊤
  M₁ = slc (pb M₀ (cst Cell₀))
  M₂ = slc (pb M₁ Cell₁)

  Hom : Cell₀ → Cell₀ → Type₀
  Hom x y = Cell₁ ((unit , y) , (unit , cst x))

  Pd₁ : Cell₀ → Cell₀ → Type₀
  Pd₁ x y = ⟪ M₁ ⟫ Cell₁ ((tt , y) , (tt , cst x))

  one-seq : {x y : Cell₀} → Hom x y → Pd₁ x y
  one-seq {x} {y} f = box (unit , y) (unit , cst x)
                          (λ { unit → unit , λ { unit → x }})
                          (λ { unit → dot (unit , x) }) ,
                        (λ { (inl unit) → f ; (inr (unit , ())) })

  two-seq : {x y z : Cell₀} → Hom y z → Hom x y → Pd₁ x z 
  two-seq {x} {y} {z} f g = box (unit , z) (unit , λ { unit → y }) (λ { unit → unit , λ { unit → x }})
                                (λ { unit → box (unit , y) (unit , λ { unit → x }) (λ { unit → unit , λ { unit → x }})
                                (λ { unit → dot (unit , x) })}) ,
                                  λ { (inl unit) → f ;
                                      (inr (unit , inl unit)) → g ;
                                      (inr (unit , inr (unit , ()))) }

  Hom₂ : (x y : Cell₀) (s : Pd₁ x y) (t : Hom x y) → Type₀
  Hom₂ x y s t = Cell₂ ((((unit , y) , unit , cst x) , t) , s)

  Pd₂ : (x y : Cell₀) (s : Pd₁ x y) (t : Hom x y) → Type₀
  Pd₂ x y s t =  ⟪ M₂ ⟫ Cell₂ ((((unit , y) , unit , cst x) , t) , s)

