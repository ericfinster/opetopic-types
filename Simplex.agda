{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import StrictPoly
open import LowDim

module Simplex where

  -- -- Okay, we want to make a simplex.
  -- simplex : (x y z : Cell₀)
  --   → (f : Hom x y) (g : Hom y z) (h : Hom x z)
  --   → (α : Hom₂ x z (two-seq g f) h)
  --   → Pd₂ x z (two-seq g f) h
  -- simplex x y z f g h α =
  --   (box (((unit , z) , unit , cst x) , h)
  --     (two-seq g f)
  --     (λ { (inl unit) → one-seq g ;
  --          (inr (unit , inl unit)) → one-seq f ;
  --          (inr (unit , inr ())) })  -- These should be the individual arrows as single sequences ...
  --     (λ { (inl unit) → dot (((unit , z) , unit , cst y) , g) ;
  --          (inr (unit , inl unit)) → dot (((unit , y) , unit , cst x) , f) ;
  --          (inr (unit , inr ())) })) ,
  --     {!!}  


  simplex : (x y z : Cell₀)
    → (f : Hom x y) (g : Hom y z) (h : Hom x z)
    → (α : Hom₂ x z (two-seq g f) h)
    → Pd₂ x z (two-seq g f) h
  simplex x y z f g h α = box i c δ ε , {!!}

    where M = pb M₁ Cell₁

          i : Idx M
          i = ((unit , z) , unit , cst x) , h

          c : γ M i
          c = two-seq g f

          δ : (p : ρ M i c) → γ M (τ M i c p)
          δ p = {!snd
                     (δ
                      (μρ-fst M₁ ((tt , z) , tt , (λ _ → x)) (fst (two-seq g f))
                       (λ p → fst (δ p)) p))
                     (μρ-snd M₁ ((tt , z) , tt , (λ _ → x)) (fst (two-seq g f))
                      (λ p → fst (δ p)) p)
!}
          -- δ (inl unit) = ?
          -- δ (inr (unit , inl unit)) = ?
          -- δ (inr (unit , inr ()))


-- snd
-- (δ
--  (μρ-fst M₁ ((tt , z) , tt , (λ _ → x)) (fst (two-seq g f))
--   (λ p → fst (δ p)) p))
-- (μρ-snd M₁ ((tt , z) , tt , (λ _ → x)) (fst (two-seq g f))
--  (λ p → fst (δ p)) p)
-- !=
-- (λ { true → g
--    ; (inr (tt , true)) → f
--    ; (inr (tt , inr (tt , ())))
--    })
-- p

          -- δ (inl unit) = one-seq g
          -- δ (inr (unit , inl unit)) = one-seq f
          -- δ (inr (unit , inr ())) 

          ε : (p : ρ M i c) → Nst M (τ M i c p) (δ p)
          ε p = {!!}

    -- (box (((unit , z) , unit , cst x) , h)
    --   (two-seq g f) {!!} {!!} , {!!})
      -- (λ { (inl unit) → one-seq g ;
      --      (inr (unit , inl unit)) → one-seq f ;
      --      (inr (unit , inr ())) })  -- These should be the individual arrows as single sequences ...
      -- (λ { (inl unit) → dot (((unit , z) , unit , cst y) , g) ;
      --      (inr (unit , inl unit)) → dot (((unit , y) , unit , cst x) , f) ;
      --      (inr (unit , inr ())) })) ,
      -- {!!}  


