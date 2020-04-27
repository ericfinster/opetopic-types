{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FundamentalThm where

  -- The fundamental theorem of HoTT

  -- module _ {i} (A : Type i) (P : A → Type i)
  --   (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P)) (a₁ : A) where

  --   to :  P a₁ → a₀ == a₁
  --   to p = fst= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))

  --   from : a₀ == a₁ → P a₁
  --   from idp = r

    -- to-from : (p : a₀ == a₁) → to (from p) == p
    -- to-from p = {!!}


  postulate
  
    fundamental-thm : ∀ {i} (A : Type i) (P : A → Type i)
      → (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P))
      → (a₁ : A) → P a₁ ≃ (a₀ == a₁)
      
  -- fundamental-thm A P a₀ r is-c a₁ =
  --   equiv (to A P a₀ r is-c a₁) (from A P a₀ r is-c a₁)
  --         {!!} {!!}
