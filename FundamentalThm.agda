{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FundamentalThm where

  -- The fundamental theorem of HoTT
  
  fundamental-thm : ∀ {i} (A : Type i) (P : A → Type i)
    → (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P))
    → (a₁ : A) → P a₁ ≃ (a₀ == a₁)
  fundamental-thm A P a₀ r is-c a₁ = equiv to from to-from from-to 

    where to :  P a₁ → a₀ == a₁
          to p = fst= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))

          from : a₀ == a₁ → P a₁
          from p = transport P p r

          to-from : (p : a₀ == a₁) → to (from p) == p
          to-from idp = ap fst= claim

            where claim : contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r) == idp
                  claim = contr-has-all-paths ⦃ =-preserves-contr {x = (a₀ , r)} {y = a₀ , r} is-c ⦄
                            (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r)) idp

          from-to : (p : P a₁) → from (to p) == p
          from-to p = to-transp (snd= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p)))

