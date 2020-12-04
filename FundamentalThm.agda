{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import lib.NType2

module FundamentalThm where

  -- The fundamental theorem of HoTT

  module _ {i} (A : Type i) (P : A → Type i) (is-c : is-contr (Σ A P)) (a₀ : A) (r : P a₀) where

    ft-to : (a₁ : A) → P a₁ → a₀ == a₁
    ft-to a₁ p = fst= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))

    ft-to-β : ft-to a₀ r == idp
    ft-to-β = ap fst= nh 

      where nh : contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r) == idp
            nh = contr-has-all-paths ⦃ =-preserves-contr {x = (a₀ , r)} {y = a₀ , r} is-c ⦄
                      (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r)) idp

    ft-from : (a₁ : A) → a₀ == a₁ → P a₁
    ft-from a₁ p = transport P p r

    ft-to-from : (a₁ : A) (p : a₀ == a₁) → ft-to a₁ (ft-from a₁ p) == p
    ft-to-from a₁ idp = ft-to-β 

    ft-from-to : (a₁ : A) (p : P a₁) → ft-from a₁ (ft-to a₁ p) == p
    ft-from-to a₁ p = to-transp (snd= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))) 

    fundamental-thm : (a₁ : A) → P a₁ ≃ (a₀ == a₁)
    fundamental-thm a₁ = equiv (ft-to a₁) (ft-from a₁) (ft-to-from a₁) (ft-from-to a₁)

    fundamental-thm-β : –> (fundamental-thm a₀) r == idp
    fundamental-thm-β = ft-to-β

  -- module _ {i} (A : Type i) where
  
  --   fibrant-reflexive-rel :  Type (lsucc i)
  --   fibrant-reflexive-rel =
  --     Σ (A → A → Type i) (λ Q →
  --     Σ ((a : A) → Q a a) (λ ρ →
  --     (a₀ : A) → is-contr (Σ A (λ a₁ → Q a₀ a₁))))

  --   id-rel : fibrant-reflexive-rel
  --   id-rel = _==_ , (λ a → idp {a = a}) , pathfrom-is-contr 

  --   id-rel-unique : (Q : fibrant-reflexive-rel) → Q == id-rel
  --   id-rel-unique (Q , ρ , is-fib)  = pair= step1 (↓-Σ-in {!!} (prop-has-all-paths-↓ ⦃ Π-level (λ a → is-contr-is-prop) ⦄ )) 

  --     where step1 : Q == _==_
  --           step1 = λ= (λ a₀ → λ= (λ a₁ → ua (fundamental-thm A (Q a₀) (is-fib a₀) a₀ (ρ a₀) a₁))) 

  --   corollary : ∀ {i} (A : Type i) → is-contr (fibrant-reflexive-rel)
  --   corollary A = has-level-in (id-rel , λ Q → ! (id-rel-unique Q))

