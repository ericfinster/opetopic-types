--
--  Scratch.agda - Random things I'm working on 
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Core.Prelude
open import Core.Everything

module Experimental.Scratch where

  -- --  Can I think of a quick example to understand when these rewrites
  -- -- appply in these unfolding situations?

  -- Fin : ℕ → Type
  -- Fin zero = ⊥
  -- Fin (suc n) = Unit ⊎ Fin n

  -- Fin-plus : {n m : ℕ} → Fin n → Fin m → Fin (n + m)
  -- Fin-plus {suc n} (inl tt) fm = inl tt
  -- Fin-plus {suc n} (inr fn) fm = inr (Fin-plus fn fm)

  -- -- So, here we have a list of types.  What is a reasonable rewrite?
  -- -- Associativity? Unit?  But what do you mean by this? 

  -- data List (A : Type) : Type where
  --   nil : List A
  --   cns : A → List A → List A 


  -- postulate

  --   nat-assoc : (n m p : ℕ)
  --     → ((n + m) + p) ↦ (n + (m + p))
  --   {-# REWRITE nat-assoc #-}

  --   Fin-assoc : ∀ {n m p}
  --     → (fn : Fin n) (fm : Fin m) (fp : Fin p)
  --     → Fin-plus (Fin-plus fn fm) fp ↦
  --       Fin-plus fn (Fin-plus fm fp)
  --   {-# REWRITE Fin-assoc #-}

  --   sizeof : Type → ℕ
    
  --   crazy : (n : ℕ)
  --     → sizeof (Fin n) ↦ 70
  --   {-# REWRITE crazy #-}


  -- -- This shows that having the arguments compute is a problem...
  -- test : ∀ {n m p}
  --   → (fn : Fin (suc n)) (fm : Fin m) (fp : Fin p)
  --   → Fin-plus (Fin-plus fn fm) fp ≡ 
  --     Fin-plus fn (Fin-plus fm fp)
  -- test fn fm fp = {!!}

  -- -- And I think this shows that having a left side which
  -- -- computes is *also* a problem.
  -- crazy-test : (n : ℕ) → sizeof (Fin (suc n)) ≡ 70
  -- crazy-test n = {!sizeof (Fin (suc n))!}

  -- -- Now, is there one where the arguments are fixed, but the reduction
  -- -- happens in the head of the rewrite that you can check? 

  -- -- What do you need? 

  --
  --  The following shows that this definitional equation that you are missing
  --  is trivially provable by induction.  Maybe the solution to your problem
  --  is to accept that this equation is simply propositional? 
  -- 

  fst-shp-test : ∀ {n ℓ₀ ℓ₁} {Xₙ : 𝕆Type n ℓ₀} {Pₙ : 𝕆Fam Xₙ ℓ₁}
    → (Xₛₙ : {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ₀)
    → (Pₛₙ : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} → Frm↓ Pₙ f → Xₛₙ f → Type ℓ₁)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑡 : 𝒫 (𝑜 ∣ 𝑝)} 
    → (f : Frm (Σₒ Xₙ Pₙ , Σ-cell Xₛₙ Pₛₙ) (𝑜 ∣ 𝑝)) (c : Cns (Σₒ Xₙ Pₙ , Σ-cell Xₛₙ Pₛₙ) f 𝑡) (p : Pos 𝑡)
    → Shp (Xₙ , Xₛₙ) (fst-cns c) p ≡ fst-frm (Shp (Σₒ Xₙ Pₙ , Σ-cell Xₛₙ Pₛₙ) c p) 
  fst-shp-test {Xₙ = Xₙ} {Pₙ} Xₛₙ Pₛₙ {𝑜} {𝑡 = ndₒ 𝑡 𝑞 𝑟} ._ (nd x c y d z ψ) (inl tt) = refl
  fst-shp-test {Xₙ = Xₙ} {Pₙ} Xₛₙ Pₛₙ {𝑜} {𝑡 = ndₒ 𝑡 𝑞 𝑟} ._ (nd x c y d z ψ) (inr (p , q)) =
    fst-shp-test Xₛₙ Pₛₙ _ (ψ p) q


