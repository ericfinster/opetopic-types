--
--  Scratch.agda - Random things I'm working on 
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything

module Experimental.Scratch where

  μ-test₀ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {f : Frm X 𝑜} (c : Cns X f 𝑝)
    → μ X c (λ p → η X (Shp X c p)) ≡ c
  μ-test₀ X c = refl 

  μ-test₁ : ∀ {n ℓ} (X : 𝕆Type (suc n) ℓ)
    → {𝑜 : 𝒪 (suc n)} {𝑝 : 𝒫 𝑜}
    → {f : Frm X 𝑜} (c : Cns X f 𝑝)
    → μ X c (λ p → η X (Shp X c p)) ≡ {!!}
  μ-test₁ X c = {!!}

  -- Interesting.  So this doesn't even work for opetopes.

  -- On opetopes
  μₒ-test₀ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
    → μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) ≡ 𝑝
  μₒ-test₀ 𝑝 = refl 

  -- Well, I mean now that you stare at it, this isn't an instance of
  -- the above rule, is it?  So this gives me pause as to whether it
  -- can really work for all n.  But yeah, it's an interesting
  -- question...

  -- I mean, maybe it's okay.  The point is that you won't be trying
  -- to match on *exactly* the rule in this form.  Rather, the
  -- equation that you state will normalize to something more
  -- complicated from which the correct values of n should be deduced.

  -- But yeah, I'm curious if you can get a setup where these kinds of
  -- equations hold.
  
  μₒ-test₁ : {n : ℕ} {𝑜 : 𝒪 (suc n)} (𝑝 : 𝒫 𝑜)
    → μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) ≡ 𝑝
  μₒ-test₁ 𝑝 = {!refl!}
