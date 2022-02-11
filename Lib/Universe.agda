--
--  OpetopicType.agda - Definition of Opetopic Types in Context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything
open import Lib.Structures 

module Lib.Universe where

  -- The universe as an opetopic type 
  𝒰ₒ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒱ₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ

  𝒰ₒ zero ℓ = lift tt
  𝒰ₒ (suc n) ℓ = 𝒰ₒ n ℓ , λ f → Frm↓ (𝒱ₒ n) f → Type ℓ
  
  𝒱ₒ zero = lift tt
  𝒱ₒ (suc n) = 𝒱ₒ n , λ f↓ X → X f↓

  --
  --  Let's get set up for some of the main theorems
  --

  is-fibrant-rel : ∀ {n ℓ} {𝑜 : 𝒪 n} {f : Frm (𝒰ₒ n ℓ) 𝑜}
    → (X : Frm↓ (𝒱ₒ n) f → Type ℓ) → Type ℓ
  is-fibrant-rel {zero} X = Lift Unit
  is-fibrant-rel {suc n} {𝑜 = 𝑜 , 𝑝} {f , Xₙ , c , Yₙ} R = 
    (f↓ : Frm↓ (𝒱ₒ n) f) (c↓ : Cns↓ (𝒱ₒ n) f↓ c)
    (y↓ : (p : Pos 𝑝) → Yₙ p (Shp↓ (𝒱ₒ n) c↓ p))
     → isContr (Σ[ x↓ ∈ Xₙ f↓ ] R (f↓ , x↓ , c↓ , y↓)) 

  -- The dependent type of fibrancy
  ℱₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ
  ℱₒ zero = tt*
  ℱₒ (suc n) = ℱₒ n , λ _ X → is-fibrant-rel X
  
  -- We can now define the (∞,1)-category of spaces:
  𝒮ₙ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮ₙ n ℓ = Σₒ (𝒰ₒ n ℓ) (ℱₒ n) 

