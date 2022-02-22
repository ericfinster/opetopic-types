open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything
open import Lib.Structures
open import Lib.Universe

module Experimental.FibrantUniverse where

  -- Right, so this I think is now correct.  Just needs to be cleaned up
  -- and written in a way which is comprehensible....
  CompRel : ∀ {n ℓ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑡 : 𝒫 (𝑜 ∣ 𝑝)}
    → (f : Frm (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) 𝑜)
    → (X : Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel) f)
    → (c : Cns (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) f 𝑝)
    → (Y : (p : Pos 𝑝) →
           Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel)
           (Shp (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) c p))
    → (ω : Cns
        (Σₒ (𝒰ₒ n ℓ) (ℱₒ n) ,
         Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel))
        (f , X , c , Y) 𝑡)
    → (R : (p : Pos 𝑡) →
        Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n , (λ f↓ X₁ → X₁ f↓)) f₁ → Type ℓ)
        (λ _ → is-fibrant-rel)
        (Shp
         (Σₒ (𝒰ₒ n ℓ) (ℱₒ n) ,
          Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel))
         ω p))
    → Frm↓ (𝒱ₒ (suc n)) {𝑜 = 𝑜 ∣ 𝑝} (fst-frm (f , X , c , Y))
    → Type ℓ 
  CompRel {n} {ℓ} {𝑜 = 𝑜} {𝑝} {𝑡} f X c Y ω R f↓ =  
    Σ[ ω↓ ∈ Cns↓ (𝒱ₒ (suc n)) f↓ (fst-cns {P = ℱₒ (suc n)} ω) ]  
    ((p : Pos 𝑡) → fstₒ (R p) {!(Shp↓ (𝒱ₒ (suc n)) ω↓ p)!}) 


  thm : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (suc (suc (suc n))) ℓ)
  thm n ℓ {𝑜 ∣ 𝑝} {𝑡} {f , X , c , Y} ω R =
    ((CompRel f X c Y ω R , {!!}) , {!!}) , {!!}


