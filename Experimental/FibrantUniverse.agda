open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything
open import Lib.Structures
open import Lib.Universe

module Experimental.FibrantUniverse where

  -- Right, so this I think is now correct.  Just needs to be cleaned up
  -- and written in a way which is comprehensible....
  CompRel : ∀ {n ℓ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑡 : 𝒯r 𝑝}
    → (f : Frm (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) 𝑜)
    → (X : Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel) f)
    → (c : Cns (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) f 𝑝)
    → (Y : (p : Pos 𝑝) →
           Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel)
           (Shp (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) c p))
    → (ω : Web (Σₒ (𝒰ₒ n ℓ) (ℱₒ n))
           (Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel))
           (f , X , c , Y) 𝑡)
    → (R : (p : 𝒯rPos 𝑡) →
         snd (fst (𝒮ₙ (suc (suc (suc n))) ℓ))
         (Shp (fst (fst (𝒮ₙ (suc (suc (suc n))) ℓ))) ω p))
    → Frm↓ (𝒱ₒ (suc n)) (fst-frm (f , X , c , Y))
    → Type ℓ 
  CompRel {n} {𝑡 = 𝑡} f X c Y ω R f↓ = 
    Σ[ ω↓ ∈ Cns↓ (𝒱ₒ (suc n)) f↓ (fst-cns {P = ℱₒ (suc n)} ω) ] 
    ((p : 𝒯rPos 𝑡) → fstₒ (R p) {!(Shp (𝒰ₒ n _ , (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type _)) (fst-cns ω) p) !})  -- (Shp↓ (𝒱ₒ (suc n)) ω↓ p)

-- fst (Shp (𝒰ₒ (suc n) ℓ) (fst-cns ω) p) !=
-- fst-frm (fst (Shp (fst (fst (𝒮ₙ (suc (suc (suc n))) ℓ))) ω p)) of

-- normalized
-- fst (Shp (𝒰ₒ n ℓ , (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ)) (fst-cns ω) p)
-- fst-frm (fst (Shp (Σₒ (𝒰ₒ n ℓ) (ℱₒ n) , Σ-cell (λ f₁ → Frm↓ (𝒱ₒ n) f₁ → Type ℓ) (λ _ → is-fibrant-rel)) ω p))

    -- fst-shp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    --   → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (f : Frm (Σₒ X P) 𝑜)
    --   → (c : Cns (Σₒ X P) f 𝑝) (p : Pos 𝑝)
    --   → Shp X (fst-cns c) p ↦ fst-frm (Shp (Σₒ X P) c p) 
    -- {-# REWRITE fst-shp #-}
    
    -- snd-shp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    --   → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (f : Frm (Σₒ X P) 𝑜)
    --   → (c : Cns (Σₒ X P) f 𝑝) (p : Pos 𝑝)
    --   → Shp↓ P (snd-cns c) p ↦ snd-frm (Shp (Σₒ X P) c p) 
    -- {-# REWRITE snd-shp #-} 


  thm : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (suc (suc (suc n))) ℓ)
  thm n ℓ {𝑜 , 𝑝} {𝑡} {f , X , c , Y} ω R =
    (({!!} , {!!}) , {!!}) , {!!}


