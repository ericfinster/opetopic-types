open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything

module Experimental.SimpleUniverse where

  -- Interesting!  So this is a really neat idea which avoids having a
  -- separate setup for dependent opetopic types!  Instead, you accept
  -- to have the universe *be* the definition of dependent opetopic
  -- type.

  𝒰ₒ : ∀ {n} → (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)

  el-frm : ∀ {n ℓ} {𝑜 : 𝒪 n} → Frm (𝒰ₒ ℓ) 𝑜 → Type ℓ
  
  el-cns : ∀ {n ℓ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → (f : Frm (𝒰ₒ ℓ) 𝑜) (f↓ : el-frm f)
    → (c : Cns (𝒰ₒ ℓ) f 𝑝) → Type
    
  el-shp : ∀ {n ℓ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → (f : Frm (𝒰ₒ ℓ) 𝑜) (f↓ : el-frm f)
    → (c : Cns (𝒰ₒ ℓ) f 𝑝) (c↓ : el-cns f f↓ c)
    → (p : Pos 𝑝) → el-frm (Shp (𝒰ₒ ℓ) c p) 

  𝒰ₒ {zero} ℓ = tt*
  𝒰ₒ {suc n} ℓ = 𝒰ₒ ℓ , λ f → el-frm f → Type ℓ

  el-frm {zero} {𝑜 = ●} tt* = Lift Unit
  el-frm {suc n} {𝑜 = 𝑜 ∣ 𝑝} (f , X , c , Y) =
    Σ[ f↓ ∈ el-frm f ]
    Σ[ x↓ ∈ X f↓ ]
    Σ[ c↓ ∈ el-cns f f↓ c ]
    ((p : Pos 𝑝) → Y p (el-shp f f↓ c c↓ p))

  el-cns = {!!} 

  el-shp = {!!} 
