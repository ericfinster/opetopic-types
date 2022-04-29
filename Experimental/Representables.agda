open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything

module Experimental.Representables where


  Repr : ∀ {n}  (𝑜 : 𝒪 n) → 𝕆Type (suc n) ℓ-zero

  -- "Pos q ⊔ Pos r"
  data Codim2Face {n} (𝑜 : 𝒪 n) : (𝑝 : 𝒫 𝑜)  (𝑞 : 𝒫 (𝑜 ∣ 𝑝)) (𝑟 : 𝒫 (𝑜 ∣ 𝑝 ∣ 𝑞))
      → {𝑜' : 𝒪 (suc n)} → Frm (fst (fst (Repr (𝑜 ∣ 𝑝 ∣ 𝑞)))) 𝑜' → Type where

  -- "Pos r ⊔ 1"
  data Codim1Face {n} (𝑜 : 𝒪 n) : (𝑝 : 𝒫 𝑜)  (𝑞 : 𝒫 (𝑜 ∣ 𝑝)) (𝑟 : 𝒫 (𝑜 ∣ 𝑝 ∣ 𝑞))
      → {𝑜' : 𝒪 (suc (suc n))} → Frm (fst (fst (Repr (𝑜 ∣ 𝑝 ∣ 𝑞))) , Codim2Face 𝑜 𝑝 𝑞 𝑟) 𝑜' → Type where



  Repr ● = tt* , λ f → Unit                                    -- object
  Repr (● ∣ objₒ) = {!!}                                       -- arrow 
  Repr (● ∣ objₒ ∣ 𝑞) = {!!}                                   -- 2d n-gon 
  Repr (𝑜 ∣ 𝑝 ∣ 𝑞 ∣ 𝑟) =
    ((fst (fst (Repr (𝑜 ∣ 𝑝 ∣ 𝑞))) , Codim2Face 𝑜 𝑝 𝑞 𝑟) , Codim1Face 𝑜 𝑝 𝑞 𝑟) , λ _ → Unit   

