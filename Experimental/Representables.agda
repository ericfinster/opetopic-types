open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Sum 

open import Core.Everything

module Experimental.Representables where

  target : ∀ {n} → 𝒪 (suc n) → 𝒪 n
  target (𝑜 ∣ 𝑝) = 𝑜
  
  Repr₋₂ : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) → 𝕆Type n ℓ-zero
  -- Repr₋₁ : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) → 𝕆Type (1 + n) ℓ-zero
  -- Repr : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) → 𝕆Type (2 + n) ℓ-zero

  η-frm : ∀ {n} (𝑜 : 𝒪 n)
    → Frm (Repr₋₂ 𝑜 (ηₒ 𝑜)) 𝑜
    
  μ-frm : ∀ {n} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
    → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    → Frm (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) 𝑜 

  data Face₋₂ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
    → {𝑜' : 𝒪 n} → Frm (Repr₋₂ 𝑜 𝑝) 𝑜' → Type where

    lf-case : {n : ℕ} (𝑜 : 𝒪 n)
      → Face₋₂ (ηₒ 𝑜) lfₒ (η-frm 𝑜)

    nd-case : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
      → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (μ-frm 𝑝 𝑞) 


  Repr₋₂ ● objₒ = tt*
  Repr₋₂ (𝑜 ∣ 𝑝) 𝑞 = Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞

  η-frm ● = tt*
  η-frm (𝑜 ∣ 𝑝) = μ-frm 𝑝 (λ p → ηₒ (Typ 𝑝 p)) ,
                  nd-case 𝑝 (λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ) ,
                  {!!} ,
                  {!!}
  
  μ-frm objₒ 𝑞 = tt*
  μ-frm (lfₒ {𝑜 = 𝑜}) 𝑞 = η-frm 𝑜 , lf-case 𝑜 , η (Repr₋₂ 𝑜 (ηₒ 𝑜)) (η-frm 𝑜) , const (lf-case 𝑜)
  μ-frm (ndₒ 𝑝 𝑞 𝑟) κ = μ-frm 𝑝 𝑞 , {!!} , {!!} , {!!}


  -- μₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → 𝒫 𝑜
  -- μₒ objₒ 𝑞 = objₒ
  -- μₒ lfₒ 𝑞 = lfₒ
  -- μₒ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
  --   graftₒ (𝑠 (inl tt))
  --     (λ p → μₒ (𝑟 p) (λ q → 𝑠 (inr (p , q))))



  -- src-frm : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --   → Frm (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞) , Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟)) (𝑜 ∣ 𝑝) 
  -- src-frm = {!!}

  -- tgt-frm : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  --   → Frm (Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) (𝑜 ∣ 𝑝)
  -- tgt-frm = {!!} 

  -- data Face₋₁ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  --   → {𝑜' : 𝒪 (suc n)} → Frm (Repr₋₂ 𝑜 𝑝 , Face₋₂  𝑝 𝑞) 𝑜' → Type where

  --   src-case : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --     → Face₋₁ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) {!!} 

  --   tgt-case : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  --     → Face₋₁ 𝑝 𝑞 {!!}

  -- Repr₋₁ ● objₒ = tt* , λ _ → Unit
  -- Repr₋₁ (𝑜 ∣ 𝑝) 𝑞 = (Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) , Face₋₁ 𝑝 𝑞

  -- Repr ● objₒ = (tt* , λ _ → Unit) , λ _ → Unit
  -- Repr (𝑜 ∣ 𝑝) 𝑞 = ((Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) , Face₋₁ 𝑝 𝑞) , λ _ → Unit 


  -- tgt-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  --   → Frm (Repr₋₂ 𝑜 𝑝) 𝑜 

  -- src-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) (p : Pos 𝑝)
  --   → Frm (Repr₋₂ 𝑜 𝑝) (Typ 𝑝 p)

  -- tgt-frm .● objₒ = tt*
  -- tgt-frm .(_ ∣ ηₒ _) lfₒ = {!!}
  -- tgt-frm .(_ ∣ μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) = {!!}

  -- src-frm = {!!} 

