open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Sum 

open import Core.Everything

module Experimental.Representables where

  Repr₋₂ : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) → 𝕆Type n ℓ-zero

  data Face₋₂ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
    → {𝑜' : 𝒪 n} → Frm (Repr₋₂ 𝑜 𝑝) 𝑜' → Type 

  Repr₋₂ ● objₒ = tt*
  Repr₋₂ (𝑜 ∣ 𝑝) 𝑞 = Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞

  outer-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
    → Frm (Repr₋₂ 𝑜 𝑝) 𝑜

  outer-cns : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) 
    → Cns (Repr₋₂ 𝑜 𝑝) (outer-frm 𝑜 𝑝) 𝑝 

  base-cns : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
    → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    → Cns (Repr₋₂ 𝑜 𝑝) (outer-frm 𝑜 𝑝) 𝑝
    → Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) 𝑝

  -- base-face : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (p : Pos 𝑝)
  --   → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟)
  --     (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (base-cns 𝑜 𝑝 𝑞 (outer-cns 𝑜 𝑝)) p)
  -- base-face = ? 

  pos-cns : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
    → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)) (p : Pos 𝑝)
    → Cns (Repr₋₂ (Typ 𝑝 p) (𝑞 p)) (outer-frm (Typ 𝑝 p) (𝑞 p)) (𝑞 p)
    → Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) (μₒ 𝑝 𝑞)

  data Face₋₂ where

    lf-face : {n : ℕ} (𝑜 : 𝒪 n)
      → Face₋₂ (ηₒ 𝑜) lfₒ (outer-frm 𝑜 (ηₒ 𝑜))

    nd-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
      → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (outer-frm 𝑜 (μₒ 𝑝 𝑞))

  outer-frm ● 𝑝 = tt*
  outer-frm (𝑜 ∣ .(ηₒ 𝑜)) lfₒ = outer-frm 𝑜 (ηₒ 𝑜) , lf-face 𝑜 , η (Repr₋₂ 𝑜 (ηₒ 𝑜)) (outer-frm 𝑜 (ηₒ 𝑜)) , const (lf-face 𝑜)
  outer-frm (𝑜 ∣ .(μₒ 𝑝 𝑞)) (ndₒ 𝑝 𝑞 𝑟) = outer-frm 𝑜 (μₒ 𝑝 𝑞) , nd-face 𝑝 𝑞 𝑟 , c , y

    where c : Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) (μₒ 𝑝 𝑞)
          c = {!!} --μ (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) {f = outer-frm 𝑜 (μₒ 𝑝 𝑞)} {!outer-cns 𝑜 𝑝!} {!!}

          y : (p : Pos (μₒ 𝑝 𝑞)) → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) c p)
          y p = {!!}

  outer-cns ● 𝑝 = tt*
  outer-cns (𝑜 ∣ .(ηₒ 𝑜)) lfₒ = lf (lf-face 𝑜)
  outer-cns (𝑜 ∣ .(μₒ 𝑝 𝑞)) (ndₒ 𝑝 𝑞 𝑟) = 
    nd {f = outer-frm 𝑜 (μₒ 𝑝 𝑞)} (nd-face 𝑝 𝑞 𝑟)
        (base-cns 𝑜 𝑝 𝑞 (outer-cns 𝑜 𝑝))
        {!!} {!!} {!!} {!!}
       -- (μ-fst-cns 𝑝 𝑞 𝑟) (μ-fst-dec 𝑝 𝑞 𝑟)
       -- (μ-snd-cns 𝑝 𝑞 𝑟) (μ-snd-dec 𝑝 𝑞 𝑟) (λ p → {!outer-cns 𝑜 𝑝!})

  base-cns = {!!} 
  pos-cns = {!!} 



  -- -- base-map : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → Cns (Repr₋₂ 𝑜 𝑝) (outer-frm 𝑜 𝑝) 𝑝
  -- --   → Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) (μₒ 𝑝 𝑞)
  -- -- base-map = {!!} 

  -- -- pos-map : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)) (p : Pos 𝑝)
  -- --   → Cns (Repr₋₂ (Typ 𝑝 p) (𝑞 p)) (outer-frm (Typ 𝑝 p) (𝑞 p)) (𝑞 p)
  -- --   → Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) (μₒ 𝑝 𝑞)
  -- -- pos-map = {!!} 

  -- base-map : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → Repr₋₂ 𝑜 𝑝 ⇒ Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)
  -- base-map = {!!} 

  -- pos-map : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (p : Pos 𝑝)
  --   → Repr₋₂ (Typ 𝑝 p) (𝑞 p) ⇒ Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)
  -- pos-map = {!!} 

  -- data Face₋₂' : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  --   → {𝑜' : 𝒪 n} → Frm (Repr₋₂ 𝑜 𝑝) 𝑜' → Type where

  --   lf-face : {n : ℕ} (𝑜 : 𝒪 n)
  --     → Face₋₂' (ηₒ 𝑜) lfₒ {!!}

  --   nd-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --     → Face₋₂' (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) {!!}


  -- μ-fst-cns : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --   → Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) 𝑝 

  -- μ-snd-cns : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --   → (p : Pos 𝑝) → Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (μ-fst-cns 𝑝 𝑞 𝑟) p) (𝑞 p)

  -- μ-fst-dec : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --   → (p : Pos 𝑝) → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (μ-fst-cns 𝑝 𝑞 𝑟) p) 

  -- μ-snd-dec :{n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --   → (p : Pos 𝑝) (q : Pos (𝑞 p))
  --   → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (μ-snd-cns 𝑝 𝑞 𝑟 p) q)



  -- data Face₋₂ where

  --   lf-face : {n : ℕ} (𝑜 : 𝒪 n)
  --     → Face₋₂ (ηₒ 𝑜) lfₒ (outer-frm 𝑜 (ηₒ 𝑜))

  --   nd-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  --     → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (outer-frm 𝑜 (μₒ 𝑝 𝑞))

  -- outer-frm ● 𝑝 = tt*
  -- outer-frm (𝑜 ∣ .(ηₒ 𝑜)) lfₒ = outer-frm 𝑜 (ηₒ 𝑜) , lf-face 𝑜 , η (Repr₋₂ 𝑜 (ηₒ 𝑜)) (outer-frm 𝑜 (ηₒ 𝑜)) , const (lf-face 𝑜)
  -- outer-frm (𝑜 ∣ .(μₒ 𝑝 𝑞)) (ndₒ 𝑝 𝑞 𝑟) = outer-frm 𝑜 (μₒ 𝑝 𝑞) , nd-face 𝑝 𝑞 𝑟 , c , y

  -- --   where c : Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) (μₒ 𝑝 𝑞)
  -- --         c = μ (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) {f = outer-frm 𝑜 (μₒ 𝑝 𝑞)} {!outer-cns 𝑜 𝑝!} {!!}

  -- --         y : (p : Pos (μₒ 𝑝 𝑞)) → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) c p)
  -- --         y p = {!!}

  --   where c : Cns (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) (outer-frm 𝑜 (μₒ 𝑝 𝑞)) (μₒ 𝑝 𝑞)
  --         c = μ (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) {f = outer-frm 𝑜 (μₒ 𝑝 𝑞)} {𝑝 = 𝑝} (μ-fst-cns 𝑝 𝑞 𝑟) {𝑞 = 𝑞} (μ-snd-cns 𝑝 𝑞 𝑟)

  --         y : (p : Pos (μₒ 𝑝 𝑞)) → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (Shp (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) c p)
  --         y p = μ-snd-dec 𝑝 𝑞 𝑟 (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p) 

  -- outer-cns ● 𝑝 = tt*
  -- outer-cns (𝑜 ∣ .(ηₒ 𝑜)) lfₒ = lf (lf-face 𝑜)
  -- outer-cns (𝑜 ∣ .(μₒ 𝑝 𝑞)) (ndₒ 𝑝 𝑞 𝑟) = 
  --   nd {f = outer-frm 𝑜 (μₒ 𝑝 𝑞)} (nd-face 𝑝 𝑞 𝑟) 
  --      (μ-fst-cns 𝑝 𝑞 𝑟) (μ-fst-dec 𝑝 𝑞 𝑟)
  --      (μ-snd-cns 𝑝 𝑞 𝑟) (μ-snd-dec 𝑝 𝑞 𝑟) (λ p → {!outer-cns 𝑜 𝑝!})

  -- -- Okay, interesting.  So we need decorating functions, and that's
  -- -- basically going to be force.  And then we'll fall back to
  -- -- grafting and have to have similar combinators, I suppose....

  -- μ-fst-cns objₒ 𝑞 𝑟 = tt*
  -- μ-fst-cns (lfₒ {𝑜 = 𝑜}) 𝑞 𝑟 = lf (lf-face 𝑜)
  -- μ-fst-cns (ndₒ 𝑝 𝑞 𝑟) κ 𝑟𝑟 = {!!}

  -- μ-snd-cns objₒ 𝑞 𝑟 p = tt*
  -- μ-snd-cns (ndₒ 𝑝 𝑞 𝑟) 𝑞𝑞 𝑟𝑟 (inl tt) = {!!}
  -- μ-snd-cns (ndₒ 𝑝 𝑞 𝑟) 𝑞𝑞 𝑟𝑟 (inr (p , q)) = {!!}

  -- μ-fst-dec = {!!} 
  -- μ-snd-dec = {!!} 



  -- -- Repr₋₁ : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) → 𝕆Type (1 + n) ℓ-zero

  -- -- tgt-incl : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --   → Repr₋₁ 𝑜 𝑝 ⇒ Repr₋₂ (𝑜 ∣ 𝑝) 𝑞

  -- -- lf-incl : ∀ {n} (𝑜 : 𝒪 n)
  -- --   → Repr₋₁ 𝑜 (ηₒ 𝑜) ⇒ Repr₋₂ (𝑜 ∣ ηₒ 𝑜) lfₒ

  -- -- nd-incl : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  -- --   → Repr₋₁ 𝑜 (μₒ 𝑝 𝑞) ⇒ Repr₋₂ (𝑜 ∣ μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟)

  -- -- ∂-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Frm (Repr₋₁ 𝑜 𝑝) (𝑜 ∣ 𝑝)


  -- -- data Face₋₁ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --   → {𝑜' : 𝒪 (suc n)} → Frm (Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) 𝑜' → Type 


  -- -- Repr₋₁ ● objₒ = tt* , const Unit
  -- -- Repr₋₁ (𝑜 ∣ 𝑝) 𝑞 = (Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) , Face₋₁ 𝑝 𝑞

  -- -- postulate
  
  -- --   outer-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --     → Frm (Repr₋₂ 𝑜 𝑝) 𝑜


  -- -- data Face₋₁ where

  -- --   src-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  -- --     → Face₋₁ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) {!!} 

  -- --   tgt-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --     → Face₋₁ 𝑝 𝑞 {𝑜' = 𝑜 ∣ 𝑝} (outer-frm 𝑜 𝑝 , {!!} , {!!} , {!!})


  -- -- tgt-incl = {!!} 
  -- -- lf-incl = {!!} 
  -- -- nd-incl = {!!} 
  -- -- ∂-frm = {!!} 



  -- -- outer-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Frm (Repr₋₂ 𝑜 𝑝) 𝑜

  -- -- outer-cns : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Cns (Repr₋₂ 𝑜 𝑝) (outer-frm 𝑜 𝑝) 𝑝

  -- -- base-map : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → Repr₋₂ 𝑜 𝑝 ⇒ Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)
  -- -- base-map = {!!} 

  -- -- pos-map : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → (p : Pos 𝑝)
  -- --   → Repr₋₂ (Typ 𝑝 p) (𝑞 p) ⇒ Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)
  -- -- pos-map = {!!} 

  -- -- ∂-inc : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --   → Repr₋₁ 𝑜 𝑝 ⇒ Repr₋₂ (𝑜 ∣ 𝑝) 𝑞
  -- -- ∂-inc = {!!} 

  -- -- src-inc : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝)) 
  -- --   → (p : Pos 𝑞) → Repr₋₁ {!Typ 𝑞 p!} {!!} ⇒ Repr₋₂ (𝑜 ∣ 𝑝) 𝑞
  -- -- src-inc 𝑝 𝑞 p = {!!} 

  -- -- ∂-frm : {n : ℕ} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Frm (Repr₋₁ 𝑜 𝑝) (𝑜 ∣ 𝑝)
  -- -- ∂-frm 𝑜 𝑝 = {!!} 

  -- -- data Face₋₂ where

  -- --   lf-case : {n : ℕ} (𝑜 : 𝒪 n)
  -- --     → Face₋₂ (ηₒ 𝑜) lfₒ (outer-frm 𝑜 (ηₒ 𝑜))

  -- --   nd-case : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  -- --     → Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) (outer-frm 𝑜 (μₒ 𝑝 𝑞))

  -- -- data Face₋₁ where

  -- --   src-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  -- --     → Face₋₁ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) {𝑜' = 𝑜 ∣ 𝑝} (outer-frm 𝑜 (μₒ 𝑝 𝑞) , nd-case 𝑝 𝑞 𝑟 , {!!} , {!!})

  -- --   tgt-face : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --     → Face₋₁ 𝑝 𝑞 {𝑜' = 𝑜 ∣ 𝑝} {!∂-frm 𝑜 𝑝!}




  -- -- outer-frm = {!!}
  -- -- outer-cns = {!!} 


  -- -- outer-frm .● objₒ = tt*
  -- -- outer-frm .(_ ∣ ηₒ _) (lfₒ {𝑜 = 𝑜}) = outer-frm 𝑜 (ηₒ 𝑜) , lf-case 𝑜 , η (Repr₋₂ 𝑜 (ηₒ 𝑜)) (outer-frm 𝑜 (ηₒ 𝑜)) , const (lf-case 𝑜)
  -- -- outer-frm .(_ ∣ μₒ 𝑝 𝑞) (ndₒ {𝑜 = 𝑜} 𝑝 𝑞 𝑟) = outer-frm 𝑜 (μₒ 𝑝 𝑞) , nd-case 𝑝 𝑞 𝑟 , μ (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) {!Cns⇒ (base-map 𝑜 𝑝 𝑞) (outer-cns 𝑜 𝑝)!} {!!} , {!!} 

  -- -- outer-cns .● objₒ = tt*
  -- -- outer-cns .(_ ∣ ηₒ _) (lfₒ {𝑜 = 𝑜})  = lf {f = outer-frm 𝑜 (ηₒ 𝑜)} (lf-case 𝑜)
  -- -- outer-cns .(_ ∣ μₒ 𝑝 𝑞) (ndₒ {𝑜 = 𝑜} 𝑝 𝑞 𝑟) = {!!}



  -- -- outer-cns : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Cns (Repr₋₂ 𝑜 𝑝) (outer-frm 𝑜 𝑝) 𝑝


  -- -- data NdCns {n ℓ} (X : 𝕆Type (suc n) ℓ)
  -- --       (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --       (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --       (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
        
  -- --   : Frm X (𝑜 ∣ μₒ 𝑝 𝑞) → Type ℓ where

  --   -- nd : {f : Frm (fst X) 𝑜} (x : (snd X) f) (c : Cns (fst X) f 𝑝)
  --   --   → (y : (p : Pos 𝑝) → (snd X) (Shp (fst X) c p))
  --   --   → (d : (p : Pos 𝑝) → Cns (fst X) (Shp (fst X) c p) (𝑞 p))
  --   --   → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → (snd X) (Shp (fst X) (d p) q))
  --   --   → (ψ : (p : Pos 𝑝) → Cns X (Shp (fst X) c p , y p , d p , z p) (𝑟 p)) 
  --   --   → NdCns X 𝑜 𝑝 𝑞 𝑟 (f , x , μ (fst X) c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) 















  -- -- η-frm ● = tt*
  -- -- η-frm (𝑜 ∣ 𝑝) = μ-frm 𝑝 (λ p → ηₒ (Typ 𝑝 p)) ,
  -- --                 nd-case 𝑝 (λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ) ,
  -- --                 {!!} ,
  -- --                 {!!}
  
  -- -- μ-frm objₒ 𝑞 = tt*
  -- -- μ-frm (lfₒ {𝑜 = 𝑜}) 𝑞 = η-frm 𝑜 , lf-case 𝑜 , η (Repr₋₂ 𝑜 (ηₒ 𝑜)) (η-frm 𝑜) , const (lf-case 𝑜)
  -- -- μ-frm (ndₒ 𝑝 𝑞 𝑟) κ = μ-frm 𝑝 𝑞 , {!nd-case 𝑝 𝑞 𝑟!} , {!!} , {!!}


  -- -- μₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → 𝒫 𝑜
  -- -- μₒ objₒ 𝑞 = objₒ
  -- -- μₒ lfₒ 𝑞 = lfₒ
  -- -- μₒ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
  -- --   graftₒ (𝑠 (inl tt))
  -- --     (λ p → μₒ (𝑟 p) (λ q → 𝑠 (inr (p , q))))

  -- -- src-frm : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  -- --   → Frm (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞) , Face₋₂ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟)) (𝑜 ∣ 𝑝) 
  -- -- src-frm = {!!}

  -- -- tgt-frm : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --   → Frm (Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) (𝑜 ∣ 𝑝)
  -- -- tgt-frm = {!!} 

  -- -- data Face₋₁ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --   → {𝑜' : 𝒪 (suc n)} → Frm (Repr₋₂ 𝑜 𝑝 , Face₋₂  𝑝 𝑞) 𝑜' → Type where

  -- --   src-case : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --     → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --     → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
  -- --     → Face₋₁ (μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) {!!} 

  -- --   tgt-case : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 ∣ 𝑝))
  -- --     → Face₋₁ 𝑝 𝑞 {!!}

  -- -- Repr₋₁ ● objₒ = tt* , λ _ → Unit
  -- -- Repr₋₁ (𝑜 ∣ 𝑝) 𝑞 = (Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) , Face₋₁ 𝑝 𝑞

  -- -- Repr ● objₒ = (tt* , λ _ → Unit) , λ _ → Unit
  -- -- Repr (𝑜 ∣ 𝑝) 𝑞 = ((Repr₋₂ 𝑜 𝑝 , Face₋₂ 𝑝 𝑞) , Face₋₁ 𝑝 𝑞) , λ _ → Unit 


  -- -- tgt-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Frm (Repr₋₂ 𝑜 𝑝) 𝑜 

  -- -- src-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) (p : Pos 𝑝)
  -- --   → Frm (Repr₋₂ 𝑜 𝑝) (Typ 𝑝 p)

  -- -- tgt-frm .● objₒ = tt*
  -- -- tgt-frm .(_ ∣ ηₒ _) lfₒ = {!!}
  -- -- tgt-frm .(_ ∣ μₒ 𝑝 𝑞) (ndₒ 𝑝 𝑞 𝑟) = {!!}

  -- -- src-frm = {!!} 

  -- -- tgt-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  -- --   → Frm (Repr₋₂ 𝑜 𝑝) 𝑜 
  -- -- tgt-frm = {!!} 

  -- -- src-frm : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) (p : Pos 𝑝)
  -- --   → Frm (Repr₋₂ 𝑜 𝑝) (Typ 𝑝 p)
  -- -- src-frm = {!!} 

  -- -- η-frm : ∀ {n} (𝑜 : 𝒪 n)
  -- --   → Frm (Repr₋₂ 𝑜 (ηₒ 𝑜)) 𝑜
    
  -- -- μ-frm : ∀ {n} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  -- --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  -- --   → Frm (Repr₋₂ 𝑜 (μₒ 𝑝 𝑞)) 𝑜 
