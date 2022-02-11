--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat 
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum 

open import Core.Prelude

module Core.Opetopes where

  --
  --  The Opetopic Polynomials
  --

  {-# NO_POSITIVITY_CHECK #-}
  
  data 𝒪 : ℕ → Type
  data 𝒫 : {n : ℕ} → 𝒪 n → Type
  data Pos : {n : ℕ} {o : 𝒪 n} → 𝒫 o → Type 
  Typ : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o) (p : Pos 𝑝) → 𝒪 n

  --
  --  Monadic Structure
  --
  
  ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o

  ηₒ-pos : {n : ℕ} (o : 𝒪 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : ∀ {ℓ} {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (ηₒ o)) → Type ℓ)
    → (ηₒ-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

  μₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
    → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    → 𝒫 𝑜

  pairₚ : {n : ℕ} {𝑜 : 𝒪 n} 
    → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    → (p : Pos 𝑝) (q : Pos (𝑞 p))
    → Pos (μₒ 𝑝 𝑞)

  fstₚ : {n : ℕ} {𝑜 : 𝒪 n} 
    → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    → Pos (μₒ 𝑝 𝑞) → Pos 𝑝

  sndₚ : {n : ℕ} {𝑜 : 𝒪 n} 
    → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    → (p : Pos (μₒ 𝑝 𝑞)) → Pos (𝑞 (fstₚ 𝑝 𝑞 p))

  --
  --  Polynomial Definitions
  --

  infixl 40 _∣_
  
  data 𝒪 where

    ● : 𝒪 zero
    
    _∣_ : {n : ℕ} (𝑜 : 𝒪 n)
      → (𝑝 : 𝒫 𝑜) → 𝒪 (suc n) 

  data 𝒫 where

    objₒ : 𝒫 ●
    
    lfₒ : {n : ℕ} {𝑜 : 𝒪 n}
      → 𝒫 (𝑜 ∣ ηₒ 𝑜)
      
    ndₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
      → 𝒫 (𝑜 ∣ μₒ 𝑝 𝑞)

  data Pos where

    obj-pos : Pos objₒ

    nd-here : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p)}
      → Pos (ndₒ 𝑝 𝑞 𝑟)

    nd-there : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p)}
      → (p : Pos 𝑝) (q : Pos (𝑟 p)) 
      → Pos (ndₒ 𝑝 𝑞 𝑟)

  Typ ._ obj-pos = ●
  Typ ._ (nd-here {𝑜 = 𝑜} {𝑝}) = 𝑜 ∣ 𝑝
  Typ ._ (nd-there {𝑟 = 𝑟} p q) = Typ (𝑟 p) q

  -- 
  --  Position Laws
  --
  
  postulate
  
    -- ηₒ-pos laws
    ηₒ-pos-typ : {n : ℕ} (o : 𝒪 n)
      → (p : Pos (ηₒ o))
      → Typ (ηₒ o) p ↦ o
    {-# REWRITE ηₒ-pos-typ #-}

    ηₒ-pos-elim-β : ∀ {ℓ} {n : ℕ} (o : 𝒪 n)
      → (X : (p : Pos (ηₒ o)) → Type ℓ)
      → (ηₒ-pos* : X (ηₒ-pos o))
      → ηₒ-pos-elim o X ηₒ-pos* (ηₒ-pos o) ↦ ηₒ-pos*
    {-# REWRITE ηₒ-pos-elim-β #-}

    -- pairₚ laws
    fstₚ-β : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (p : Pos 𝑝) (q : Pos (𝑞 p))
      → fstₚ 𝑝 𝑞 (pairₚ 𝑝 𝑞 p q) ↦ p
    {-# REWRITE fstₚ-β #-}

    sndₚ-β : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (p : Pos 𝑝) (q : Pos (𝑞 p))
      → sndₚ 𝑝 𝑞 (pairₚ 𝑝 𝑞 p q) ↦ q
    {-# REWRITE sndₚ-β #-}
    
    pairₚ-ηₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (p : Pos (μₒ 𝑝 𝑞))
      → pairₚ 𝑝 𝑞 (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p) ↦ p
    {-# REWRITE pairₚ-ηₒ #-}

    pairₚ-typ : {n : ℕ} {𝑜 : 𝒪 n}  (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (p : Pos (μₒ 𝑝 𝑞))
      → Typ (μₒ 𝑝 𝑞) p ↦ Typ (𝑞 (fstₚ 𝑝 𝑞 p)) (sndₚ 𝑝 𝑞 p)
    {-# REWRITE pairₚ-typ #-}

  -- 
  --  Monad Laws
  --

  postulate

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → μₒ 𝑝 (λ p → ηₒ (Typ 𝑝 p)) ↦ 𝑝
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → μₒ (ηₒ 𝑜) ϕ ↦ ϕ (ηₒ-pos 𝑜)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos (μₒ 𝑝 𝑞)) → 𝒫 (Typ (μₒ 𝑝 𝑞) p))
      → μₒ (μₒ 𝑝 𝑞) 𝑟 ↦ μₒ 𝑝 (λ p → μₒ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q)))
    {-# REWRITE μₒ-assoc #-}

  --
  --  Position and Monad Law Compatibilities 
  --

  postulate
  
    -- intro compatibilities
    pairₚ-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos 𝑝) (q : Pos (ηₒ (Typ 𝑝 p)))
      → pairₚ 𝑝 (λ p → ηₒ (Typ 𝑝 p)) p q ↦ p
    {-# REWRITE pairₚ-unit-r #-}

    pairₚ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (𝑝 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → (p : Pos (𝑝 (ηₒ-pos 𝑜)))
      → pairₚ (ηₒ 𝑜) 𝑝 (ηₒ-pos 𝑜) p ↦ p
    {-# REWRITE pairₚ-unit-l #-}

    pairₚ-assoc : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos (μₒ 𝑝 𝑞)) → 𝒫 (Typ (μₒ 𝑝 𝑞) p))    
      → (pq : Pos (μₒ 𝑝 𝑞)) (r : Pos (𝑟 pq))
      → let 𝑟' p = μₒ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q))
            p = fstₚ 𝑝 𝑞 pq
            q = sndₚ 𝑝 𝑞 pq
        in pairₚ (μₒ 𝑝 𝑞) 𝑟 pq r
          ↦ pairₚ 𝑝 𝑟' p
              (pairₚ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q)) q r)
    {-# REWRITE pairₚ-assoc #-} 

    -- first projection compatibilities
    μₒ-fst-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos (μₒ 𝑝 (λ p → ηₒ (Typ 𝑝 p))))
      → fstₚ 𝑝 (λ p → ηₒ (Typ 𝑝 p)) p ↦ p
    {-# REWRITE μₒ-fst-unit-r #-}

    μₒ-fst-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (𝑝 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → (p : Pos (μₒ (ηₒ 𝑜) 𝑝))
      → fstₚ (ηₒ 𝑜) 𝑝 p ↦ ηₒ-pos 𝑜
    {-# REWRITE μₒ-fst-unit-l #-}

    μₒ-fst-assoc : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos (μₒ 𝑝 𝑞)) → 𝒫 (Typ (μₒ 𝑝 𝑞) p))    
      → (pqr : Pos (μₒ (μₒ 𝑝 𝑞) 𝑟))
      → let 𝑟' p = μₒ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q))
            p = fstₚ 𝑝 𝑟' pqr
            qr = sndₚ 𝑝 𝑟' pqr
            q = fstₚ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q)) qr
        in fstₚ (μₒ 𝑝 𝑞) 𝑟 pqr ↦ pairₚ 𝑝 𝑞 p q
    {-# REWRITE μₒ-fst-assoc #-}

    -- second projection compatibilities
    μₒ-snd-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos (μₒ 𝑝 (λ p → ηₒ (Typ 𝑝 p))))
      → sndₚ 𝑝 (λ p → ηₒ (Typ 𝑝 p)) p ↦ ηₒ-pos (Typ 𝑝 p)
    {-# REWRITE μₒ-snd-unit-r #-}

    μₒ-snd-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (𝑝 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → (p : Pos (μₒ (ηₒ 𝑜) 𝑝))
      → sndₚ (ηₒ 𝑜) 𝑝 p ↦ p 
    {-# REWRITE μₒ-snd-unit-l #-}

    μₒ-snd-assoc : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos (μₒ 𝑝 𝑞)) → 𝒫 (Typ (μₒ 𝑝 𝑞) p))    
      → (pqr : Pos (μₒ (μₒ 𝑝 𝑞) 𝑟))
      → let 𝑟' p = μₒ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q))
            p = fstₚ 𝑝 𝑟' pqr
            qr = sndₚ 𝑝 𝑟' pqr
        in sndₚ (μₒ 𝑝 𝑞) 𝑟 pqr ↦ sndₚ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q)) qr
    {-# REWRITE μₒ-snd-assoc #-}

  --
  --  Grafting 
  --

  graftₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (𝑠 : 𝒫 (𝑜 ∣ 𝑝))
    → (𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
    → 𝒫 (𝑜 ∣ μₒ 𝑝 𝑞)
  graftₒ (lfₒ {𝑜 = 𝑜}) 𝑡 = 𝑡 (ηₒ-pos 𝑜)
  graftₒ {𝑞 = 𝑟} (ndₒ 𝑝 𝑞 ε) 𝑡 = 
    ndₒ 𝑝 (λ p → μₒ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q)))
        (λ p → graftₒ (ε p) (λ q → 𝑡 (pairₚ 𝑝 𝑞 p q)))

  inlₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (𝑠 : 𝒫 (𝑜 ∣ 𝑝))
    → (𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
    → Pos 𝑠 → Pos (graftₒ 𝑠 𝑡)
  inlₒ ._ 𝑡 nd-here = nd-here
  inlₒ ._ 𝑡 (nd-there {𝑝 = 𝑝} {𝑞} {𝑟} u v) = 
    nd-there u (inlₒ (𝑟 u) (λ q → 𝑡 (pairₚ 𝑝 𝑞 u q)) v)

  inrₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (𝑠 : 𝒫 (𝑜 ∣ 𝑝))
    → (𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
    → (p : Pos 𝑝) (q : Pos (𝑡 p))
    → Pos (graftₒ 𝑠 𝑡)
  inrₒ (lfₒ {𝑜 = 𝑜}) 𝑡 = 
    ηₒ-pos-elim 𝑜 (λ p → Pos (𝑡 p) → Pos (𝑡 (ηₒ-pos 𝑜))) (λ p → p) 
  inrₒ (ndₒ 𝑝 𝑞 𝑟) 𝑡 u v = 
    let u₀ = fstₚ 𝑝 𝑞 u
        u₁ = sndₚ 𝑝 𝑞 u
    in nd-there u₀ (inrₒ (𝑟 u₀) (λ q → 𝑡 (pairₚ 𝑝 𝑞 u₀ q)) u₁ v)

  graftₒ-pos-elim : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (𝑠 : 𝒫 (𝑜 ∣ 𝑝))
    → (𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
    → (X : Pos (graftₒ 𝑠 𝑡) → Type ℓ)
    → (inl* : (p : Pos 𝑠) → X (inlₒ 𝑠 𝑡 p))
    → (inr* : (p : Pos 𝑝) (q : Pos (𝑡 p)) → X (inrₒ 𝑠 𝑡 p q))
    → (p : Pos (graftₒ 𝑠 𝑡)) → X p
  graftₒ-pos-elim lfₒ 𝑡 X inl* inr* p = inr* (ηₒ-pos _) p
  graftₒ-pos-elim (ndₒ 𝑝 𝑞 𝑟) 𝑡 X inl* inr* nd-here = inl* nd-here
  graftₒ-pos-elim (ndₒ 𝑝 𝑞 𝑟) 𝑡 X inl* inr* (nd-there u v) = 
    graftₒ-pos-elim (𝑟 u) (λ q → 𝑡 (pairₚ 𝑝 𝑞 u q)) 
      (λ q → X (nd-there u q))
      (λ q → inl* (nd-there u q))
      (λ p q → inr* (pairₚ 𝑝 𝑞 u p) q) v
      
  --
  --  Grafting Laws
  --

  postulate

    graftₒ-pos-elim-inl-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (𝑠 : 𝒫 (𝑜 ∣ 𝑝))
      → (𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
      → (X : Pos (graftₒ 𝑠 𝑡) → Type ℓ)
      → (inl* : (p : Pos 𝑠) → X (inlₒ 𝑠 𝑡 p))
      → (inr* : (p : Pos 𝑝) (q : Pos (𝑡 p)) → X (inrₒ 𝑠 𝑡 p q))
      → (p : Pos 𝑠)
      → graftₒ-pos-elim 𝑠 𝑡 X inl* inr* (inlₒ 𝑠 𝑡 p) ↦ inl* p
    {-# REWRITE graftₒ-pos-elim-inl-β #-}

    graftₒ-pos-elim-inr-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (𝑠 : 𝒫 (𝑜 ∣ 𝑝))
      → (𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
      → (X : Pos (graftₒ 𝑠 𝑡) → Type ℓ)
      → (inl* : (p : Pos 𝑠) → X (inlₒ 𝑠 𝑡 p))
      → (inr* : (p : Pos 𝑝) (q : Pos (𝑡 p)) → X (inrₒ 𝑠 𝑡 p q))
      → (p : Pos 𝑝) (q : Pos (𝑡 p))
      → graftₒ-pos-elim 𝑠 𝑡 X inl* inr* (inrₒ 𝑠 𝑡 p q) ↦ inr* p q
    {-# REWRITE graftₒ-pos-elim-inr-β #-}

  --
  --  Monad Implementation 
  --

  -- ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o
  ηₒ {zero} ● = objₒ
  ηₒ {suc n} (o ∣ 𝑝) =
    ndₒ 𝑝 (λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ)

  -- ηₒ-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (ηₒ o)
  ηₒ-pos {zero} ● = obj-pos 
  ηₒ-pos {suc n} (o ∣ 𝑝) = nd-here

  -- ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (ηₒ o)) → Type)
  --   → (ηₒ-pos* : X (ηₒ-pos o))
  --   → (p : Pos (ηₒ o)) → X p
  ηₒ-pos-elim {n = zero} .● X ηₒ-pos* obj-pos = ηₒ-pos*
  ηₒ-pos-elim {n = suc n} (o ∣ 𝑝) X ηₒ-pos* nd-here = ηₒ-pos*

  -- μₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
  --   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → 𝒫 𝑜
  μₒ objₒ 𝑞 = objₒ
  μₒ lfₒ 𝑞 = lfₒ
  μₒ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
    graftₒ (𝑠 nd-here)
      (λ p → μₒ (𝑟 p) (λ q → 𝑠 (nd-there p q)))

  -- pairₚ : {n : ℕ} {𝑜 : 𝒪 n} 
  --   → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (p : Pos 𝑝) (q : Pos (𝑞 p))
  --   → Pos (μₒ 𝑝 𝑞)
  pairₚ objₒ 𝑠 p q = obj-pos
  pairₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 nd-here r =
    inlₒ (𝑠 nd-here)
      (λ p → μₒ (𝑟 p) (λ q → 𝑠 (nd-there p q))) r
  pairₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 (nd-there p q) r =
    inrₒ (𝑠 nd-here)
      (λ p → μₒ (𝑟 p) (λ q → 𝑠 (nd-there p q))) p
        (pairₚ (𝑟 p) (λ q → 𝑠 (nd-there p q)) q r ) 

  -- fstₚ : {n : ℕ} {𝑜 : 𝒪 n} 
  --   → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → Pos (μₒ 𝑝 𝑞) → Pos 𝑝
  fstₚ objₒ 𝑞 p = obj-pos
  fstₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
    graftₒ-pos-elim (𝑠 nd-here) (λ p → μₒ (𝑟 p) (λ q → 𝑠 (nd-there p q))) _
      (const nd-here) (λ p q → nd-there p (fstₚ (𝑟 p) (λ q → 𝑠 (nd-there p q)) q))

  -- sndₚ : {n : ℕ} {𝑜 : 𝒪 n} 
  --   → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (p : Pos (μₒ 𝑝 𝑞)) → Pos (𝑞 (fstₚ 𝑝 𝑞 p))
  sndₚ objₒ 𝑞 obj-pos with 𝑞 obj-pos
  sndₚ objₒ 𝑞 obj-pos | objₒ = obj-pos
  sndₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
    graftₒ-pos-elim (𝑠 nd-here) (λ p → μₒ (𝑟 p) (λ q → 𝑠 (nd-there p q))) _
      (λ p → p) (λ p q → sndₚ (𝑟 p) (λ q → 𝑠 (nd-there p q)) q)
      
  --
  --  Examples
  --

  obj : 𝒪 0
  obj = ●

  arrow : 𝒪 1
  arrow = ● ∣ objₒ 

  2-drop : 𝒪 2
  2-drop = ● ∣ objₒ ∣ lfₒ 

  2-globe : 𝒪 2
  2-globe = ● ∣ objₒ ∣ ndₒ objₒ (λ { obj-pos → objₒ }) (λ { obj-pos → lfₒ })

  2-simplex : 𝒪 2
  2-simplex = ● ∣ objₒ ∣ ndₒ objₒ (λ { obj-pos → objₒ }) (λ { obj-pos →
                           ndₒ objₒ (λ { obj-pos → objₒ }) (λ { obj-pos → lfₒ }) })
  
