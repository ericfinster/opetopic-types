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

  {-# TERMINATING #-}
  
  --
  --  The Opetopic Polynomials
  --
  
  𝒪 : ℕ → Type
  𝒫 : {n : ℕ} → 𝒪 n → Type
  Pos : {n : ℕ} {o : 𝒪 n} → 𝒫 o → Type 
  Typ : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o) (p : Pos 𝑝) → 𝒪 n

  --
  --  The slice construction
  -- 

  data 𝒯r {n : ℕ} : (𝑜 : 𝒪 (suc n)) → Type
  𝒯rPos : {n : ℕ} {𝑜 : 𝒪 (suc n)} → 𝒯r 𝑜 → Type 
  𝒯rTyp : {n : ℕ} {𝑜 : 𝒪 (suc n)} (𝑡 : 𝒯r 𝑜) (p : 𝒯rPos 𝑡) → 𝒪 (suc n)

  --
  --  Polynomial Definitions
  --

  𝒪 zero = Unit
  𝒪 (suc n) = Σ (𝒪 n) 𝒫
  
  𝒫 {zero} _ = Unit
  𝒫 {suc n} = 𝒯r
  
  Pos {zero} _ = Unit
  Pos {suc n} = 𝒯rPos
  
  Typ {zero} _ _ = tt
  Typ {suc n} = 𝒯rTyp

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

  postulate

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
  
  --   -- intro compatibilities
  --   pairₚ-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
  --     → (p : Pos 𝑝) (q : Pos (ηₒ (Typ 𝑝 p)))
  --     → pairₚ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p q ↦ p
  --   {-# REWRITE pairₚ-unit-r #-}

  --   pairₚ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
  --     → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
  --     → (q : Pos (ϕ (ηₒ-pos 𝑜)))
  --     → pairₚ (ηₒ 𝑜 , ϕ) (ηₒ-pos 𝑜) q ↦ q 
  --   {-# REWRITE pairₚ-unit-l #-}

  --   pairₚ-assoc : {n : ℕ} {o : 𝒪 n} 
  --     → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
  --     → (pq : Pos (μₒ 𝑝)) (r : Pos (ε pq))
  --     → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q))
  --           p = fstₚ 𝑝 pq
  --           q = sndₚ 𝑝 pq
  --       in pairₚ (μₒ 𝑝 , ε) pq r
  --         ↦ pairₚ (fst 𝑝 , ε')
  --             p (pairₚ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)) q r)
  --   {-# REWRITE pairₚ-assoc #-} 

  --   -- first projection compatibilities
  --   μₒ-fst-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
  --     → (p : Pos (μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p))))
  --     → fstₚ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p ↦ p
  --   {-# REWRITE μₒ-fst-unit-r #-}

  --   μₒ-fst-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
  --     → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
  --     → (p : Pos (μₒ (ηₒ 𝑜 , ϕ)))
  --     → fstₚ (ηₒ 𝑜 , ϕ) p ↦ ηₒ-pos 𝑜
  --   {-# REWRITE μₒ-fst-unit-l #-}

  --   μₒ-fst-assoc : {n : ℕ} {o : 𝒪 n} 
  --     → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
  --     → (pqr : Pos (μₒ (μₒ 𝑝 , ε)))
  --     → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q))
  --           p = fstₚ (fst 𝑝 , ε') pqr
  --           qr = sndₚ (fst 𝑝 , ε') pqr
  --           q = fstₚ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)) qr
  --       in fstₚ (μₒ 𝑝 , ε) pqr ↦ pairₚ 𝑝 p q
  --   {-# REWRITE μₒ-fst-assoc #-}

  --   -- second projection compatibilities
  --   μₒ-snd-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
  --     → (p : Pos (μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p))))
  --     → sndₚ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p ↦ ηₒ-pos (Typ 𝑝 p)
  --   {-# REWRITE μₒ-snd-unit-r #-}

  --   μₒ-snd-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
  --     → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
  --     → (p : Pos (μₒ (ηₒ 𝑜 , ϕ)))
  --     → sndₚ (ηₒ 𝑜 , ϕ) p ↦ p 
  --   {-# REWRITE μₒ-snd-unit-l #-}

  --   μₒ-snd-assoc : {n : ℕ} {o : 𝒪 n} 
  --     → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
  --     → (pqr : Pos (μₒ (μₒ 𝑝 , ε)))
  --     → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q))
  --           p = fstₚ (fst 𝑝 , ε') pqr
  --           qr = sndₚ (fst 𝑝 , ε') pqr
  --       in sndₚ (μₒ 𝑝 , ε) pqr ↦ sndₚ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)) qr
  --   {-# REWRITE μₒ-snd-assoc #-}

  --
  --  Implementation of the slice polynomial
  --

  data 𝒯r {n} where
    lfₒ : {𝑜 : 𝒪 n} → 𝒯r (𝑜 , ηₒ 𝑜)
    ndₒ : {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (ε : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p , 𝑞 p))
      → 𝒯r (𝑜 , μₒ 𝑝 𝑞)
      
  𝒯rPos lfₒ = ⊥
  𝒯rPos (ndₒ 𝑝 𝑞 ε) =
    Unit ⊎ Σ (Pos 𝑝) (λ p → 𝒯rPos (ε p)) 
  
  𝒯rTyp (ndₒ {𝑜} 𝑝 𝑞 ε) (inl tt) = 𝑜 , 𝑝
  𝒯rTyp (ndₒ 𝑝 𝑞 ε) (inr (p , q)) = 𝒯rTyp (ε p) q

  corolla : {n : ℕ} → (𝑜 : 𝒪 (suc n)) → 𝒯r 𝑜
  corolla (𝑜 , 𝑝) = ndₒ 𝑝 (λ p → ηₒ (Typ 𝑝 p))
                          (λ p → lfₒ)

  corolla-pos : {n : ℕ} → (𝑜 : 𝒪 (suc n))
    → 𝒯rPos (corolla 𝑜)
  corolla-pos (𝑜 , 𝑝) = inl tt 
    
  --
  --  Grafting 
  --

  graftₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (𝑠 : 𝒯r (𝑜 , 𝑝))
    → (𝑡 : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p , 𝑞 p))
    → 𝒯r (𝑜 , μₒ 𝑝 𝑞)
  graftₒ (lfₒ {𝑜}) 𝑡 = 𝑡 (ηₒ-pos 𝑜)
  graftₒ {𝑞 = 𝑟} (ndₒ 𝑝 𝑞 ε) 𝑡 = 
    ndₒ 𝑝 (λ p → μₒ (𝑞 p) (λ q → 𝑟 (pairₚ 𝑝 𝑞 p q)))
        (λ p → graftₒ (ε p) (λ q → 𝑡 (pairₚ 𝑝 𝑞 p q)))

  substₒ : {n : ℕ} {𝑜 : 𝒪 (suc n)} (𝑠 : 𝒯r 𝑜)
    → (𝑡 : (p : 𝒯rPos 𝑠) → 𝒯r (𝒯rTyp 𝑠 p))
    → 𝒯r 𝑜
  substₒ lfₒ 𝑡 = lfₒ
  substₒ (ndₒ 𝑝 𝑞 ε) 𝑡 = 
    graftₒ (𝑡 (inl tt))
      (λ p → μₒ (ε p) (λ q → 𝑡 (inr (p , q))))

  -- inlₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
  --   → (𝑡 : 𝒯r (fst 𝑝))
  --   → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
  --   → 𝒯rPos 𝑡 → 𝒯rPos (graftₒ 𝑡 ψ)
  -- inlₒ (ndₒ 𝑝 ε) ψ (inl tt) = inl tt
  -- inlₒ {𝑝 = ._ , ϕ} (ndₒ (𝑝 , 𝑑) ε) ψ (inr (u , v)) = 
  --   inr (u , inlₒ (ε u) (λ q → ψ (pairₚ (𝑝 , 𝑑) u q)) v)

  -- inrₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
  --   → (𝑡 : 𝒯r (fst 𝑝))
  --   → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
  --   → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p))
  --   → 𝒯rPos (graftₒ 𝑡 ψ)
  -- inrₒ {𝑜 = 𝑜} lfₒ ψ =
  --   ηₒ-pos-elim 𝑜 (λ p → 𝒯rPos (ψ p) → 𝒯rPos (ψ (ηₒ-pos 𝑜))) (λ p → p) 
  -- inrₒ (ndₒ 𝑝 ε) ψ u v = 
  --   let u₀ = fstₚ 𝑝 u
  --       u₁ = sndₚ 𝑝 u
  --   in inr (u₀ , inrₒ (ε u₀) (λ q → ψ (pairₚ 𝑝 u₀ q)) u₁ v)

  -- graftₒ-pos-elim : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
  --   → (𝑡 : 𝒯r (fst 𝑝))
  --   → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
  --   → (X : 𝒯rPos (graftₒ 𝑡 ψ) → Type ℓ)
  --   → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
  --   → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
  --   → (p : 𝒯rPos (graftₒ 𝑡 ψ)) → X p
  -- graftₒ-pos-elim lfₒ ψ X inl* inr* p = inr* (ηₒ-pos _) p
  -- graftₒ-pos-elim (ndₒ 𝑝 ε) ψ X inl* inr* (inl tt) = inl* (inl tt)
  -- graftₒ-pos-elim (ndₒ 𝑝 ε) ψ X inl* inr* (inr (u , v)) = 
  --   graftₒ-pos-elim (ε u) (λ q → ψ (pairₚ 𝑝 u q)) 
  --     (λ q → X (inr (u , q)))
  --     (λ q → inl* (inr (u , q)))
  --     (λ p q → inr* (pairₚ 𝑝 u p) q) v
      
  -- --
  -- --  Grafting Laws
  -- --

  -- postulate

  --   graftₒ-pos-elim-inl-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
  --     → (𝑡 : 𝒯r (fst 𝑝))
  --     → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
  --     → (X : 𝒯rPos (graftₒ 𝑡 ψ) → Type ℓ)
  --     → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
  --     → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
  --     → (p : 𝒯rPos 𝑡)
  --     → graftₒ-pos-elim 𝑡 ψ X inl* inr* (inlₒ 𝑡 ψ p) ↦ inl* p
  --   {-# REWRITE graftₒ-pos-elim-inl-β #-}

  --   graftₒ-pos-elim-inr-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
  --     → (𝑡 : 𝒯r (fst 𝑝))
  --     → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
  --     → (X : 𝒯rPos (graftₒ 𝑡 ψ) → Type ℓ)
  --     → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
  --     → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
  --     → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p))
  --     → graftₒ-pos-elim 𝑡 ψ X inl* inr* (inrₒ 𝑡 ψ p q) ↦ inr* p q
  --   {-# REWRITE graftₒ-pos-elim-inr-β #-}

  --   -- TODO : More grafting laws...

  -- ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o
  ηₒ {zero} _ = tt
  ηₒ {suc n} = corolla 

  -- ηₒ-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (ηₒ o)
  ηₒ-pos {zero} _ = tt
  ηₒ-pos {suc n} = corolla-pos

  -- ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (ηₒ o)) → Type)
  --   → (ηₒ-pos* : X (ηₒ-pos o))
  --   → (p : Pos (ηₒ o)) → X p
  ηₒ-pos-elim {n = zero} o X ηₒ-pos* tt = ηₒ-pos*
  ηₒ-pos-elim {n = suc n} o X ηₒ-pos* (inl tt) = ηₒ-pos*

  -- μₒ : {n : ℕ} {o : 𝒪 n} → ⟦ 𝒫 ⟧ₒ o → 𝒫 o
  μₒ {zero} _ _ = tt
  μₒ {suc n} = substₒ 

  -- -- pairₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  -- --   → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
  -- --   → Pos (μₒ 𝑝)
  -- pairₚ {zero} (𝑝 , 𝑑) p q = tt
  -- pairₚ {suc n} (ndₒ 𝑝 ε , 𝑑) (inl tt) r = 
  --   let 𝑡 = 𝑑 (inl tt)
  --       Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
  --   in inlₒ 𝑡 Ψ r  
  -- pairₚ {suc n} (ndₒ 𝑝 ε , 𝑑) (inr (p , q)) r =
  --   let 𝑡 = 𝑑 (inl tt)
  --       Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
  --   in inrₒ 𝑡 Ψ p (pairₚ (ε p , λ q → 𝑑 (inr (p , q))) q r) 

  -- -- fstₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  -- --   → Pos (μₒ 𝑝) → Pos (fst 𝑝)
  -- fstₚ {zero} (𝑝 , 𝑑) p = tt
  -- fstₚ {suc n} (ndₒ 𝑝 ε , 𝑑) = 
  --   let 𝑡 = 𝑑 (inl tt)
  --       Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
  --   in graftₒ-pos-elim 𝑡 Ψ _ (const (inl tt))
  --        (λ p q → inr (p , fstₚ (ε p , λ q → 𝑑 (inr (p , q))) q))

  -- -- sndₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  -- --   → (p : Pos (μₒ 𝑝)) → Pos (snd 𝑝 (fstₚ 𝑝 p))
  -- sndₚ {zero} (𝑝 , 𝑑) p = tt
  -- sndₚ {suc n} (ndₒ 𝑝 ε , 𝑑) = 
  --   let 𝑡 = 𝑑 (inl tt)
  --       Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
  --   in graftₒ-pos-elim 𝑡 Ψ _ (λ p → p)
  --        (λ p q → sndₚ (ε p , λ q → 𝑑 (inr (p , q))) q)

  -- --
  -- --  Examples
  -- --

  -- obj : 𝒪 0
  -- obj = tt

  -- arrow : 𝒪 1
  -- arrow = tt , tt

  -- 2-drop : 𝒪 2
  -- 2-drop = (tt , tt) , lfₒ 

  -- 2-globe : 𝒪 2
  -- 2-globe = (tt , tt) , ndₒ (tt , λ _ → tt) (λ _ → lfₒ)

  -- 2-simplex : 𝒪 2
  -- 2-simplex = (tt , tt) , ndₒ (tt , λ _ → tt) (λ p → ndₒ (tt , λ _ → tt) (λ _ → lfₒ))

