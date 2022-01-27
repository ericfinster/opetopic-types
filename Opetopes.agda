--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat 
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum 

open import Prelude

module Opetopes where

  --
  --  The Opetopic Polynomials
  --
  
  𝒪 : ℕ → Type
  𝒫 : {n : ℕ} → 𝒪 n → Type
  Pos : {n : ℕ} {o : 𝒪 n} → 𝒫 o → Type 
  Typ : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o) (p : Pos 𝑝) → 𝒪 n

  --
  --  Decorations and the extensions
  --
  
  Decₒ : ∀ {n ℓ} (X : 𝒪 n → Type ℓ) {𝑜 : 𝒪 n} → 𝒫 𝑜 → Type ℓ
  Decₒ X 𝑝 = (p : Pos 𝑝) → X (Typ 𝑝 p) 

  ⟦_⟧ₒ : ∀ {n ℓ} (P : 𝒪 n → Type ℓ) → 𝒪 n → Type ℓ
  ⟦ P ⟧ₒ 𝑜 = Σ (𝒫 𝑜) (Decₒ P) 

  --
  --  Monadic signature
  --

  ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o

  ηₒ-pos : {n : ℕ} (o : 𝒪 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : ∀ {ℓ} {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (ηₒ o)) → Type ℓ)
    → (ηₒ-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p
  
  {-# TERMINATING #-}
  μₒ : {n : ℕ} {o : 𝒪 n} → ⟦ 𝒫 ⟧ₒ o → 𝒫 o

  pairₒ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
    → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
    → Pos (μₒ 𝑝)

  fstₒ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
    → Pos (μₒ 𝑝) → Pos (fst 𝑝)

  sndₒ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
    → (p : Pos (μₒ 𝑝)) → Pos (snd 𝑝 (fstₒ 𝑝 p))

  -- 
  --  Monadic Laws
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

    -- pairₒ laws
    fstₒ-β : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
      → fstₒ 𝑝 (pairₒ 𝑝 p q) ↦ p
    {-# REWRITE fstₒ-β #-}

    sndₒ-β : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
      → sndₒ 𝑝 (pairₒ 𝑝 p q) ↦ q
    {-# REWRITE sndₒ-β #-}
    
    pairₒ-ηₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (μₒ 𝑝))
      → pairₒ 𝑝 (fstₒ 𝑝 p) (sndₒ 𝑝 p) ↦ p
    {-# REWRITE pairₒ-ηₒ #-}

    pairₒ-typ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (μₒ 𝑝))
      → Typ (μₒ 𝑝) p ↦ Typ (snd 𝑝 (fstₒ 𝑝 p)) (sndₒ 𝑝 p)
    {-# REWRITE pairₒ-typ #-}

  --
  --  Monad action on families (not sure we need this ...)
  --

  ηₘ : ∀ {ℓ n} → (X : 𝒪 n → Type ℓ)
    → {𝑜 : 𝒪 n} → X 𝑜 → ⟦ X ⟧ₒ 𝑜
  ηₘ X {𝑜} x = ηₒ 𝑜 , const x

  μₘ : ∀ {ℓ n} → (X : 𝒪 n → Type ℓ)
    → {𝑜 : 𝒪 n} → ⟦ ⟦ X ⟧ₒ ⟧ₒ 𝑜 → ⟦ X ⟧ₒ 𝑜
  μₘ X {𝑜} (𝑝 , 𝑑) = μₒ (𝑝 , fst ∘ 𝑑) , λ p → snd (𝑑 (fstₒ _ p)) (sndₒ _ p) 

  postulate

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) ↦ 𝑝
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → μₒ (ηₒ 𝑜 , ϕ) ↦ ϕ (ηₒ-pos 𝑜)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → μₒ (μₒ 𝑝 , ε) ↦ μₒ (fst 𝑝 , λ p → μₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q)))
    {-# REWRITE μₒ-assoc #-}

    -- intro compatibilities
    pairₒ-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos 𝑝) (q : Pos (ηₒ (Typ 𝑝 p)))
      → pairₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p q ↦ p
    {-# REWRITE pairₒ-unit-r #-}

    pairₒ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → (q : Pos (ϕ (ηₒ-pos 𝑜)))
      → pairₒ (ηₒ 𝑜 , ϕ) (ηₒ-pos 𝑜) q ↦ q 
    {-# REWRITE pairₒ-unit-l #-}

    pairₒ-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → (pq : Pos (μₒ 𝑝)) (r : Pos (ε pq))
      → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q))
            p = fstₒ 𝑝 pq
            q = sndₒ 𝑝 pq
        in pairₒ (μₒ 𝑝 , ε) pq r
          ↦ pairₒ (fst 𝑝 , ε')
              p (pairₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q)) q r)
    {-# REWRITE pairₒ-assoc #-} 

    -- first projection compatibilities
    μₒ-fst-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos (μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p))))
      → fstₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p ↦ p
    {-# REWRITE μₒ-fst-unit-r #-}

    μₒ-fst-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → (p : Pos (μₒ (ηₒ 𝑜 , ϕ)))
      → fstₒ (ηₒ 𝑜 , ϕ) p ↦ ηₒ-pos 𝑜
    {-# REWRITE μₒ-fst-unit-l #-}

    μₒ-fst-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → (pqr : Pos (μₒ (μₒ 𝑝 , ε)))
      → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q))
            p = fstₒ (fst 𝑝 , ε') pqr
            qr = sndₒ (fst 𝑝 , ε') pqr
            q = fstₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q)) qr
        in fstₒ (μₒ 𝑝 , ε) pqr ↦ pairₒ 𝑝 p q
    {-# REWRITE μₒ-fst-assoc #-}

    -- second projection compatibilities
    μₒ-snd-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos (μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p))))
      → sndₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p ↦ ηₒ-pos (Typ 𝑝 p)
    {-# REWRITE μₒ-snd-unit-r #-}

    μₒ-snd-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → (p : Pos (μₒ (ηₒ 𝑜 , ϕ)))
      → sndₒ (ηₒ 𝑜 , ϕ) p ↦ p 
    {-# REWRITE μₒ-snd-unit-l #-}

    μₒ-snd-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → (pqr : Pos (μₒ (μₒ 𝑝 , ε)))
      → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q))
            p = fstₒ (fst 𝑝 , ε') pqr
            qr = sndₒ (fst 𝑝 , ε') pqr
        in sndₒ (μₒ 𝑝 , ε) pqr ↦ sndₒ (snd 𝑝 p , λ q → ε (pairₒ 𝑝 p q)) qr
    {-# REWRITE μₒ-snd-assoc #-}

  --
  --  Trees and Grafting 
  --

  data 𝒯r {n : ℕ} {o : 𝒪 n} : (𝑝 : 𝒫 o) → Type where
    lfₒ : 𝒯r (ηₒ o)
    ndₒ : (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → 𝒯r (μₒ 𝑝)

  𝒯rPos : {n : ℕ} {o : 𝒪 n} {𝑝 : 𝒫 o} → 𝒯r 𝑝 → Type 
  𝒯rPos lfₒ = ⊥
  𝒯rPos (ndₒ 𝑝 ε) = Unit ⊎ Σ (Pos (fst 𝑝)) (λ p → 𝒯rPos (ε p)) 

  𝒯rTyp : {n : ℕ} {o : 𝒪 n} {𝑝 : 𝒫 o} (σ : 𝒯r 𝑝) (p : 𝒯rPos σ) → Σ (𝒪 n) 𝒫
  𝒯rTyp lfₒ ()
  𝒯rTyp (ndₒ 𝓅 ε) (inl tt) = _ , fst 𝓅 
  𝒯rTyp (ndₒ 𝓅 ε) (inr (p , q)) = 𝒯rTyp (ε p) q

  γₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → 𝒯r (μₒ 𝑝)
  γₒ lfₒ ψ = ψ (ηₒ-pos _)
  γₒ {𝑝 = ._ , ϕ} (ndₒ (𝑝 , 𝑑) ε) ψ =
    ndₒ (𝑝 , λ p → μₒ (𝑑 p , λ q → ϕ (pairₒ (𝑝 , 𝑑) p q)))
        (λ p → γₒ (ε p) (λ q → ψ (pairₒ (𝑝 , 𝑑) p q)))

  inlₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → 𝒯rPos 𝑡 → 𝒯rPos (γₒ 𝑡 ψ)
  inlₒ (ndₒ 𝑝 ε) ψ (inl tt) = inl tt
  inlₒ {𝑝 = ._ , ϕ} (ndₒ (𝑝 , 𝑑) ε) ψ (inr (u , v)) = 
    inr (u , inlₒ (ε u) (λ q → ψ (pairₒ (𝑝 , 𝑑) u q)) v)

  inrₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p))
    → 𝒯rPos (γₒ 𝑡 ψ)
  inrₒ {𝑜 = 𝑜} lfₒ ψ =
    ηₒ-pos-elim 𝑜 (λ p → 𝒯rPos (ψ p) → 𝒯rPos (ψ (ηₒ-pos 𝑜))) (λ p → p) 
  inrₒ (ndₒ 𝑝 ε) ψ u v = 
    let u₀ = fstₒ 𝑝 u
        u₁ = sndₒ 𝑝 u
    in inr (u₀ , inrₒ (ε u₀) (λ q → ψ (pairₒ 𝑝 u₀ q)) u₁ v)

  γₒ-pos-elim : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → (X : 𝒯rPos (γₒ 𝑡 ψ) → Type ℓ)
    → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
    → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
    → (p : 𝒯rPos (γₒ 𝑡 ψ)) → X p
  γₒ-pos-elim lfₒ ψ X inl* inr* p = inr* (ηₒ-pos _) p
  γₒ-pos-elim (ndₒ 𝑝 ε) ψ X inl* inr* (inl tt) = inl* (inl tt)
  γₒ-pos-elim (ndₒ 𝑝 ε) ψ X inl* inr* (inr (u , v)) = 
    γₒ-pos-elim (ε u) (λ q → ψ (pairₒ 𝑝 u q)) 
      (λ q → X (inr (u , q)))
      (λ q → inl* (inr (u , q)))
      (λ p q → inr* (pairₒ 𝑝 u p) q) v
      
  --
  --  Grafting Laws
  --

  postulate

    γₒ-pos-elim-inl-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
      → (𝑡 : 𝒯r (fst 𝑝))
      → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → (X : 𝒯rPos (γₒ 𝑡 ψ) → Type ℓ)
      → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
      → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
      → (p : 𝒯rPos 𝑡)
      → γₒ-pos-elim 𝑡 ψ X inl* inr* (inlₒ 𝑡 ψ p) ↦ inl* p
    {-# REWRITE γₒ-pos-elim-inl-β #-}

    γₒ-pos-elim-inr-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
      → (𝑡 : 𝒯r (fst 𝑝))
      → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → (X : 𝒯rPos (γₒ 𝑡 ψ) → Type ℓ)
      → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
      → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
      → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p))
      → γₒ-pos-elim 𝑡 ψ X inl* inr* (inrₒ 𝑡 ψ p q) ↦ inr* p q
    {-# REWRITE γₒ-pos-elim-inr-β #-}

    -- TODO : More grafting laws...

  --
  --  Opetopes 
  --

  𝒪 zero = Unit
  𝒪 (suc n) = Σ (𝒪 n) 𝒫

  𝒫 {zero} _ = Unit
  𝒫 {suc n} (o , p) = 𝒯r p

  Pos {zero} _ = Unit
  Pos {suc n} 𝑝 = 𝒯rPos 𝑝
  
  Typ {zero} _ _ = tt
  Typ {suc n} 𝑝 p = 𝒯rTyp 𝑝 p

  -- ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o
  ηₒ {zero} _ = tt
  ηₒ {suc n} (o , 𝑝) =
    ndₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ)

  -- ηₒ-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (ηₒ o)
  ηₒ-pos {zero} _ = tt
  ηₒ-pos {suc n} (o , 𝑝) = inl tt

  -- ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (ηₒ o)) → Type)
  --   → (ηₒ-pos* : X (ηₒ-pos o))
  --   → (p : Pos (ηₒ o)) → X p
  ηₒ-pos-elim {n = zero} o X ηₒ-pos* tt = ηₒ-pos*
  ηₒ-pos-elim {n = suc n} o X ηₒ-pos* (inl tt) = ηₒ-pos*

  -- μₒ : {n : ℕ} {o : 𝒪 n} → ⟦ 𝒫 ⟧ₒ o → 𝒫 o
  μₒ {zero} (𝑝 , 𝑑) = tt
  μₒ {suc n} (lfₒ , 𝑑) = lfₒ
  μₒ {suc n} (ndₒ 𝑝 ε , 𝑑) =
    let 𝑡 = 𝑑 (inl tt)
        Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
    in γₒ 𝑡 Ψ

  -- pairₒ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  --   → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
  --   → Pos (μₒ 𝑝)
  pairₒ {zero} (𝑝 , 𝑑) p q = tt
  pairₒ {suc n} (ndₒ 𝑝 ε , 𝑑) (inl tt) r = 
    let 𝑡 = 𝑑 (inl tt)
        Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
    in inlₒ 𝑡 Ψ r  
  pairₒ {suc n} (ndₒ 𝑝 ε , 𝑑) (inr (p , q)) r =
    let 𝑡 = 𝑑 (inl tt)
        Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
    in inrₒ 𝑡 Ψ p (pairₒ (ε p , λ q → 𝑑 (inr (p , q))) q r) 

  -- fstₒ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  --   → Pos (μₒ 𝑝) → Pos (fst 𝑝)
  fstₒ {zero} (𝑝 , 𝑑) p = tt
  fstₒ {suc n} (ndₒ 𝑝 ε , 𝑑) = 
    let 𝑡 = 𝑑 (inl tt)
        Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
    in γₒ-pos-elim 𝑡 Ψ _ (const (inl tt))
         (λ p q → inr (p , fstₒ (ε p , λ q → 𝑑 (inr (p , q))) q))

  -- sndₒ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  --   → (p : Pos (μₒ 𝑝)) → Pos (snd 𝑝 (fstₒ 𝑝 p))
  sndₒ {zero} (𝑝 , 𝑑) p = tt
  sndₒ {suc n} (ndₒ 𝑝 ε , 𝑑) = 
    let 𝑡 = 𝑑 (inl tt)
        Ψ p = μₒ (ε p , λ q → 𝑑 (inr (p , q)))
    in γₒ-pos-elim 𝑡 Ψ _ (λ p → p)
         (λ p q → sndₒ (ε p , λ q → 𝑑 (inr (p , q))) q)

  --
  --  Examples
  --

  obj : 𝒪 0
  obj = tt

  arrow : 𝒪 1
  arrow = tt , tt

  2-drop : 𝒪 2
  2-drop = (tt , tt) , lfₒ 

  2-globe : 𝒪 2
  2-globe = (tt , tt) , ndₒ (tt , λ _ → tt) (λ _ → lfₒ)

  2-simplex : 𝒪 2
  2-simplex = (tt , tt) , ndₒ (tt , λ _ → tt) (λ p → ndₒ (tt , λ _ → tt) (λ _ → lfₒ))
