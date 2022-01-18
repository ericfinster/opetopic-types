{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module Opetopes where

  --
  --  The Opetopic Polynomials
  --
  
  𝒪 : ℕ → Set
  𝒫 : {n : ℕ} → 𝒪 n → Set
  Pos : {n : ℕ} {o : 𝒪 n} → 𝒫 o → Set 
  Typ : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o) (p : Pos ρ) → 𝒪 n

  --
  --  Monadic signature
  --

  ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o

  ηₒ-pos : {n : ℕ} (o : 𝒪 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : ∀ {ℓ} {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (ηₒ o)) → Set ℓ)
    → (ηₒ-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

  -- To fix the termination issue, you should define "subst"
  -- independently of dimension as you have now done for 𝒯rPos and
  -- 𝒯rTyp.
  
  {-# TERMINATING #-}
  μₒ : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
    → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → 𝒫 o

  μₒ-pos : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
    → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → (p : Pos ρ) (q : Pos (κ p))
    → Pos (μₒ ρ κ)

  μₒ-pos-fst : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
    → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → Pos (μₒ ρ κ) → Pos ρ

  μₒ-pos-snd : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
    → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → (p : Pos (μₒ ρ κ)) → Pos (κ (μₒ-pos-fst ρ κ p))

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
      → (X : (p : Pos (ηₒ o)) → Set ℓ)
      → (ηₒ-pos* : X (ηₒ-pos o))
      → ηₒ-pos-elim o X ηₒ-pos* (ηₒ-pos o) ↦ ηₒ-pos*
    {-# REWRITE ηₒ-pos-elim-β #-}

    -- μₒ-pos laws
    μₒ-pos-fst-β : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (p : Pos ρ) (q : Pos (κ p))
      → μₒ-pos-fst ρ κ (μₒ-pos ρ κ p q) ↦ p
    {-# REWRITE μₒ-pos-fst-β #-}

    μₒ-pos-snd-β : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (p : Pos ρ) (q : Pos (κ p))
      → μₒ-pos-snd ρ κ (μₒ-pos ρ κ p q) ↦ q
    {-# REWRITE μₒ-pos-snd-β #-}
    
    μₒ-pos-ηₒ : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (p : Pos (μₒ ρ κ))
      → μₒ-pos ρ κ (μₒ-pos-fst ρ κ p) (μₒ-pos-snd ρ κ p) ↦ p
    {-# REWRITE μₒ-pos-ηₒ #-}

    μₒ-pos-typ : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (p : Pos (μₒ ρ κ))
      → Typ (μₒ ρ κ) p ↦ Typ (κ (μₒ-pos-fst ρ κ p)) (μₒ-pos-snd ρ κ p)
    {-# REWRITE μₒ-pos-typ #-}

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → μₒ ρ (λ p → ηₒ (Typ ρ p)) ↦ ρ
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {o : 𝒪 n}
      → (ϕ : (p : Pos (ηₒ o)) → 𝒫 (Typ (ηₒ o) p))
      → μₒ (ηₒ o) ϕ ↦ ϕ (ηₒ-pos o)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (θ : (p : Pos (μₒ ρ κ)) → 𝒫 (Typ (μₒ ρ κ) p))
      → μₒ (μₒ ρ κ) θ ↦ μₒ ρ (λ p → μₒ (κ p) (λ t → θ (μₒ-pos ρ κ p t)))
    {-# REWRITE μₒ-assoc #-}

    -- intro compatibilities
    μₒ-pos-unit-r : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (p : Pos ρ) (q : Pos (ηₒ (Typ ρ p)))
      → μₒ-pos ρ (λ p → ηₒ (Typ ρ p)) p q ↦ p
    {-# REWRITE μₒ-pos-unit-r #-}

    μₒ-pos-unit-l : {n : ℕ} {o : 𝒪 n}
      → (ϕ : (p : Pos (ηₒ o)) → 𝒫 (Typ (ηₒ o) p))
      → (q : Pos (ϕ (ηₒ-pos o)))
      → μₒ-pos (ηₒ o) ϕ (ηₒ-pos o) q ↦ q 
    {-# REWRITE μₒ-pos-unit-l #-}

    μₒ-pos-assoc : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (θ : (p : Pos (μₒ ρ κ)) → 𝒫 (Typ (μₒ ρ κ) p))
      → (pq : Pos (μₒ ρ κ)) (r : Pos (θ pq))
      → let p = μₒ-pos-fst ρ κ pq
            q = μₒ-pos-snd ρ κ pq
        in μₒ-pos (μₒ ρ κ) θ pq r
          ↦ μₒ-pos ρ (λ p → μₒ (κ p) (λ t → θ (μₒ-pos ρ κ p t)))
             p (μₒ-pos (κ p) (λ q → θ (μₒ-pos ρ κ p q)) q r)
    {-# REWRITE μₒ-pos-assoc #-}

    -- first projection compatibilities
    μₒ-fst-unit-r : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (p : Pos (μₒ ρ (λ p → ηₒ (Typ ρ p))))
      → μₒ-pos-fst ρ (λ p → ηₒ (Typ ρ p)) p ↦ p
    {-# REWRITE μₒ-fst-unit-r #-}

    μₒ-fst-unit-l : {n : ℕ} {o : 𝒪 n}
      → (ϕ : (p : Pos (ηₒ o)) → 𝒫 (Typ (ηₒ o) p))
      → (p : Pos (μₒ (ηₒ o) ϕ))
      → μₒ-pos-fst (ηₒ o) ϕ p ↦ ηₒ-pos o
    {-# REWRITE μₒ-fst-unit-l #-}

    μₒ-fst-assoc : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (θ : (p : Pos (μₒ ρ κ)) → 𝒫 (Typ (μₒ ρ κ) p))
      → (pqr : Pos (μₒ (μₒ ρ κ) θ))
      → let κ' p = μₒ (κ p) (λ t → θ (μₒ-pos ρ κ p t))
            p = μₒ-pos-fst ρ κ' pqr
            qr = μₒ-pos-snd ρ κ' pqr
            q = μₒ-pos-fst (κ p) (λ q → θ (μₒ-pos ρ κ p q)) qr
        in μₒ-pos-fst (μₒ ρ κ) θ pqr ↦ μₒ-pos ρ κ p q 
    {-# REWRITE μₒ-fst-assoc #-}
    
    -- second projection compatibilities
    μₒ-snd-unit-r : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (p : Pos (μₒ ρ (λ p → ηₒ (Typ ρ p))))
      → μₒ-pos-snd ρ (λ p → ηₒ (Typ ρ p)) p ↦ ηₒ-pos (Typ ρ p)
    {-# REWRITE μₒ-snd-unit-r #-}

    μₒ-snd-unit-l : {n : ℕ} {o : 𝒪 n}
      → (ϕ : (p : Pos (ηₒ o)) → 𝒫 (Typ (ηₒ o) p))
      → (p : Pos (μₒ (ηₒ o) ϕ))
      → μₒ-pos-snd (ηₒ o) ϕ p ↦ p 
    {-# REWRITE μₒ-snd-unit-l #-}

    μₒ-snd-assoc : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
      → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (θ : (p : Pos (μₒ ρ κ)) → 𝒫 (Typ (μₒ ρ κ) p))
      → (pqr : Pos (μₒ (μₒ ρ κ) θ))
      → let κ' p = μₒ (κ p) (λ t → θ (μₒ-pos ρ κ p t))
            p = μₒ-pos-fst ρ κ' pqr
            qr = μₒ-pos-snd ρ κ' pqr
        in μₒ-pos-snd (μₒ ρ κ) θ pqr
            ↦ μₒ-pos-snd (κ p) (λ q → θ (μₒ-pos ρ κ p q)) qr
    {-# REWRITE μₒ-snd-assoc #-} 

  --
  --  Trees and Grafting 
  --

  data 𝒯r {n : ℕ} : (o : 𝒪 n) (ρ : 𝒫 o) → Set where

    lfₒ : (o : 𝒪 n) → 𝒯r o (ηₒ o)
    
    ndₒ : (o : 𝒪 n) (ρ : 𝒫 o) 
      → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
      → 𝒯r o (μₒ ρ δ)

  𝒯rPos : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} → 𝒯r o ρ → Set 
  𝒯rPos (lfₒ o) = ∅
  𝒯rPos (ndₒ o ρ δ ε) =
    ⊤ ⊔ (Σ (Pos ρ) (λ p → 𝒯rPos (ε p)))

  𝒯rTyp : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} (σ : 𝒯r o ρ) (p : 𝒯rPos σ) → Σ (𝒪 n) 𝒫
  𝒯rTyp (lfₒ _) ()
  𝒯rTyp (ndₒ o ρ δ ε) (inl tt) = o , ρ
  𝒯rTyp (ndₒ o ρ δ ε) (inr (p , q)) = 𝒯rTyp (ε p) q

  γₒ : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} (τ : 𝒯r o ρ)
    → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    → 𝒯r o (μₒ ρ δ)
  γₒ (lfₒ o) ϕ ψ = ψ (ηₒ-pos o)
  γₒ (ndₒ o ρ δ ε) ϕ ψ = 
    let ϕ' p q = ϕ (μₒ-pos ρ δ p q)
        ψ' p q = ψ (μₒ-pos ρ δ p q)
        δ' p = μₒ (δ p) (ϕ' p)
        ε' p = γₒ (ε p) (ϕ' p) (ψ' p) 
    in ndₒ o ρ δ' ε'

  γₒ-pos-inl : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} (τ : 𝒯r o ρ)
    → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    → 𝒯rPos τ → 𝒯rPos (γₒ τ δ ε)
  γₒ-pos-inl (ndₒ o ρ δ ε) ϕ ψ (inl tt) = inl tt
  γₒ-pos-inl (ndₒ o ρ δ ε) ϕ ψ (inr (u , v)) = 
    let ϕ' p q = ϕ (μₒ-pos ρ δ p q)
        ψ' p q = ψ (μₒ-pos ρ δ p q)
    in inr (u , γₒ-pos-inl (ε u) (ϕ' u) (ψ' u) v) 

  γₒ-pos-inr : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} (τ : 𝒯r o ρ)
    → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    → (p : Pos ρ) (q : 𝒯rPos (ε p))
    → 𝒯rPos (γₒ τ δ ε)
  γₒ-pos-inr (lfₒ o) ϕ ψ =
    ηₒ-pos-elim o (λ p → 𝒯rPos (ψ p) → 𝒯rPos (ψ (ηₒ-pos o))) (λ p → p) 
  γₒ-pos-inr (ndₒ o ρ δ ε) ϕ ψ u v = 
    let ϕ' p q = ϕ (μₒ-pos ρ δ p q)
        ψ' p q = ψ (μₒ-pos ρ δ p q)
        u₀ = μₒ-pos-fst ρ δ u
        u₁ = μₒ-pos-snd ρ δ u
    in inr (u₀ , γₒ-pos-inr (ε u₀) (ϕ' u₀) (ψ' u₀) u₁ v) 

  γₒ-pos-elim : ∀ {ℓ} {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} (τ : 𝒯r o ρ)
    → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    → (X : 𝒯rPos (γₒ τ δ ε) → Set ℓ)
    → (left : (p : 𝒯rPos τ) → X (γₒ-pos-inl τ δ ε p))
    → (right : (p : Pos ρ) (q : 𝒯rPos (ε p)) → X (γₒ-pos-inr τ δ ε p q))
    → (p : 𝒯rPos (γₒ τ δ ε)) → X p
  γₒ-pos-elim (lfₒ o) ϕ ψ X left right p = right (ηₒ-pos o) p
  γₒ-pos-elim (ndₒ o ρ δ ε) ϕ ψ X left right (inl tt) = left (inl tt)
  γₒ-pos-elim (ndₒ o ρ δ ε) ϕ ψ X left right (inr (u , v)) = 
    let ϕ' p q = ϕ (μₒ-pos ρ δ p q)
        ψ' p q = ψ (μₒ-pos ρ δ p q)
    in γₒ-pos-elim (ε u) (ϕ' u) (ψ' u)
         (λ q → X (inr (u , q)))
         (λ q → left (inr (u , q)))
         (λ p q → right (μₒ-pos ρ δ u p) q) v
    
  --
  --  Grafting Laws
  --

  postulate
  
    -- γₒ elim rules
    γₒ-pos-elim-inl-β : ∀ {ℓ} {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (υ : 𝒯r o ρ)
      → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
      → (X : 𝒯rPos (γₒ υ δ ε) → Set ℓ)
      → (left : (p : 𝒯rPos υ) → X (γₒ-pos-inl υ δ ε p))
      → (right : (p : Pos ρ) (q : 𝒯rPos (ε p)) → X (γₒ-pos-inr υ δ ε p q))
      → (p : 𝒯rPos υ)
      → γₒ-pos-elim υ δ ε X left right (γₒ-pos-inl υ δ ε p) ↦ left p
    {-# REWRITE γₒ-pos-elim-inl-β #-}

    γₒ-pos-elim-inr-β : ∀ {ℓ} {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (υ : 𝒯r o ρ)
      → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
      → (X : 𝒯rPos (γₒ υ δ ε) → Set ℓ)
      → (left : (p : 𝒯rPos υ) → X (γₒ-pos-inl υ δ ε p))
      → (right : (p : Pos ρ) (q : 𝒯rPos (ε p)) → X (γₒ-pos-inr υ δ ε p q))
      → (p : Pos ρ) (q : 𝒯rPos (ε p))
      → γₒ-pos-elim υ δ ε X left right (γₒ-pos-inr υ δ ε p q) ↦ right p q
    {-# REWRITE γₒ-pos-elim-inr-β #-}

    -- Interesting that these are not needed with the current arrangement ...
    
    -- γₒ pos laws
    -- γₒ-pos-inl-typ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (υ : 𝒯r o ρ)
    --   → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    --   → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    --   → (p : 𝒯rPos υ)
    --   → 𝒯rTyp (γₒ o ρ υ δ ε) (γₒ-pos-inl o ρ υ δ ε p) ↦ 𝒯rTyp υ p
    -- {-# REWRITE γₒ-pos-inl-typ #-}

    -- γₒ-pos-inr-typ : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (υ : 𝒯r o ρ)
    --   → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    --   → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    --   → (p : Pos ρ) (q : 𝒯rPos (ε p))
    --   → 𝒯rTyp (γₒ o ρ υ δ ε) (γₒ-pos-inr o ρ υ δ ε p q) ↦ 𝒯rTyp (ε p) q
    -- {-# REWRITE γₒ-pos-inr-typ #-}

    -- γₒ laws
    -- γₒ-unit-r : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (υ : 𝒯r o ρ)
    --   → γₒ υ (λ p → ηₒ (Typ ρ p)) (λ p → lfₒ (Typ ρ p)) ↦ υ 
    -- {-# REWRITE γₒ-unit-r #-}

    -- γₒ-assoc : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (τ : 𝒯r o ρ)
    --   → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
    --   → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
    --   → (ϕ : (p : Pos (μₒ ρ δ))  → 𝒫 (Typ (μₒ ρ δ) p))
    --   → (ψ : (p : Pos (μₒ ρ δ)) → 𝒯r (Typ (μₒ ρ δ) p) (ϕ p))
    --   → let ϕ' p q = ϕ (μₒ-pos ρ δ p q)
    --         ψ' p q = ψ (μₒ-pos ρ δ p q)
    --         δ' p = μₒ (δ p) (ϕ' p)
    --         ε' p = γₒ (ε p) (ϕ' p) (ψ' p)
    --     in γₒ (γₒ τ δ ε) ϕ ψ
    --         ↦ γₒ τ δ' ε'
    -- {-# REWRITE γₒ-assoc #-} 

  --
  --  Opetopes 
  --

  𝒪 O = ⊤
  𝒪 (S n) = Σ (𝒪 n) 𝒫

  𝒫 {O} _ = ⊤
  𝒫 {S n} (o , p) = 𝒯r o p

  Pos {O} _ = ⊤
  Pos {S n} ρ = 𝒯rPos ρ
  
  Typ {O} _ _ = tt
  Typ {S n} ρ p = 𝒯rTyp ρ p

  -- ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o
  ηₒ {O} _ = tt
  ηₒ {S n} (o , ρ) =
    ndₒ o ρ (λ p → ηₒ (Typ ρ p))
           (λ p → lfₒ (Typ ρ p))

  -- ηₒ-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (ηₒ o)
  ηₒ-pos {O} _ = tt
  ηₒ-pos {S n} (o , ρ) = inl tt

  -- ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (ηₒ o)) → Set)
  --   → (ηₒ-pos* : X (ηₒ-pos o))
  --   → (p : Pos (ηₒ o)) → X p
  ηₒ-pos-elim {n = O} o X ηₒ-pos* tt = ηₒ-pos*
  ηₒ-pos-elim {n = S n} o X ηₒ-pos* (inl tt) = ηₒ-pos*

  -- μₒ : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
  --   → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
  --   → 𝒫 o
  μₒ {O} {_} _ _ = tt
  μₒ {S n} (lfₒ o) κ = lfₒ o
  μₒ {S n} (ndₒ o ρ δ ε) κ = 
    let w = κ (inl tt)
        ε' p = μₒ (ε p) (λ q → κ (inr (p , q)))
    in γₒ w δ ε'

  -- μₒ-pos : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
  --   → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
  --   → (p : Pos ρ) (q : Pos (κ p))
  --   → Pos (μₒ ρ κ)
  μₒ-pos {O} _ _ _ _ = tt
  μₒ-pos {S n} (ndₒ o ρ δ ε) κ (inl tt) r = 
    let w = κ (inl tt)
        ε' p = μₒ (ε p) (λ q → κ (inr (p , q)))
    in γₒ-pos-inl w δ ε' r
  μₒ-pos {S n} (ndₒ o ρ δ ε) κ (inr (p , q)) r = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μₒ (ε p) (κ' p)
    in γₒ-pos-inr w δ ε' p (μₒ-pos (ε p) (κ' p) q r) 

  -- μₒ-pos-fst : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
  --   → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
  --   → Pos (μₒ ρ κ) → Pos ρ
  μₒ-pos-fst {O} _ _ _ = tt
  μₒ-pos-fst {S n} (ndₒ o ρ δ ε) κ = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μₒ (ε p) (κ' p)
    in γₒ-pos-elim w δ ε' _ (λ _ → inl tt)
        (λ p q → inr (p , μₒ-pos-fst (ε p) (κ' p) q))

  -- μₒ-pos-snd : {n : ℕ} {o : 𝒪 n} (ρ : 𝒫 o)
  --   → (κ : (p : Pos ρ) → 𝒫 (Typ ρ p))
  --   → (p : Pos (μₒ ρ κ)) → Pos (κ (μₒ-pos-fst ρ κ p))
  μₒ-pos-snd {O} _ _ _ = tt
  μₒ-pos-snd {S n} (ndₒ o ρ δ ε) κ = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μₒ (ε p) (κ' p)
    in γₒ-pos-elim w δ ε' _ (λ p → p)
         (λ p q → μₒ-pos-snd (ε p) (κ' p) q)

  --
  --  Examples
  --

  obj : 𝒪 0
  obj = tt

  arrow : 𝒪 1
  arrow = tt , tt

  2-drop : 𝒪 2
  2-drop = (tt , tt) , lfₒ tt

  2-globe : 𝒪 2
  2-globe = (tt , tt) , ndₒ tt tt (cst tt) (cst (lfₒ tt))

  2-simplex : 𝒪 2
  2-simplex = (tt , tt) , ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))
