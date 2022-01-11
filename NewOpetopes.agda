{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module NewOpetopes where

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

  ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (ηₒ o)) → Set)
    → (ηₒ-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

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

    ηₒ-pos-elim-β : {n : ℕ} (o : 𝒪 n)
      → (X : (p : Pos (ηₒ o)) → Set)
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


  --
  --  Trees and Grafting 
  --

  data 𝒯r {n : ℕ} : (o : 𝒪 n) (ρ : 𝒫 o) → Set where

    lf : (o : 𝒪 n) → 𝒯r o (ηₒ o)
    
    nd : (o : 𝒪 n) (ρ : 𝒫 o) 
      → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
      → 𝒯r o (μₒ ρ δ)

  𝒯rPos : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} → 𝒯r o ρ → Set 
  𝒯rPos (lf o) = ∅
  𝒯rPos (nd o ρ δ ε) =
    ⊤ ⊔ (Σ (Pos ρ) (λ p → 𝒯rPos (ε p)))

  𝒯rTyp : {n : ℕ} {o : 𝒪 n} {ρ : 𝒫 o} (σ : 𝒯r o ρ) (p : 𝒯rPos σ) → Σ (𝒪 n) 𝒫
  𝒯rTyp (lf _) ()
  𝒯rTyp (nd o ρ δ ε) (inl tt) = o , ρ
  𝒯rTyp (nd o ρ δ ε) (inr (p , q)) = 𝒯rTyp (ε p) q

  γₒ : {n : ℕ} (o : 𝒪 n) (τ : 𝒫 o) (υ : 𝒯r o τ)
    → (δ : (p : Pos τ) → 𝒫 (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p) (δ p))
    → 𝒯r o (μₒ τ δ)

  γₒ-pos-inl : {n : ℕ} (o : 𝒪 n) (τ : 𝒫 o) (υ : 𝒯r o τ)
    → (δ : (p : Pos τ) → 𝒫 (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p) (δ p))
    → 𝒯rPos υ → 𝒯rPos (γₒ o τ υ δ ε)

  γₒ-pos-inr : {n : ℕ} (o : 𝒪 n) (τ : 𝒫 o) (υ : 𝒯r o τ)
    → (δ : (p : Pos τ) → 𝒫 (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p) (δ p))
    → (p : Pos τ) (q : 𝒯rPos (ε p))
    → 𝒯rPos (γₒ o τ υ δ ε)

  γₒ-pos-elim : {n : ℕ} (o : 𝒪 n) (τ : 𝒫 o) (υ : 𝒯r o τ)
    → (δ : (p : Pos τ) → 𝒫 (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p) (δ p))
    → (X : 𝒯rPos (γₒ o τ υ δ ε) → Set)
    → (left : (p : 𝒯rPos υ) → X (γₒ-pos-inl o τ υ δ ε p))
    → (right : (p : Pos τ) (q : 𝒯rPos (ε p)) → X (γₒ-pos-inr o τ υ δ ε p q))
    → (p : 𝒯rPos (γₒ o τ υ δ ε)) → X p

  --
  --  Grafting Laws
  --
  
    -- -- γₒ elim rules
    -- γₒ-pos-elim-inl-β : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    --   → (X : Pos (γₒ o τ υ δ ε) → Set)
    --   → (left : (p : Pos υ) → X (γₒ-pos-inl o τ υ δ ε p))
    --   → (right : (p : Pos τ) (q : Pos (ε p)) → X (γₒ-pos-inr o τ υ δ ε p q))
    --   → (p : Pos υ)
    --   → γₒ-pos-elim o τ υ δ ε X left right (γₒ-pos-inl o τ υ δ ε p) ↦ left p
    -- {-# REWRITE γₒ-pos-elim-inl-β #-}

    -- γₒ-pos-elim-inr-β : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    --   → (X : Pos (γₒ o τ υ δ ε) → Set)
    --   → (left : (p : Pos υ) → X (γₒ-pos-inl o τ υ δ ε p))
    --   → (right : (p : Pos τ) (q : Pos (ε p)) → X (γₒ-pos-inr o τ υ δ ε p q))
    --   → (p : Pos τ) (q : Pos (ε p))
    --   → γₒ-pos-elim o τ υ δ ε X left right (γₒ-pos-inr o τ υ δ ε p q) ↦ right p q
    -- {-# REWRITE γₒ-pos-elim-inr-β #-}

    -- -- γₒ pos laws
    -- γₒ-pos-inl-typ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    --   → (p : Pos υ)
    --   → Typ (γₒ o τ υ δ ε) (γₒ-pos-inl o τ υ δ ε p) ↦ Typ υ p
    -- {-# REWRITE γₒ-pos-inl-typ #-}

    -- γₒ-pos-inr-typ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    --   → (p : Pos τ) (q : Pos (ε p))
    --   → Typ (γₒ o τ υ δ ε) (γₒ-pos-inr o τ υ δ ε p q) ↦ Typ (ε p) q
    -- {-# REWRITE γₒ-pos-inr-typ #-}

    -- -- γₒ laws
    -- γₒ-unit-r : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    --   → γₒ o τ υ (λ p → ηₒ (Typ τ p)) (λ p → lf (Typ τ p)) ↦ υ 
    -- {-# REWRITE γₒ-unit-r #-}

  --
  --  Opetopes 
  --

  infixl 40 _▸_

  𝒪 O = ⊤
  𝒪 (S n) = Σ (𝒪 n) 𝒫

  𝒫 {O} tt = ⊤
  𝒫 {S n} (o , p) = 𝒯r o p

  Pos {O} ρ = ⊤
  Pos {S n} ρ = 𝒯rPos ρ
  
  Typ {O} ρ p = tt
  Typ {S n} ρ p = 𝒯rTyp ρ p

  ηₒ = {!!} 
  ηₒ-pos = {!!} 
  ηₒ-pos-elim = {!!}

  μₒ = {!!} 
  μₒ-pos = {!!} 
  μₒ-pos-fst = {!!} 
  μₒ-pos-snd = {!!} 

  γₒ = {!!} 
  γₒ-pos-inl = {!!} 
  γₒ-pos-inr = {!!} 
  γₒ-pos-elim = {!!} 

