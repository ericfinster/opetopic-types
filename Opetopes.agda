{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module Opetopes where

  data 𝒪 : ℕ → Set
  data 𝒯r : {n : ℕ} (o : 𝒪 n) → Set
  Pos : {n : ℕ} {o : 𝒪 n} → 𝒯r o → Set 
  Typ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o) (p : Pos τ) → 𝒪 n

  infixl 40 _▸_
  
  data 𝒪 where
    ● : 𝒪 O
    _▸_ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) → 𝒪 (S n)

  ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒯r o

  ηₒ-pos : {n : ℕ} (o : 𝒪 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (ηₒ o)) → Set)
    → (ηₒ-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

  μₒ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → 𝒯r o

  μₒ-pos : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (p : Pos τ) (q : Pos (κ p))
    → Pos (μₒ τ κ)

  μₒ-pos-fst : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → Pos (μₒ τ κ) → Pos τ

  μₒ-pos-snd : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (p : Pos (μₒ τ κ)) → Pos (κ (μₒ-pos-fst τ κ p))

  γₒ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → 𝒯r (o ▸ μₒ τ δ)

  γₒ-pos-inl : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → Pos υ → Pos (γₒ o τ υ δ ε)

  γₒ-pos-inr : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → (p : Pos τ) (q : Pos (ε p))
    → Pos (γₒ o τ υ δ ε)

  γₒ-pos-elim : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → (X : Pos (γₒ o τ υ δ ε) → Set)
    → (left : (p : Pos υ) → X (γₒ-pos-inl o τ υ δ ε p))
    → (right : (p : Pos τ) (q : Pos (ε p)) → X (γₒ-pos-inr o τ υ δ ε p q))
    → (p : Pos (γₒ o τ υ δ ε)) → X p

  data 𝒯r where
    arr : 𝒯r ●
    lf : {n : ℕ} (o : 𝒪 n) → 𝒯r (o ▸ ηₒ o)
    nd : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o)
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → 𝒯r (o ▸ μₒ τ δ)

  -- Pos : {n : ℕ} {o : 𝒪 n} → 𝒯r o → Set
  Pos arr = ⊤
  Pos (lf o) = ∅
  Pos (nd o τ δ ε) = ⊤ ⊔ Σ (Pos τ) (λ p → Pos (ε p))

  -- Typ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o) (p : Pos τ) → 𝒪 n
  Typ arr p = ●
  Typ (nd o τ δ ε) (inl tt) = o ▸ τ
  Typ (nd o τ δ ε) (inr (p , q)) = Typ (ε p) q

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
    μₒ-pos-fst-β : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos τ) (q : Pos (κ p))
      → μₒ-pos-fst τ κ (μₒ-pos τ κ p q) ↦ p
    {-# REWRITE μₒ-pos-fst-β #-}

    μₒ-pos-snd-β : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos τ) (q : Pos (κ p))
      → μₒ-pos-snd τ κ (μₒ-pos τ κ p q) ↦ q
    {-# REWRITE μₒ-pos-snd-β #-}
    
    μₒ-pos-ηₒ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos (μₒ τ κ))
      → μₒ-pos τ κ (μₒ-pos-fst τ κ p) (μₒ-pos-snd τ κ p) ↦ p
    {-# REWRITE μₒ-pos-ηₒ #-}

    μₒ-pos-typ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos (μₒ τ κ))
      → Typ (μₒ τ κ) p ↦ Typ (κ (μₒ-pos-fst τ κ p)) (μₒ-pos-snd τ κ p)
    {-# REWRITE μₒ-pos-typ #-}

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → μₒ τ (λ p → ηₒ (Typ τ p)) ↦ τ
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {o : 𝒪 n} (ϕ : (p : Pos (ηₒ o)) → 𝒯r o)
      → μₒ (ηₒ o) ϕ ↦ ϕ (ηₒ-pos o)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (θ : (p : Pos (μₒ τ κ)) → 𝒯r (Typ (μₒ τ κ) p))
      → μₒ (μₒ τ κ) θ ↦ μₒ τ (λ p → μₒ (κ p) (λ t → θ (μₒ-pos τ κ p t)))
    {-# REWRITE μₒ-assoc #-}

    -- γₒ elim rules
    γₒ-pos-elim-inl-β : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (X : Pos (γₒ o τ υ δ ε) → Set)
      → (left : (p : Pos υ) → X (γₒ-pos-inl o τ υ δ ε p))
      → (right : (p : Pos τ) (q : Pos (ε p)) → X (γₒ-pos-inr o τ υ δ ε p q))
      → (p : Pos υ)
      → γₒ-pos-elim o τ υ δ ε X left right (γₒ-pos-inl o τ υ δ ε p) ↦ left p
    {-# REWRITE γₒ-pos-elim-inl-β #-}

    γₒ-pos-elim-inr-β : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (X : Pos (γₒ o τ υ δ ε) → Set)
      → (left : (p : Pos υ) → X (γₒ-pos-inl o τ υ δ ε p))
      → (right : (p : Pos τ) (q : Pos (ε p)) → X (γₒ-pos-inr o τ υ δ ε p q))
      → (p : Pos τ) (q : Pos (ε p))
      → γₒ-pos-elim o τ υ δ ε X left right (γₒ-pos-inr o τ υ δ ε p q) ↦ right p q
    {-# REWRITE γₒ-pos-elim-inr-β #-}

    -- γₒ pos laws
    γₒ-pos-inl-typ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (p : Pos υ)
      → Typ (γₒ o τ υ δ ε) (γₒ-pos-inl o τ υ δ ε p) ↦ Typ υ p
    {-# REWRITE γₒ-pos-inl-typ #-}

    γₒ-pos-inr-typ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (p : Pos τ) (q : Pos (ε p))
      → Typ (γₒ o τ υ δ ε) (γₒ-pos-inr o τ υ δ ε p q) ↦ Typ (ε p) q
    {-# REWRITE γₒ-pos-inr-typ #-}

    -- γₒ laws
    γₒ-unit-r : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → γₒ o τ υ (λ p → ηₒ (Typ τ p)) (λ p → lf (Typ τ p)) ↦ υ 
    {-# REWRITE γₒ-unit-r #-}

  -- ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒯r o
  ηₒ ● = arr
  ηₒ (o ▸ τ) = nd o τ (λ p → ηₒ (Typ τ p)) (λ p → lf (Typ τ p))

  -- ηₒ-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (ηₒ o)
  ηₒ-pos ● = tt 
  ηₒ-pos (o ▸ τ) = inl tt 
  
  -- ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (ηₒ o)) → Set)
  --   → (ηₒ-pos* : X (ηₒ-pos o))
  --   → (p : Pos (ηₒ o)) → X p
  ηₒ-pos-elim ● X ηₒ-pos* arr-pos = ηₒ-pos*
  ηₒ-pos-elim (o ▸ τ) X ηₒ-pos* (inl tt) = ηₒ-pos*
  ηₒ-pos-elim (o ▸ τ) X ηₒ-pos* (inr (p , ()))

  -- μₒ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → 𝒯r o
  μₒ arr κ = κ tt
  μₒ (lf o) κ = lf o
  μₒ (nd o τ δ ε) κ =
    let w = κ (inl tt)
        ε' p = μₒ (ε p) (λ q → κ (inr (p , q)))
    in γₒ o τ w δ ε'

  -- γₒ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → 𝒯r (o ▸ μₒ τ δ)
  γₒ o .(ηₒ o) (lf .o) ϕ ψ = ψ (ηₒ-pos o)
  γₒ o .(μₒ τ δ) (nd .o τ δ ε) ϕ ψ =
    let ϕ' p q = ϕ (μₒ-pos τ δ p q)
        ψ' p q = ψ (μₒ-pos τ δ p q)
        δ' p = μₒ (δ p) (ϕ' p)
        ε' p = γₒ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p) 
    in nd o τ δ' ε'

  -- μₒ-pos : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (p : Pos τ) (q : Pos (κ p))
  --   → Pos (μₒ τ κ)
  μₒ-pos arr κ arr-pos q = q
  μₒ-pos (lf o) κ () q
  μₒ-pos (nd o τ δ ε) κ (inl tt) r =
    let w = κ (inl tt) 
        ε' p = μₒ (ε p) (λ q → κ (inr (p , q)))
    in γₒ-pos-inl o τ w δ ε' r
  μₒ-pos (nd o τ δ ε) κ (inr (p , q)) r = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μₒ (ε p) (κ' p)
    in γₒ-pos-inr o τ w δ ε' p (μₒ-pos (ε p) (κ' p) q r) 

  -- μₒ-pos-fst : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → Pos (μₒ τ κ) → Pos τ
  μₒ-pos-fst arr κ _ = tt
  μₒ-pos-fst (lf o) κ ()
  μₒ-pos-fst (nd o τ δ ε) κ =
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μₒ (ε p) (κ' p)
    in γₒ-pos-elim o τ w δ ε' _ (λ _ → inl tt)
        (λ p q → inr (p , μₒ-pos-fst (ε p) (κ' p) q))
    
  -- μₒ-pos-snd : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (p : Pos (μₒ τ κ)) → Pos (κ (μₒ-pos-fst τ κ p))
  μₒ-pos-snd arr κ p = p
  μₒ-pos-snd (lf o) κ ()
  μₒ-pos-snd (nd o τ δ ε) κ = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μₒ (ε p) (κ' p)
    in γₒ-pos-elim o τ w δ ε' _ (λ p → p)
         (λ p q → μₒ-pos-snd (ε p) (κ' p) q)

  -- γₒ-pos-inl : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → Pos p → Pos (γₒ o τ p δ ε)
  γₒ-pos-inl o .(ηₒ o) (lf .o) ϕ ψ ()
  γₒ-pos-inl o .(μₒ τ δ) (nd .o τ δ ε) ϕ ψ (inl tt) = inl tt
  γₒ-pos-inl o .(μₒ τ δ) (nd .o τ δ ε) ϕ ψ (inr (u , v)) = 
    let ϕ' p q = ϕ (μₒ-pos τ δ p q)
        ψ' p q = ψ (μₒ-pos τ δ p q)
        δ' p = μₒ (δ p) (ϕ' p)
        ε' p = γₒ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in inr (u , γₒ-pos-inl (Typ τ u) (δ u) (ε u) (ϕ' u) (ψ' u) v) 

  -- γₒ-pos-inr : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → (p : Pos τ) (q : Pos (ε p))
  --   → Pos (γₒ o τ p δ ε)
  γₒ-pos-inr o .(ηₒ o) (lf .o) ϕ ψ =
    ηₒ-pos-elim o (λ p → Pos (ψ p) → Pos (ψ (ηₒ-pos o))) (λ p → p) 
  γₒ-pos-inr o .(μₒ τ δ) (nd .o τ δ ε) ϕ ψ u v = 
    let ϕ' p q = ϕ (μₒ-pos τ δ p q)
        ψ' p q = ψ (μₒ-pos τ δ p q)
        δ' p = μₒ (δ p) (ϕ' p)
        ε' p = γₒ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p)
        u₀ = μₒ-pos-fst τ δ u
        u₁ = μₒ-pos-snd τ δ u
    in inr (u₀ , γₒ-pos-inr (Typ τ u₀) (δ u₀) (ε u₀) (ϕ' u₀) (ψ' u₀) u₁ v) 

  -- γₒ-pos-elim : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → (X : Pos (γₒ o τ p δ ε) → pet)
  --   → (left : (p : Pos p) → X (γₒ-pos-inl o τ p δ ε p))
  --   → (right : (p : Pos τ) (q : Pos (ε p)) → X (γₒ-pos-inr o τ p δ ε p t))
  --   → (p : Pos (γₒ o τ p δ ε)) → X p
  γₒ-pos-elim o .(ηₒ o) (lf .o) ϕ ψ X inl* inr* q = inr* (ηₒ-pos o) q
  γₒ-pos-elim o .(μₒ τ δ) (nd .o τ δ ε) ϕ ψ X inl* inr* (inl tt) =
    inl* (inl tt)
  γₒ-pos-elim o .(μₒ τ δ) (nd .o τ δ ε) ϕ ψ X inl* inr* (inr (u , v)) =
    let ϕ' p q = ϕ (μₒ-pos τ δ p q)
        ψ' p q = ψ (μₒ-pos τ δ p q)
        δ' p = μₒ (δ p) (ϕ' p)
        ε' p = γₒ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in γₒ-pos-elim (Typ τ u) (δ u) (ε u) (ϕ' u) (ψ' u)
         (λ q → X (inr (u , q)))
         (λ q → inl* (inr (u , q)))
         (λ p q → inr* (μₒ-pos τ δ u p) q) v

  --
  --  Examples
  --

  τb : 𝒪 0
  τb = ●

  arrow : 𝒪 1
  arrow = ● ▸ arr

  2-drop : 𝒪 2
  2-drop = ● ▸ arr ▸ lf ●

  2-globe : 𝒪 2
  2-globe = ● ▸ arr ▸ nd ● arr (λ { arr-pos → arr }) (λ { arr-pos → lf ● })

  2-simplex : 𝒪 2
  2-simplex = ● ▸ arr ▸ nd ● arr (λ { arr-pos → arr }) (λ { arr-pos → nd ● arr (λ { arr-pos → arr }) (λ { arr-pos → lf ● }) })
