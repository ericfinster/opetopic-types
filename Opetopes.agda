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
    _▸_ : {n : ℕ} (o : 𝒪 n) → 𝒯r o → 𝒪 (S n)

  η : {n : ℕ} (o : 𝒪 n) → 𝒯r o

  η-pos : {n : ℕ} (o : 𝒪 n)
    → Pos (η o)

  η-pos-elim : {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (η o)) → Set)
    → (η-pos* : X (η-pos o))
    → (p : Pos (η o)) → X p

  μ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → 𝒯r o

  μ-pos : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (p : Pos τ) (q : Pos (κ p))
    → Pos (μ τ κ)

  μ-pos-fst : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → Pos (μ τ κ) → Pos τ

  μ-pos-snd : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
    → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (p : Pos (μ τ κ)) → Pos (κ (μ-pos-fst τ κ p))

  γ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → 𝒯r (o ▸ μ τ δ)

  γ-pos-inl : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → Pos υ → Pos (γ o τ υ δ ε)

  γ-pos-inr : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → (p : Pos τ) (q : Pos (ε p))
    → Pos (γ o τ υ δ ε)

  γ-pos-elim : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
    → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
    → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
    → (X : Pos (γ o τ υ δ ε) → Set)
    → (left : (p : Pos υ) → X (γ-pos-inl o τ υ δ ε p))
    → (right : (p : Pos τ) (q : Pos (ε p)) → X (γ-pos-inr o τ υ δ ε p q))
    → (p : Pos (γ o τ υ δ ε)) → X p

  data 𝒯r where
    arr : 𝒯r ●
    lf : {n : ℕ} (o : 𝒪 n) → 𝒯r (o ▸ η o)
    nd : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o)
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → 𝒯r (o ▸ μ τ δ)

  -- Pos : {n : ℕ} {o : 𝒪 n} → 𝒯r o → Set
  Pos arr = ⊤
  Pos (lf o) = ∅
  Pos (nd o τ δ ε) = ⊤ ⊔ Σ (Pos τ) (λ p → Pos (ε p))

  -- Typ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o) (p : Pos τ) → 𝒪 n
  Typ arr p = ●
  Typ (nd o τ δ ε) (inl tt) = o ▸ τ
  Typ (nd o τ δ ε) (inr (p , q)) = Typ (ε p) q

  postulate

    -- η-pos laws
    η-pos-typ : {n : ℕ} (o : 𝒪 n)
      → (p : Pos (η o))
      → Typ (η o) p ↦ o
    {-# REWRITE η-pos-typ #-}

    η-pos-elim-β : {n : ℕ} (o : 𝒪 n)
      → (X : (p : Pos (η o)) → Set)
      → (η-pos* : X (η-pos o))
      → η-pos-elim o X η-pos* (η-pos o) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    -- μ-pos laws
    μ-pos-fst-β : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos τ) (q : Pos (κ p))
      → μ-pos-fst τ κ (μ-pos τ κ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos τ) (q : Pos (κ p))
      → μ-pos-snd τ κ (μ-pos τ κ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}
    
    μ-pos-η : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos (μ τ κ))
      → μ-pos τ κ (μ-pos-fst τ κ p) (μ-pos-snd τ κ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    μ-pos-typ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (p : Pos (μ τ κ))
      → Typ (μ τ κ) p ↦ Typ (κ (μ-pos-fst τ κ p)) (μ-pos-snd τ κ p)
    {-# REWRITE μ-pos-typ #-}

    -- μ laws
    μ-unit-r : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → μ τ (λ p → η (Typ τ p)) ↦ τ
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : {n : ℕ} {o : 𝒪 n} (ϕ : (p : Pos (η o)) → 𝒯r o)
      → μ (η o) ϕ ↦ ϕ (η-pos o)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
      → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (θ : (p : Pos (μ τ κ)) → 𝒯r (Typ (μ τ κ) p))
      → μ (μ τ κ) θ ↦ μ τ (λ p → μ (κ p) (λ t → θ (μ-pos τ κ p t)))
    {-# REWRITE μ-assoc #-}

    -- γ elim rules
    γ-pos-elim-inl-β : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (X : Pos (γ o τ υ δ ε) → Set)
      → (left : (p : Pos υ) → X (γ-pos-inl o τ υ δ ε p))
      → (right : (p : Pos τ) (q : Pos (ε p)) → X (γ-pos-inr o τ υ δ ε p q))
      → (p : Pos υ)
      → γ-pos-elim o τ υ δ ε X left right (γ-pos-inl o τ υ δ ε p) ↦ left p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (X : Pos (γ o τ υ δ ε) → Set)
      → (left : (p : Pos υ) → X (γ-pos-inl o τ υ δ ε p))
      → (right : (p : Pos τ) (q : Pos (ε p)) → X (γ-pos-inr o τ υ δ ε p q))
      → (p : Pos τ) (q : Pos (ε p))
      → γ-pos-elim o τ υ δ ε X left right (γ-pos-inr o τ υ δ ε p q) ↦ right p q
    {-# REWRITE γ-pos-elim-inr-β #-}

    -- γ pos laws
    γ-pos-inl-typ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (p : Pos υ)
      → Typ (γ o τ υ δ ε) (γ-pos-inl o τ υ δ ε p) ↦ Typ υ p
    {-# REWRITE γ-pos-inl-typ #-}

    γ-pos-inr-typ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
      → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
      → (p : Pos τ) (q : Pos (ε p))
      → Typ (γ o τ υ δ ε) (γ-pos-inr o τ υ δ ε p q) ↦ Typ (ε p) q
    {-# REWRITE γ-pos-inr-typ #-}

    -- γ laws
    γ-unit-r : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (υ : 𝒯r (o ▸ τ))
      → γ o τ υ (λ p → η (Typ τ p)) (λ p → lf (Typ τ p)) ↦ υ 
    {-# REWRITE γ-unit-r #-}

  -- η : {n : ℕ} (o : 𝒪 n) → 𝒯r o
  η ● = arr
  η (o ▸ τ) = nd o τ (λ p → η (Typ τ p)) (λ p → lf (Typ τ p))

  -- η-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (η o)
  η-pos ● = tt 
  η-pos (o ▸ τ) = inl tt 
  
  -- η-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (η o)) → Set)
  --   → (η-pos* : X (η-pos o))
  --   → (p : Pos (η o)) → X p
  η-pos-elim ● X η-pos* arr-pos = η-pos*
  η-pos-elim (o ▸ τ) X η-pos* (inl tt) = η-pos*
  η-pos-elim (o ▸ τ) X η-pos* (inr (p , ()))

  -- μ : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → 𝒯r o
  μ arr κ = κ tt
  μ (lf o) κ = lf o
  μ (nd o τ δ ε) κ =
    let w = κ (inl tt)
        ε' p = μ (ε p) (λ q → κ (inr (p , q)))
    in γ o τ w δ ε'

  -- γ : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → 𝒯r (o ▸ μ τ δ)
  γ o .(η o) (lf .o) ϕ ψ = ψ (η-pos o)
  γ o .(μ τ δ) (nd .o τ δ ε) ϕ ψ =
    let ϕ' p q = ϕ (μ-pos τ δ p q)
        ψ' p q = ψ (μ-pos τ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p) 
    in nd o τ δ' ε'

  -- μ-pos : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (p : Pos τ) (q : Pos (κ p))
  --   → Pos (μ τ κ)
  μ-pos arr κ arr-pos q = q
  μ-pos (lf o) κ () q
  μ-pos (nd o τ δ ε) κ (inl tt) r =
    let w = κ (inl tt) 
        ε' p = μ (ε p) (λ q → κ (inr (p , q)))
    in γ-pos-inl o τ w δ ε' r
  μ-pos (nd o τ δ ε) κ (inr (p , q)) r = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μ (ε p) (κ' p)
    in γ-pos-inr o τ w δ ε' p (μ-pos (ε p) (κ' p) q r) 

  -- μ-pos-fst : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → Pos (μ τ κ) → Pos τ
  μ-pos-fst arr κ _ = tt
  μ-pos-fst (lf o) κ ()
  μ-pos-fst (nd o τ δ ε) κ =
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μ (ε p) (κ' p)
    in γ-pos-elim o τ w δ ε' _ (λ _ → inl tt)
        (λ p q → inr (p , μ-pos-fst (ε p) (κ' p) q))
    
  -- μ-pos-snd : {n : ℕ} {o : 𝒪 n} (τ : 𝒯r o)
  --   → (κ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (p : Pos (μ τ κ)) → Pos (κ (μ-pos-fst τ κ p))
  μ-pos-snd arr κ p = p
  μ-pos-snd (lf o) κ ()
  μ-pos-snd (nd o τ δ ε) κ = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μ (ε p) (κ' p)
    in γ-pos-elim o τ w δ ε' _ (λ p → p)
         (λ p q → μ-pos-snd (ε p) (κ' p) q)

  -- γ-pos-inl : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → Pos p → Pos (γ o τ p δ ε)
  γ-pos-inl o .(η o) (lf .o) ϕ ψ ()
  γ-pos-inl o .(μ τ δ) (nd .o τ δ ε) ϕ ψ (inl tt) = inl tt
  γ-pos-inl o .(μ τ δ) (nd .o τ δ ε) ϕ ψ (inr (u , v)) = 
    let ϕ' p q = ϕ (μ-pos τ δ p q)
        ψ' p q = ψ (μ-pos τ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in inr (u , γ-pos-inl (Typ τ u) (δ u) (ε u) (ϕ' u) (ψ' u) v) 

  -- γ-pos-inr : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → (p : Pos τ) (q : Pos (ε p))
  --   → Pos (γ o τ p δ ε)
  γ-pos-inr o .(η o) (lf .o) ϕ ψ =
    η-pos-elim o (λ p → Pos (ψ p) → Pos (ψ (η-pos o))) (λ p → p) 
  γ-pos-inr o .(μ τ δ) (nd .o τ δ ε) ϕ ψ u v = 
    let ϕ' p q = ϕ (μ-pos τ δ p q)
        ψ' p q = ψ (μ-pos τ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p)
        u₀ = μ-pos-fst τ δ u
        u₁ = μ-pos-snd τ δ u
    in inr (u₀ , γ-pos-inr (Typ τ u₀) (δ u₀) (ε u₀) (ϕ' u₀) (ψ' u₀) u₁ v) 

  -- γ-pos-elim : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o) (p : 𝒯r (o ▸ τ))
  --   → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  --   → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  --   → (X : Pos (γ o τ p δ ε) → pet)
  --   → (left : (p : Pos p) → X (γ-pos-inl o τ p δ ε p))
  --   → (right : (p : Pos τ) (q : Pos (ε p)) → X (γ-pos-inr o τ p δ ε p t))
  --   → (p : Pos (γ o τ p δ ε)) → X p
  γ-pos-elim o .(η o) (lf .o) ϕ ψ X inl* inr* q = inr* (η-pos o) q
  γ-pos-elim o .(μ τ δ) (nd .o τ δ ε) ϕ ψ X inl* inr* (inl tt) =
    inl* (inl tt)
  γ-pos-elim o .(μ τ δ) (nd .o τ δ ε) ϕ ψ X inl* inr* (inr (u , v)) =
    let ϕ' p q = ϕ (μ-pos τ δ p q)
        ψ' p q = ψ (μ-pos τ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ τ p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in γ-pos-elim (Typ τ u) (δ u) (ε u) (ϕ' u) (ψ' u)
         (λ q → X (inr (u , q)))
         (λ q → inl* (inr (u , q)))
         (λ p q → inr* (μ-pos τ δ u p) q) v

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
