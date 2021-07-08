{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module OrdinaryOpetopes where

  data 𝕆 : ℕ → Set
  data 𝕋 : {n : ℕ} → 𝕆 n → Set
  
  Pos : {n : ℕ} {o : 𝕆 n} → 𝕋 o → Set
  Typₒ : {n : ℕ} {o : 𝕆 n}
    → (t : 𝕋 o) (p : Pos t)
    → 𝕆 n 

  infixl 40 _∣_
  
  data 𝕆 where
    ○ : 𝕆 O
    _∣_ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) → 𝕆 (S n)

  ηₒ : {n : ℕ} (o : 𝕆 n) → 𝕋 o

  ηₒ-pos : {n : ℕ} (o : 𝕆 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : {n : ℕ} (o : 𝕆 n)
    → (X : (p : Pos (ηₒ o)) → Set)
    → (η-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

  μₒ : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
    → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
    → 𝕋 o

  μₒ-pos : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Pos o) → 𝕋 (Typₒ o p))
    → (p : Pos o) (t : Pos (κ p))
    → Pos (μₒ o κ)

  μₒ-pos-fst : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Pos o) → 𝕋 (Typₒ o p))
    → Pos (μₒ o κ) → Pos o

  μₒ-pos-snd : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Pos o) → 𝕋 (Typₒ o p))
    → (p : Pos (μₒ o κ)) → Pos (κ (μₒ-pos-fst o κ p))

  γₒ : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → 𝕋 (o ∣ μₒ s δ)

  γₒ-pos-inl : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → Pos t → Pos (γₒ o s t δ ε)

  γₒ-pos-inr : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → (p : Pos s) (q : Pos (ε p))
    → Pos (γₒ o s t δ ε)

  γₒ-pos-elim : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → (X : Pos (γₒ o s t δ ε) → Set)
    → (inl* : (p : Pos t) → X (γₒ-pos-inl o s t δ ε p))
    → (inr* : (p : Pos s) (q : Pos (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
    → (p : Pos (γₒ o s t δ ε)) → X p

  data 𝕋 where
    arr : 𝕋 ○
    lfₒ : {n : ℕ} (o : 𝕆 n) → 𝕋 (o ∣ ηₒ o)
    ndₒ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o)
      → (δ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (ε : (p : Pos t) → 𝕋 (Typₒ t p ∣ δ p))
      → 𝕋 (o ∣ μₒ t δ)

  Pos arr = ⊤
  Pos (lfₒ o) = ∅
  Pos (ndₒ o t δ ε) = ⊤ ⊔ Σ (Pos t) (λ p → Pos (ε p))
  
  Typₒ arr unit = ○
  Typₒ (ndₒ o t δ ε) (inl unit) = o ∣ t
  Typₒ (ndₒ o t δ ε) (inr (p , q)) = Typₒ (ε p) q

  postulate

    -- ηₒ-pos laws
    ηₒ-pos-typ : {n : ℕ} (o : 𝕆 n)
      → (p : Pos (ηₒ o))
      → Typₒ (ηₒ o) p ↦ o
    {-# REWRITE ηₒ-pos-typ #-}

    ηₒ-pos-elim-β : {n : ℕ} (o : 𝕆 n)
      → (X : (p : Pos (ηₒ o)) → Set)
      → (ηₒ-pos* : X (ηₒ-pos o))
      → ηₒ-pos-elim o X ηₒ-pos* (ηₒ-pos o) ↦ ηₒ-pos*
    {-# REWRITE ηₒ-pos-elim-β #-}

    -- μₒ-pos laws
    μₒ-pos-typ : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos (μₒ t κ))
      → Typₒ (μₒ t κ) p ↦ Typₒ (κ (μₒ-pos-fst t κ p)) (μₒ-pos-snd t κ p)
    {-# REWRITE μₒ-pos-typ #-}
  
    μₒ-pos-fst-β : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos t) (q : Pos (κ p))
      → μₒ-pos-fst t κ (μₒ-pos t κ p q) ↦ p
    {-# REWRITE μₒ-pos-fst-β #-}

    μₒ-pos-snd-β : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos t) (q : Pos (κ p))
      → μₒ-pos-snd t κ (μₒ-pos t κ p q) ↦ q
    {-# REWRITE μₒ-pos-snd-β #-}
    
    μₒ-pos-η : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos (μₒ t κ))
      → μₒ-pos t κ (μₒ-pos-fst t κ p) (μₒ-pos-snd t κ p) ↦ p
    {-# REWRITE μₒ-pos-η #-}

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → μₒ t (λ p → ηₒ (Typₒ t p)) ↦ t
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {o : 𝕆 n} (ϕ : (p : Pos (ηₒ o)) → 𝕋 o)
      → μₒ (ηₒ o) ϕ ↦ ϕ (ηₒ-pos o)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (θ : (p : Pos (μₒ t κ)) → 𝕋 (Typₒ (μₒ t κ) p))
      → μₒ (μₒ t κ) θ ↦ μₒ t (λ p → μₒ (κ p) (λ q → θ (μₒ-pos t κ p q)))
    {-# REWRITE μₒ-assoc #-}

    -- γₒ elim rules
    γₒ-pos-elim-inl-β : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
      → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
      → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
      → (X : Pos (γₒ o s t δ ε) → Set)
      → (inl* : (p : Pos t) → X (γₒ-pos-inl o s t δ ε p))
      → (inr* : (p : Pos s) (q : Pos (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
      → (p : Pos t)
      → γₒ-pos-elim o s t δ ε X inl* inr* (γₒ-pos-inl o s t δ ε p) ↦ inl* p
    {-# REWRITE γₒ-pos-elim-inl-β #-}

    γₒ-pos-elim-inr-β : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
      → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
      → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
      → (X : Pos (γₒ o s t δ ε) → Set)
      → (inl* : (p : Pos t) → X (γₒ-pos-inl o s t δ ε p))
      → (inr* : (p : Pos s) (q : Pos (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
      → (p : Pos s) (q : Pos (ε p))
      → γₒ-pos-elim o s t δ ε X inl* inr* (γₒ-pos-inr o s t δ ε p q) ↦ inr* p q
    {-# REWRITE γₒ-pos-elim-inr-β #-}

  --   -- γₒ pos laws
  --   γₒ-pos-inl-typ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) (t : 𝕋 (f ∣ o))
  --     → (δ : (p : Pos o) → 𝕋 (Typₒ o s))
  --     → (ε : (p : Pos o) → 𝕋 (Typₒ o s ∣ δ s))
  --     → (p : Pos p)
  --     → Typₒ (γₒ f o p δ ε) (γₒ-pos-inl f o p δ ε s) ↦ Typₒ p s
  --   {-# REWRITE γₒ-pos-inl-typ #-}

  --   γₒ-pos-inr-typ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) (t : 𝕋 (f ∣ o))
  --     → (δ : (p : Pos o) → 𝕋 (Typₒ o s))
  --     → (ε : (p : Pos o) → 𝕋 (Typₒ o s ∣ δ s))
  --     → (p : Pos o) (t : Pos (ε s))
  --     → Typₒ (γₒ f o p δ ε) (γₒ-pos-inr f o p δ ε s t) ↦ Typₒ (ε s) t
  --   {-# REWRITE γₒ-pos-inr-typ #-}

  --   -- γₒ laws
  --   γₒ-unit-r : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) (t : 𝕋 (f ∣ o))
  --     → γₒ f o p (λ s → η (Typₒ o s)) (λ s → lfₒ (Typₒ o s)) ↦ p 
  --   {-# REWRITE γₒ-unit-r #-}

  ηₒ ○ = arr
  ηₒ (o ∣ t) =
    let η-dec p = ηₒ (Typₒ t p)
        lfₒ-dec p = lfₒ (Typₒ t p)
    in ndₒ o t η-dec lfₒ-dec
  
  ηₒ-pos ○ = tt
  ηₒ-pos (o ∣ t) = inl tt
  
  ηₒ-pos-elim ○ X η-pos* unit = η-pos*
  ηₒ-pos-elim (o ∣ t) X η-pos* (inl unit) = η-pos*

  μₒ arr κ = κ tt
  μₒ (lfₒ o) κ = lfₒ o
  μₒ (ndₒ o t δ ε) κ = 
    let w = κ (inl tt)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ o t w δ ϕ

  μₒ-pos arr κ unit q = q
  μₒ-pos (ndₒ o t δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ-pos-inl o t w δ ϕ r 
  μₒ-pos (ndₒ o t δ ε) κ (inr (p , q)) r = 
    let w = κ (inl tt)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ-pos-inr o t w δ ϕ p (μₒ-pos (ε p) (κ↑ p) q r)

  μₒ-pos-fst arr κ p = tt
  μₒ-pos-fst (ndₒ o t δ ε) κ p =
    let w = κ (inl tt)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Pos t) (λ q → Pos (ε q))
        inl* p = inl tt
        inr* p q = inr (p , (μₒ-pos-fst (ε p) (κ↑ p) q))
    in γₒ-pos-elim o t w δ ϕ X inl* inr* p
    
  μₒ-pos-snd arr κ p = p
  μₒ-pos-snd (ndₒ o t δ ε) κ p = 
    let w = κ (inl tt)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
        X p = Pos (κ (μₒ-pos-fst (ndₒ o t δ ε) κ p))
        inl* p = p
        inr* p q = μₒ-pos-snd (ε p) (κ↑ p) q
    in γₒ-pos-elim o t w δ ϕ X inl* inr* p

  γₒ o .(ηₒ o) (lfₒ .o) ϕ ψ = ψ (ηₒ-pos o)
  γₒ o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ =
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in ndₒ o t δ↑ ε↑ 

  γₒ-pos-inl o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ (inl unit) = inl unit
  γₒ-pos-inl o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γₒ-pos-inl (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p) q)

  γₒ-pos-inr o .(ηₒ o) (lfₒ .o) ϕ ψ p q =
    ηₒ-pos-elim o (λ p → Pos (ψ p) → Pos (ψ (ηₒ-pos o))) (λ p → p) p q
  γₒ-pos-inr o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μₒ-pos-fst t δ p
        p₁ = μₒ-pos-snd t δ p
    in inr (p₀ , γₒ-pos-inr (Typₒ t p₀) (δ p₀) (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q)

  γₒ-pos-elim o .(ηₒ o) (lfₒ .o) ϕ ψ X inl* inr* p = inr* (ηₒ-pos o) p
  γₒ-pos-elim o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γₒ-pos-elim o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
        X q = X (inr (p , q))
        inl* q = inl* (inr (p , q))
        inr* q r = inr* (μₒ-pos t δ p q) r
    in γₒ-pos-elim (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p) X inl* inr* q

  --
  --  Examples
  --

  obj : 𝕆 0
  obj = ○

  arrow : 𝕆 1
  arrow = ○ ∣ arr

  2-drop : 𝕆 2
  2-drop = ○ ∣ arr ∣ lfₒ ○

  2-globe : 𝕆 2
  2-globe = ○ ∣ arr ∣ ndₒ ○ arr (λ { unit → arr }) (λ { unit → lfₒ ○ })

  2-simplex : 𝕆 2
  2-simplex = ○ ∣ arr ∣ ndₒ ○ arr (λ { unit → arr }) (λ { unit → ndₒ ○ arr (λ { unit → arr }) (λ { unit → lfₒ ○ }) })

  -- --
  -- -- Opetopic Sum
  -- --

  -- infixl 70 _⊕_ _⊕t_ _⊝p_
  
  -- _⊕_ : {m n : ℕ} → 𝕆 m → 𝕆 n → 𝕆 (S (m + n))

  -- _⊕t_ : {m n : ℕ}
  --   → (o : 𝕆 m) {p : 𝕆 n}
  --   → 𝕋 p → 𝕋 (o ⊕ p)

  -- _⊝p_ : {m n : ℕ}
  --   → (o : 𝕆 m) {p : 𝕆 n} {t : 𝕋 p}
  --   → Pos (o ⊕t t) → Pos t
    
  -- postulate

  --   ⊕-η : {m n : ℕ}
  --     → (o : 𝕆 m) {p : 𝕆 n}
  --     → o ⊕t ηₒ p ↦ ηₒ (o ⊕ p)
  --   {-# REWRITE ⊕-η #-}

  --   ⊕-typ : {m n : ℕ}
  --     → (o : 𝕆 m) {p : 𝕆 n}
  --     → {t : 𝕋 p} (q : Pos (o ⊕t t))
  --     → Typₒ (o ⊕t t) q ↦ o ⊕ Typₒ t (o ⊝p q)
  --   {-# REWRITE ⊕-typ #-}
    
  --   ⊕-μ : {m n : ℕ}
  --     → (o : 𝕆 m) {p : 𝕆 n}
  --     → (t : 𝕋 p) (δ : (q : Pos t) → 𝕋 (Typₒ t q))
  --     → o ⊕t μₒ t δ ↦ μₒ (o ⊕t t) (λ q → o ⊕t (δ (o ⊝p q)))
  --   {-# REWRITE ⊕-μ #-}

  -- o ⊕ ○ = o ∣ ηₒ o
  -- o ⊕ (p ∣ t) = o ⊕ p ∣ o ⊕t t

  -- o ⊕t nilₒ = lfₒ o
  -- o ⊕t cnsₒ t = ndₒ o (ηₒ o) (λ _ → ηₒ o) (λ _ → o ⊕t t)
  -- o ⊕t lfₒ p = lfₒ (o ⊕ p)
  -- o ⊕t ndₒ p t δ ε = ndₒ (o ⊕ p) (o ⊕t t)
  --   (λ p → o ⊕t (δ (o ⊝p p)))
  --   (λ p → o ⊕t (ε (o ⊝p p)))

  -- _⊝p_ o {t = cnsₒ t} (inl unit) = inl unit
  -- _⊝p_ o {t = cnsₒ t} (inr (_ , p)) = inr (o ⊝p p)
  -- _⊝p_ o {t = ndₒ p t δ ε} (inl unit) = inl unit
  -- _⊝p_ o {t = ndₒ p t δ ε} (inr (q , r)) = inr (o ⊝p q , o ⊝p r)

