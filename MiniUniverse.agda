{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module MiniUniverse where

  infixr 40 _⊔ₚ_
  
  postulate

    ℙ : Set 
    El : ℙ → Set

    Decor : ∀ {ℓ} → Set ℓ → ℙ → Set ℓ
    Decor↓ : ∀ {ℓ ℓ↓} {P : ℙ} {X : Set ℓ}
      → (X↓ : X → Set ℓ↓) (δ : Decor X P)
      → Set ℓ↓

    app : ∀ {ℓ} {X : Set ℓ} {P : ℙ}
      → Decor X P → El P → X
    app↓ : ∀ {ℓ ℓ↓} {P : ℙ} {X : Set ℓ}
      → {X↓ : X → Set ℓ↓} {δ : Decor X P}
      → Decor↓ X↓ δ → (p : El P) → X↓ (app δ p)

    cst-dec : ∀ {ℓ} {X : Set ℓ}
      → (P : ℙ) → X → Decor X P

    map-dec : ∀ {ℓ ℓ'} {X : Set ℓ} {Y : Set ℓ'} {P : ℙ}
      → (f : X → Y) → Decor X P → Decor Y P 

    map2-dec : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ}
      → {Y : Set ℓ'} {Z : Set ℓ''}
      → (f : X → Y → Z)
      → {P : ℙ} → Decor X P → Decor Y P
      → Decor Z P

  fst-dec' : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
    → {P : ℙ} (δ : Decor (Σ X X↓) P)
    → Decor X P
  fst-dec' δ = map-dec fst δ 

  -- We have to be able to apply the constructions
  -- "inside" decorations ...
  Σ-in-dec : {U : ℙ} (V : Decor ℙ U)
    → (W : Decor↓ (Decor ℙ) V)
    → Decor ℙ U
  Σ-in-dec V W = {!!} 

  ⊔-in-dec : {U : ℙ} (V : Decor ℙ U)
    → (W : Decor ℙ U) → Decor ℙ U
  ⊔-in-dec V W = map2-dec {!_⊔ₚ_!} V W 

  postulate

    --
    --  Decorations with values in Σ 
    --
    
    pair-dec : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {P : ℙ} (δ : Decor X P) (δ↓ : Decor↓ X↓ δ)
      → Decor (Σ X X↓) P 

    fst-dec : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {P : ℙ} (δ : Decor (Σ X X↓) P)
      → Decor X P 

    snd-dec : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {P : ℙ} (δ : Decor (Σ X X↓) P)
      → Decor↓ X↓ (fst-dec δ) 
      
    pair-dec↓ : ∀ {ℓ ℓ↓ ℓ↓↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {X↓↓ : (x : X) → X↓ x → Set ℓ↓↓}
      → {P : ℙ} {δ : Decor X P} (δ↓ : Decor↓ X↓ δ)
      → (δ↓↓ : Decor↓ (curry X↓↓) (pair-dec δ δ↓)) 
      → Decor↓ (λ x → Σ (X↓ x) (X↓↓ x)) δ

    fst-dec↓ : ∀ {ℓ ℓ↓ ℓ↓↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {X↓↓ : (x : X) → X↓ x → Set ℓ↓↓}
      → {P : ℙ} {δ : Decor X P}
      → Decor↓ (λ x → Σ (X↓ x) (X↓↓ x)) δ
      → Decor↓ X↓ δ

    snd-dec↓ : ∀ {ℓ ℓ↓ ℓ↓↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {X↓↓ : (x : X) → X↓ x → Set ℓ↓↓}
      → {P : ℙ} {δ : Decor X P}
      → (δ↓ : Decor↓ (λ x → Σ (X↓ x) (X↓↓ x)) δ)
      → Decor↓ (curry X↓↓) (pair-dec δ (fst-dec↓ δ↓))

    --
    -- Additive unit
    --
    
    ⊥ₚ : ℙ

    ⊥-dec : ∀ {ℓ} {X : Set ℓ} → Decor X ⊥ₚ
    ⊥-dec↓ : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → Decor↓ X↓ ⊥-dec

    --
    -- Multiplicative Unit
    --
    
    ⊤ₚ : ℙ
    ttₚ : El ⊤ₚ

    ⊤-dec : ∀ {ℓ} {X : Set ℓ}
      → X → Decor X ⊤ₚ
    ⊤-dec↓ : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {x : X} (x↓ : X↓ x) → Decor↓ X↓ (⊤-dec x) 

    --
    -- Addition
    --
    
    _⊔ₚ_ : ℙ → ℙ → ℙ

    ⊔-dec : ∀ {ℓ} {X : Set ℓ}
      → {U V : ℙ} (l : Decor X U) (r : Decor X V)
      → Decor X (U ⊔ₚ V)
      
    ⊔-dec↓ : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {U V : ℙ} {l : Decor X U} {r : Decor X V}
      → (l↓ : Decor↓ X↓ l) (r↓ : Decor↓ X↓ r)
      → Decor↓ X↓ (⊔-dec l r)


    --
    --  Dependent Multiplication
    --
    
    Σₚ : (U : ℙ) (V : Decor ℙ U) → ℙ

    Σ-dec : ∀ {ℓ} {X : Set ℓ}
      → {U : ℙ} {V : Decor ℙ U}
      → Decor↓ (Decor X) V
      → Decor X (Σₚ U V) 

    Σ-dec↓ : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {U : ℙ} {V : Decor ℙ U}
      → (δ↓ : Decor↓ (λ P → Σ (Decor X P) (λ δ → Decor↓ X↓ δ)) V)
      → Decor↓ X↓ (Σ-dec (fst-dec↓ δ↓))

    --
    --  Laws for Positions
    --

    -- Additive right unit
    ⊔ₚ-unit-r : (U : ℙ)
      → U ⊔ₚ ⊥ₚ ↦ U
    {-# REWRITE ⊔ₚ-unit-r #-}

    -- Additive left unit
    ⊔ₚ-unit-l : (V : ℙ)
      → ⊥ₚ ⊔ₚ V ↦ V
    {-# REWRITE ⊔ₚ-unit-l #-}

    -- Additive associativity
    ⊔ₚ-assoc : (U V W : ℙ)
      → (U ⊔ₚ V) ⊔ₚ W ↦ U ⊔ₚ V ⊔ₚ W
    {-# REWRITE ⊔ₚ-assoc #-}

    -- Multiplicative right unit
    Σₚ-unit-r : (U : ℙ)
      → Σₚ U (cst-dec U ⊤ₚ) ↦ U
    {-# REWRITE Σₚ-unit-r #-}

    -- Multiplicative left unit
    Σₚ-unit-l : (V : Decor ℙ ⊤ₚ)
      → Σₚ ⊤ₚ V ↦ app V ttₚ
    {-# REWRITE Σₚ-unit-l #-}

    -- Multiplicative left zero
    Σₚ-zero-r : (U : ℙ)
      → Σₚ U (cst-dec U ⊥ₚ) ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-r #-}

    -- Multiplicative right zero
    Σₚ-zero-l : (V : Decor ℙ ⊥ₚ)
      → Σₚ ⊥ₚ V ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-l #-}


    -- Hmmm.  But what's not so satisfying about this is that the
    -- decoration is required to have a specific form, whereas
    -- for a rewrite rule, we would expect it to somehow be
    -- arbitrary....

    Σₚ-assoc' : (U : ℙ) (V : Decor ℙ U)
      → (W : Decor ℙ (Σₚ U V))
      → Σₚ (Σₚ U V) W ↦ Σₚ U (Σ-in-dec V {!!})

    -- Multiplicative associativity
    Σₚ-assoc : (U : ℙ) (V : Decor ℙ U)
      → (W : Decor↓ (Decor ℙ) V)
      → Σₚ (Σₚ U V) (Σ-dec W) ↦ Σₚ U (Σ-in-dec V W)

    -- Right Distributivity
    ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
      → (Wl : Decor ℙ U) (Wr : Decor ℙ V)
      → Σₚ (U ⊔ₚ V) (⊔-dec Wl Wr) ↦ Σₚ U Wl ⊔ₚ Σₚ V Wr 

    -- Left Distributivity
    ⊔ₚ-Σₚ-distrib-l : {U : ℙ}
      → (V : Decor ℙ U) (W : Decor ℙ U)
      → Σₚ U (⊔-in-dec V W) ↦ Σₚ U V ⊔ₚ Σₚ U W

  --
  --  Elements
  --

  -- postulate
  
  --   El : ℙ → Set

  --   -- ⊥
  --   ⊥ₚ-elim : ∀ {ℓ} (P : El ⊥ₚ → Set ℓ)
  --     → (b : El ⊥ₚ) → P b

  --   ttₚ : El ⊤ₚ

  --   -- ⊤ 
  --   ⊤ₚ-elim : ∀ {ℓ} (P : El ⊤ₚ → Set ℓ)
  --     → (ttₚ* : P ttₚ)
  --     → (u : El ⊤ₚ) → P u 

  --   ⊤ₚ-elim-β :  ∀ {ℓ} (P : El ⊤ₚ → Set ℓ)
  --     → (ttₚ* : P ttₚ)
  --     → ⊤ₚ-elim P ttₚ* ttₚ ↦ ttₚ*
  --   {-# REWRITE ⊤ₚ-elim-β #-}

  --   -- ⊔
  --   inlₚ : {U : ℙ} → (V : ℙ) → El U → El (U ⊔ₚ V)
  --   inrₚ : {V : ℙ} → (U : ℙ) → El V → El (U ⊔ₚ V)

  --   ⊔ₚ-elim : ∀ {ℓ} {U V : ℙ} (P : El (U ⊔ₚ V) → Set ℓ)
  --     → (inlₚ* : (u : El U) → P (inlₚ V u))
  --     → (inrₚ* : (v : El V) → P (inrₚ U v))
  --     → (w : El (U ⊔ₚ V)) → P w

  --   ⊔ₚ-inl-β : ∀ {ℓ} {U V : ℙ} (P : El (U ⊔ₚ V) → Set ℓ)
  --     → (inlₚ* : (u : El U) → P (inlₚ V u))
  --     → (inrₚ* : (v : El V) → P (inrₚ U v))
  --     → (u : El U)
  --     → ⊔ₚ-elim P inlₚ* inrₚ* (inlₚ V u) ↦ inlₚ* u
  --   {-# REWRITE ⊔ₚ-inl-β #-}

  --   ⊔ₚ-inr-β : ∀ {ℓ} {U V : ℙ} (P : El (U ⊔ₚ V) → Set ℓ)
  --     → (inlₚ* : (u : El U) → P (inlₚ V u))
  --     → (inrₚ* : (v : El V) → P (inrₚ U v))
  --     → (v : El V)
  --     → ⊔ₚ-elim P inlₚ* inrₚ* (inrₚ U v) ↦ inrₚ* v
  --   {-# REWRITE ⊔ₚ-inr-β #-}

  --   -- Σ
  --   ⟦_,_∣_,_⟧ₚ : (U : ℙ) (V : El U → ℙ)
  --     → (u : El U) (v : El (V u))
  --     → El (Σₚ U V)
      
  --   Σₚ-elim : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
  --     → (P : El (Σₚ U V) → Set ℓ)
  --     → (ρ : (u : El U) (v : El (V u)) → P ⟦ U , V ∣ u , v ⟧ₚ)
  --     → (p : El (Σₚ U V)) → P p
  
  --   Σₚ-elim-β : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
  --     → (P : El (Σₚ U V) → Set ℓ)
  --     → (ρ : (u : El U) (v : El (V u)) → P ⟦ U , V ∣ u , v ⟧ₚ)
  --     → (u : El U) (v : El (V u))
  --     → Σₚ-elim U V P ρ ⟦ U , V ∣ u , v ⟧ₚ ↦ ρ u v
  --   {-# REWRITE Σₚ-elim-β #-}
    

  --   --
  --   --  Laws 
  --   --

  --   -- Additive right unit
  --   ⊔ₚ-unit-r : (U : ℙ)
  --     → U ⊔ₚ ⊥ₚ ↦ U
  --   {-# REWRITE ⊔ₚ-unit-r #-}

  --   ⊔ₚ-unit-r-intro : (U : ℙ) (u : El U)
  --     → inlₚ ⊥ₚ u ↦ u 
  --   {-# REWRITE ⊔ₚ-unit-r-intro #-}

  --   ⊔ₚ-unit-r-elim : ∀ {ℓ} (U : ℙ)
  --     → (P : El (U ⊔ₚ ⊥ₚ) → Set ℓ)
  --     → (inlₚ* : (u : El U) → P (inlₚ ⊥ₚ u))
  --     → (inrₚ* : (v : El ⊥ₚ) → P (inrₚ U v))
  --     → ⊔ₚ-elim  P inlₚ* inrₚ* ↦ inlₚ* 
  --   {-# REWRITE ⊔ₚ-unit-r-elim #-} 

  --   -- Additive left unit
  --   ⊔ₚ-unit-l : (V : ℙ)
  --     → ⊥ₚ ⊔ₚ V ↦ V
  --   {-# REWRITE ⊔ₚ-unit-l #-}

  --   ⊔ₚ-unit-l-intro : (V : ℙ) (v : El V)
  --     → inrₚ ⊥ₚ v ↦ v
  --   {-# REWRITE ⊔ₚ-unit-l-intro #-}

  --   ⊔ₚ-unit-l-elim : ∀ {ℓ} (V : ℙ)
  --     → (P : El (⊥ₚ ⊔ₚ V) → Set ℓ)
  --     → (inlₚ* : (u : El ⊥ₚ) → P (inlₚ V u))
  --     → (inrₚ* : (v : El V) → P (inrₚ ⊥ₚ v))
  --     → ⊔ₚ-elim P inlₚ* inrₚ* ↦ inrₚ* 
  --   {-# REWRITE ⊔ₚ-unit-l-elim #-}

  --   -- Additive associativity
  --   ⊔ₚ-assoc : (U V W : ℙ)
  --     → (U ⊔ₚ V) ⊔ₚ W ↦ U ⊔ₚ V ⊔ₚ W
  --   {-# REWRITE ⊔ₚ-assoc #-}

  --   ⊔ₚ-assoc-intro-l : (U V W : ℙ) (u : El U) 
  --     → inlₚ W (inlₚ V u) ↦ inlₚ (V ⊔ₚ W) u
  --   {-# REWRITE ⊔ₚ-assoc-intro-l #-}

  --   ⊔ₚ-assoc-intro-m : (U V W : ℙ) (v : El V)
  --     → inlₚ W (inrₚ U v) ↦ inrₚ U (inlₚ W v)
  --   {-# REWRITE ⊔ₚ-assoc-intro-m #-}

  --   ⊔ₚ-assoc-intro-r : (U V W : ℙ) (w : El W)
  --     → inrₚ (U ⊔ₚ V) w ↦ inrₚ U (inrₚ V w)
  --   {-# REWRITE ⊔ₚ-assoc-intro-r #-}

  --   ⊔ₚ-assoc-elim : ∀ {ℓ} (U V W : ℙ)
  --     → (P : El ((U ⊔ₚ V) ⊔ₚ W) → Set ℓ)
  --     → (in-u* : (u : El U) → P (inlₚ W (inlₚ V u)))
  --     → (in-v* : (v : El V) → P (inlₚ W (inrₚ U v)))
  --     → (in-w* : (w : El W) → P (inrₚ (U ⊔ₚ V) w))
  --     → ⊔ₚ-elim {U = U ⊔ₚ V} {V = W} P
  --         (⊔ₚ-elim {U = U} {V = V}
  --           (λ uv → P (inlₚ W uv)) in-u* in-v*) in-w* ↦
  --           ⊔ₚ-elim {U = U} {V = V ⊔ₚ W} P in-u*
  --             (⊔ₚ-elim {U = V} {V = W} (λ vw → P (inrₚ U vw)) in-v* in-w*)
  --   {-# REWRITE ⊔ₚ-assoc-elim #-}

  --   -- Multiplicative right unit
  --   Σₚ-unit-r : (U : ℙ)
  --     → Σₚ U (λ _ → ⊤ₚ) ↦ U
  --   {-# REWRITE Σₚ-unit-r #-}

  --   Σₚ-unit-r-intro : (U : ℙ) (u : El U) (t : El ⊤ₚ)
  --     → ⟦ U , (λ _ → ⊤ₚ) ∣ u , t ⟧ₚ ↦ u
  --   {-# REWRITE Σₚ-unit-r-intro #-}

  --   Σₚ-unit-r-elim : ∀ {ℓ} (U : ℙ)
  --     → (P : El (Σₚ U (λ _ → ⊤ₚ)) → Set ℓ)
  --     → (ρ : (u : El U) (t : El ⊤ₚ) → P ⟦ U , (λ _ → ⊤ₚ) ∣ u , t ⟧ₚ)
  --     → Σₚ-elim U (λ _ → ⊤ₚ) P ρ ↦ (λ u → ρ u ttₚ)
  --   {-# REWRITE Σₚ-unit-r-elim #-}
    
  --   -- Multiplicative left unit
  --   Σₚ-unit-l : (V : El ⊤ₚ → ℙ)
  --     → Σₚ ⊤ₚ V ↦ V ttₚ
  --   {-# REWRITE Σₚ-unit-l #-}

  --   Σₚ-unit-l-intro : (V : El ⊤ₚ → ℙ) (v : El (V ttₚ))
  --     → ⟦ ⊤ₚ , V ∣ ttₚ , v ⟧ₚ ↦ v
  --   {-# REWRITE Σₚ-unit-l-intro #-}

  --   Σₚ-unit-l-elim : ∀ {ℓ} (V : El ⊤ₚ → ℙ)
  --     → (P : El (Σₚ ⊤ₚ V) → Set ℓ)
  --     → (ρ : (u : El ⊤ₚ) (v : El (V u)) → P ⟦ ⊤ₚ , V ∣ u , v ⟧ₚ)
  --     → Σₚ-elim ⊤ₚ V P ρ ↦ ρ ttₚ
  --   {-# REWRITE Σₚ-unit-l-elim #-}

  --   -- Multiplicative left zero
  --   Σₚ-zero-r : (U : ℙ)
  --     → Σₚ U (λ _ → ⊥ₚ) ↦ ⊥ₚ
  --   {-# REWRITE Σₚ-zero-r #-}

  --   Σₚ-zero-r-intro : (U : ℙ)
  --     → (u : El U) (v : El ⊥ₚ)
  --     → ⟦ U , (λ _ → ⊥ₚ) ∣ u , v ⟧ₚ ↦ v
  --   {-# REWRITE Σₚ-zero-r-intro #-}

  --   Σₚ-zero-r-elim : ∀ {ℓ} (U : ℙ)
  --     → (P : El (Σₚ U (λ _ → ⊥ₚ)) → Set ℓ)
  --     → (ρ : (u : El U) (v : El ⊥ₚ) → P ⟦ U , (λ _ → ⊥ₚ) ∣ u , v ⟧ₚ)
  --     → Σₚ-elim U (λ _ → ⊥ₚ) P ρ ↦ ⊥ₚ-elim P
  --   {-# REWRITE Σₚ-zero-r-elim #-}

  --   -- Multiplicative right zero
  --   Σₚ-zero-l : (V : El ⊥ₚ → ℙ)
  --     → Σₚ ⊥ₚ V ↦ ⊥ₚ
  --   {-# REWRITE Σₚ-zero-l #-}

  --   Σₚ-zero-l-intro : (V : El ⊥ₚ → ℙ)
  --     → (u : El ⊥ₚ) (v : El (V u))
  --     → ⟦ ⊥ₚ , V ∣ u , v ⟧ₚ ↦ u
  --   {-# REWRITE Σₚ-zero-l-intro #-}

  --   Σₚ-zero-l-elim : ∀ {ℓ} (V : El ⊥ₚ → ℙ)
  --     → (P : El (Σₚ ⊥ₚ V) → Set ℓ)
  --     → (ρ : (u : El ⊥ₚ) (v : El (V u)) → P ⟦ ⊥ₚ , V ∣ u , v ⟧ₚ)
  --     → Σₚ-elim ⊥ₚ V P ρ ↦ ⊥ₚ-elim P
  --   {-# REWRITE Σₚ-zero-l-elim #-}

  --   -- Multiplicative associativity
  --   Σₚ-assoc : (U : ℙ) (V : El U → ℙ)
  --     → (W : El (Σₚ U V) → ℙ)
  --     → Σₚ (Σₚ U V) W ↦ Σₚ U (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ))
  --   {-# REWRITE Σₚ-assoc #-}
      
  --   Σₚ-assoc-intro : (U : ℙ) (V : El U → ℙ)
  --     → (W : El (Σₚ U V) → ℙ)
  --     → (u : El U) (v : El (V u))
  --     → (w : El (W ⟦ U , V ∣ u , v ⟧ₚ))
  --     → ⟦ Σₚ U V , W ∣ ⟦ U , V ∣ u , v ⟧ₚ , w ⟧ₚ ↦
  --       ⟦ U , (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)) ∣
  --         u , ⟦ V u , (λ v → W ⟦ U , V ∣ u , v ⟧ₚ) ∣ v , w ⟧ₚ ⟧ₚ
  --   {-# REWRITE Σₚ-assoc-intro #-}

  --   Σₚ-assoc-elim : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
  --     → (W : El (Σₚ U V) → ℙ)
  --     → (P : El (Σₚ (Σₚ U V) W) → Set ℓ)
  --     → (ρ : (u : El (Σₚ U V)) (v : El (W u)) → P ⟦ Σₚ U V , W ∣ u , v ⟧ₚ)
  --     → Σₚ-elim (Σₚ U V) W P ρ ↦ 
  --       Σₚ-elim U (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)) P 
  --         (λ u → Σₚ-elim (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)
  --           (λ vw → P ⟦ U , (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)) ∣ u , vw ⟧ₚ)
  --             (λ v w → ρ ⟦ U , V ∣ u , v ⟧ₚ w))
  --   {-# REWRITE Σₚ-assoc-elim #-}

  --   -- Right Distributivity
  --   ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
  --     → (W : El (U ⊔ₚ V) → ℙ)
  --     → Σₚ (U ⊔ₚ V) W ↦ (Σₚ U (λ u → W (inlₚ V u))) ⊔ₚ (Σₚ V (λ v → W (inrₚ U v)))
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-r #-}

  --   ⊔ₚ-Σₚ-distrib-r-intro-l : (U V : ℙ)
  --     → (W : El (U ⊔ₚ V) → ℙ)
  --     → (u : El U) (w : El (W (inlₚ V u)))
  --     → ⟦ U ⊔ₚ V , W ∣ inlₚ V u , w ⟧ₚ ↦
  --         inlₚ (Σₚ V (λ v → W (inrₚ U v)))
  --              ⟦ U , (λ u → W (inlₚ V u)) ∣ u , w ⟧ₚ
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-l #-}

  --   ⊔ₚ-Σₚ-distrib-r-intro-r : (U V : ℙ)
  --     → (W : El (U ⊔ₚ V) → ℙ)
  --     → (v : El V) (w : El (W (inrₚ U v)))
  --     → ⟦ U ⊔ₚ V , W ∣ inrₚ U v , w ⟧ₚ ↦
  --         inrₚ (Σₚ U (λ u → W (inlₚ V u)))
  --              ⟦ V , (λ v → W (inrₚ U v)) ∣ v , w ⟧ₚ
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-r #-}

  --   ⊔ₚ-Σₚ-distrib-r-elim : ∀ {ℓ} (U V : ℙ)
  --     → (W : El (U ⊔ₚ V) → ℙ)
  --     → (P : El (Σₚ (U ⊔ₚ V) W) → Set ℓ)
  --     → (ρ : (uv : El (U ⊔ₚ V)) (w : El (W uv)) → P ⟦ U ⊔ₚ V , W ∣ uv , w ⟧ₚ )
  --     → Σₚ-elim (U ⊔ₚ V) W P ρ ↦
  --       ⊔ₚ-elim {U = Σₚ U (λ u → W (inlₚ V u))} {V = Σₚ V (λ v → W (inrₚ U v))} P
  --         (Σₚ-elim U (λ u → W (inlₚ V u))
  --                    (λ uw → P (inlₚ (Σₚ V (λ v → W (inrₚ U v))) uw))
  --                    (λ u w → ρ (inlₚ V u) w))
  --         (Σₚ-elim V (λ v → W (inrₚ U v))
  --                    (λ vw → P (inrₚ (Σₚ U (λ u → W (inlₚ V u))) vw))
  --                    (λ v w → ρ (inrₚ U v) w))
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-r-elim #-}

  --   -- Left distributivity
  --   ⊔ₚ-Σₚ-distrib-l : (U : ℙ)
  --     → (V : El U → ℙ) (W : El U → ℙ)
  --     → Σₚ U (λ u → V u ⊔ₚ W u) ↦ Σₚ U V ⊔ₚ Σₚ U W
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-l #-}

  --   ⊔ₚ-Σₚ-distrib-l-intro-l : (U : ℙ)
  --     → (V : El U → ℙ) (W : El U → ℙ)
  --     → (u : El U) (v : El (V u))
  --     → ⟦ U , (λ u → V u ⊔ₚ W u) ∣ u , inlₚ (W u) v ⟧ₚ ↦
  --       inlₚ (Σₚ U W) ⟦ U , V ∣ u , v ⟧ₚ
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-l #-}

  --   ⊔ₚ-Σₚ-distrib-l-intro-r : (U : ℙ)
  --     → (V : El U → ℙ) (W : El U → ℙ)
  --     → (u : El U) (w : El (W u))
  --     → ⟦ U , (λ u → V u ⊔ₚ W u) ∣ u , inrₚ (V u) w ⟧ₚ ↦
  --       inrₚ (Σₚ U V) ⟦ U , W ∣ u , w ⟧ₚ
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-r #-}

  --   ⊔ₚ-Σₚ-distrib-l-elim : ∀ {ℓ} (U : ℙ)
  --     → (V : El U → ℙ) (W : El U → ℙ)
  --     → (P : El (Σₚ U (λ u → V u ⊔ₚ W u)) → Set ℓ)
  --     → (ρ : (u : El U) (vw : El (V u ⊔ₚ W u))
  --          → P ⟦ U , (λ u₁ → V u₁ ⊔ₚ W u₁) ∣ u , vw ⟧ₚ)
  --     → Σₚ-elim U (λ u → V u ⊔ₚ W u) P ρ ↦
  --       ⊔ₚ-elim {U = Σₚ U V} {V = Σₚ U W} P
  --         (Σₚ-elim U V (λ u → P (inlₚ (Σₚ U W) u))
  --                      (λ u v → ρ u (inlₚ (W u) v)))
  --         (Σₚ-elim U W (λ u → P (inrₚ (Σₚ U V) u))
  --                      (λ u w → ρ u (inrₚ (V u) w)))
  --   {-# REWRITE ⊔ₚ-Σₚ-distrib-l-elim #-}
