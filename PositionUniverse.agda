{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module PositionUniverse where

  infixr 40 _⊔ₚ_

  postulate

    ℙ : Set
    El : ℙ → Set

    -- Small elim
    πₚ : ∀ {ℓ} (P : ℙ) (X : El P → Set ℓ) → Set ℓ

    -- Conversion to functions
    app : ∀ {ℓ} {P : ℙ} {X : El P → Set ℓ}
      → πₚ P X → (p : El P) → X p
    lam : ∀ {ℓ} (P : ℙ) {X : El P → Set ℓ}
      → (σ : (p : El P) → X p)
      → πₚ P X

    -- Empty
    ⊥ₚ : ℙ

    -- Unit
    ⊤ₚ : ℙ
    ttₚ : El ⊤ₚ

    -- Binary sum
    _⊔ₚ_ : ℙ → ℙ → ℙ
    inlₚ : {U : ℙ} (V : ℙ) → El U → El (U ⊔ₚ V)
    inrₚ : (U : ℙ) {V : ℙ} → El V → El (U ⊔ₚ V)

    -- Binary multiplication 
    Σₚ : (U : ℙ) (V : El U → ℙ) → ℙ 
    ⟦_,_∣_,_⟧ₚ : (U : ℙ) (V : El U → ℙ)
      → (u : El U) (v : El (V u))
      → El (Σₚ U V) 

    --
    --  Small eliminator constructors
    --
    
    π-⊥ : ∀ {ℓ} (X : El ⊥ₚ → Set ℓ)
      → πₚ ⊥ₚ X
      
    π-⊤ : ∀ {ℓ} (X : El ⊤ₚ → Set ℓ)
      (x : X ttₚ) → πₚ ⊤ₚ X

    π-⊔ : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → πₚ U (λ u → X (inlₚ V u))
      → πₚ V (λ v → X (inrₚ U v))
      → πₚ (U ⊔ₚ V) X 

    -- Can we make U and V implicit here?
    π-Σ : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
      → (X : El (Σₚ U V) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ (V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ)))
      → πₚ (Σₚ U V) X

    --
    --  App 
    --

    app-⊤ : ∀ {ℓ} {X : El ⊤ₚ → Set ℓ} {x : X ttₚ}
      → app (π-⊤ X x) ttₚ ↦ x
    {-# REWRITE app-⊤ #-}

    app-⊔-inl : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → (σl : πₚ U (λ u → X (inlₚ V u)))
      → (σr : πₚ V (λ v → X (inrₚ U v)))
      → (u : El U)
      → app (π-⊔ X σl σr) (inlₚ V u) ↦ app σl u
    {-# REWRITE app-⊔-inl #-}

    app-⊔-inr : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → (σl : πₚ U (λ u → X (inlₚ V u)))
      → (σr : πₚ V (λ v → X (inrₚ U v)))
      → (v : El V)
      → app (π-⊔ X σl σr) (inrₚ U v) ↦ app σr v
    {-# REWRITE app-⊔-inr #-}

    app-Σ : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
      → (X : El (Σₚ U V) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ (V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ)))
      → (u : El U) (v : El (V u))
      → app (π-Σ U V X ϕ) ⟦ U , V ∣ u , v ⟧ₚ ↦ app (app ϕ u) v
    {-# REWRITE app-Σ #-}

    --
    --  Lam
    --

    lam-⊥ : ∀ {ℓ} {X : El ⊥ₚ → Set ℓ}
      → (σ : (p : El ⊥ₚ) → X p)
      → lam ⊥ₚ σ ↦ π-⊥ _
    {-# REWRITE lam-⊥ #-}
  
    lam-⊤ : ∀ {ℓ} {X : El ⊤ₚ → Set ℓ}
      → (σ : (p : El ⊤ₚ) → X p)
      → lam ⊤ₚ σ ↦ π-⊤ _ (σ ttₚ)
    {-# REWRITE lam-⊤ #-}

    lam-⊔ : ∀ {ℓ U V} {X : El (U ⊔ₚ V) → Set ℓ}
      → (σ : (p : El (U ⊔ₚ V)) → X p)
      → lam (U ⊔ₚ V) σ ↦ π-⊔ X
          (lam U (λ u → σ (inlₚ V u)))
          (lam V (λ v → σ (inrₚ U v)))
    {-# REWRITE lam-⊔ #-}

    lam-Σ : ∀ {ℓ} {U : ℙ} {V : El U → ℙ}
      → {X : El (Σₚ U V) → Set ℓ}
      → (σ : (p : El (Σₚ U V)) → X p)
      → lam (Σₚ U V) σ ↦ π-Σ U V X (lam U (λ u →
          lam (V u) (λ v → σ ⟦ U , V ∣ u , v ⟧ₚ)))
    {-# REWRITE lam-Σ #-}
      
    --
    --  App/Lam Laws
    --

    app-lam : ∀ {ℓ} (P : ℙ) {X : El P → Set ℓ}
      → (σ : (p : El P) → X p)
      → app (lam P σ) ↦ σ
    {-# REWRITE app-lam #-}

    lam-app : ∀ {ℓ} (P : ℙ) {X : El P → Set ℓ}
      → (δ : πₚ P X)
      → lam P (λ p → app δ p) ↦ δ
    {-# REWRITE lam-app #-}

    --
    --  Laws for Positions
    --

    -- Additive right unit
    ⊔ₚ-unit-r : (U : ℙ)
      → U ⊔ₚ ⊥ₚ ↦ U
    {-# REWRITE ⊔ₚ-unit-r #-}

    ⊔ₚ-unit-r-intro : (U : ℙ) (u : El U)
      → inlₚ ⊥ₚ u ↦ u 
    {-# REWRITE ⊔ₚ-unit-r-intro #-}

    ⊔ₚ-unit-r-π : ∀ {ℓ} {U : ℙ}
      → (X : El (U ⊔ₚ ⊥ₚ) → Set ℓ)
      → (σl : πₚ U (λ u → X (inlₚ ⊥ₚ u)))
      → (σr : πₚ ⊥ₚ (λ b → X (inrₚ U b)))
      → π-⊔ X σl σr ↦ σl
    {-# REWRITE ⊔ₚ-unit-r-π #-}

    -- Additive left unit
    ⊔ₚ-unit-l : (V : ℙ)
      → ⊥ₚ ⊔ₚ V ↦ V
    {-# REWRITE ⊔ₚ-unit-l #-}

    ⊔ₚ-unit-l-intro : (V : ℙ) (v : El V)
      → inrₚ ⊥ₚ v ↦ v
    {-# REWRITE ⊔ₚ-unit-l-intro #-}

    ⊔ₚ-unit-l-π : ∀ {ℓ} {V : ℙ}
      → (X : El (⊥ₚ ⊔ₚ V) → Set ℓ)
      → (σl : πₚ ⊥ₚ (λ u → X (inlₚ V u)))
      → (σr : πₚ V (λ v → X (inrₚ ⊥ₚ v)))
      → π-⊔ X σl σr ↦ σr
    {-# REWRITE ⊔ₚ-unit-l-π #-}

    -- Additive associativity
    ⊔ₚ-assoc : (U V W : ℙ)
      → (U ⊔ₚ V) ⊔ₚ W ↦ U ⊔ₚ V ⊔ₚ W
    {-# REWRITE ⊔ₚ-assoc #-}

    ⊔ₚ-assoc-intro-l : (U V W : ℙ) (u : El U) 
      → inlₚ W (inlₚ V u) ↦ inlₚ (V ⊔ₚ W) u
    {-# REWRITE ⊔ₚ-assoc-intro-l #-}

    ⊔ₚ-assoc-intro-m : (U V W : ℙ) (v : El V)
      → inlₚ W (inrₚ U v) ↦ inrₚ U (inlₚ W v)
    {-# REWRITE ⊔ₚ-assoc-intro-m #-}

    ⊔ₚ-assoc-intro-r : (U V W : ℙ) (w : El W)
      → inrₚ (U ⊔ₚ V) w ↦ inrₚ U (inrₚ V w)
    {-# REWRITE ⊔ₚ-assoc-intro-r #-}

    ⊔ₚ-assoc-π : ∀ {ℓ} (U V W : ℙ)
      → (X : El ((U ⊔ₚ V) ⊔ₚ W) → Set ℓ)
      → (in-uv : πₚ (U ⊔ₚ V) (λ uv → X (inlₚ W uv)))
      → (in-w : πₚ W (λ w → X (inrₚ (U ⊔ₚ V) w)))
      → π-⊔ {U = U ⊔ₚ V} {V = W} X in-uv in-w ↦
          π-⊔ {U = U} {V = V ⊔ₚ W} X (lam U (λ u → app in-uv (inlₚ V u)))
            (π-⊔ {U = V} {V = W} _ (lam V (λ v → app in-uv (inrₚ U v))) in-w)
    {-# REWRITE ⊔ₚ-assoc-π #-}

    -- Multiplicative right unit
    Σₚ-unit-r : (U : ℙ)
      → Σₚ U (cst ⊤ₚ) ↦ U
    {-# REWRITE Σₚ-unit-r #-}

    Σₚ-unit-r-intro : (U : ℙ) (u : El U) (t : El ⊤ₚ)
      → ⟦ U , cst ⊤ₚ ∣ u , t ⟧ₚ ↦ u
    {-# REWRITE Σₚ-unit-r-intro #-}

    Σₚ-unit-r-π : ∀ {ℓ} (U : ℙ)
      → (X : El (Σₚ U (cst ⊤ₚ)) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ ⊤ₚ (λ t → X ⟦ U , cst ⊤ₚ ∣ u , t ⟧ₚ)))
      → π-Σ U (cst ⊤ₚ) X ϕ ↦
          lam U (λ u → app (app ϕ u) ttₚ) 
    {-# REWRITE Σₚ-unit-r-π #-}

    -- Multiplicative left unit
    Σₚ-unit-l : (V : El ⊤ₚ → ℙ)
      → Σₚ ⊤ₚ V ↦ V ttₚ
    {-# REWRITE Σₚ-unit-l #-}

    Σₚ-unit-l-intro : (V : El ⊤ₚ → ℙ)
      → (v : El (V ttₚ))
      → ⟦ ⊤ₚ , V ∣ ttₚ , v ⟧ₚ ↦ v
    {-# REWRITE Σₚ-unit-l-intro #-}

    Σₚ-unit-l-π : ∀ {ℓ} (V : El ⊤ₚ → ℙ)
      → (X : El (Σₚ ⊤ₚ V) → Set ℓ)
      → (ϕ : πₚ ⊤ₚ (λ t → πₚ (V t) (λ v → X ⟦ ⊤ₚ , V ∣ t , v ⟧ₚ)))
      → π-Σ ⊤ₚ V X ϕ ↦ app ϕ ttₚ 
    {-# REWRITE Σₚ-unit-l-π #-}

    -- -- Multiplicative left zero
    -- Σₚ-zero-r : (U : ℙ)
    --   → Σₚ U (lam U (cst ⊥ₚ)) ↦ ⊥ₚ
    -- {-# REWRITE Σₚ-zero-r #-}

    -- Σₚ-zero-r-intro : (U : ℙ)
    --   → (u : El U) (v : El ⊥ₚ)
    --   → ⟦ U , lam U (cst ⊥ₚ) ∣ u , v ⟧ₚ ↦ v
    -- {-# REWRITE Σₚ-zero-r-intro #-}

    -- Σₚ-zero-r-π : ∀ {ℓ} (U : ℙ)
    --   → (X : El (Σₚ U (lam U (cst ⊥ₚ))) → Set ℓ)
    --   → (ϕ : πₚ U (λ u → πₚ ⊥ₚ (λ v → X ⟦ U , lam U (cst ⊥ₚ) ∣ u , v ⟧ₚ)))
    --   → π-Σ U (lam U (cst ⊥ₚ)) X ϕ ↦ π-⊥ X 
    -- {-# REWRITE Σₚ-zero-r-π #-}

    -- -- Multiplicative right zero
    -- Σₚ-zero-l : (V : πₚ ⊥ₚ (cst ℙ))
    --   → Σₚ ⊥ₚ V ↦ ⊥ₚ
    -- {-# REWRITE Σₚ-zero-l #-}

    -- Σₚ-zero-l-intro : (V : πₚ ⊥ₚ (cst ℙ))
    --   → (u : El ⊥ₚ) (v : El (app V u))
    --   → ⟦ ⊥ₚ , V ∣ u , v ⟧ₚ ↦ u
    -- {-# REWRITE Σₚ-zero-l-intro #-}

    -- Σₚ-zero-l-π : ∀ {ℓ} (V : πₚ ⊥ₚ (cst ℙ))
    --   → (X : El (Σₚ ⊥ₚ V) → Set ℓ)
    --   → (ϕ : πₚ ⊥ₚ (λ u → πₚ (app V u) (λ v → X ⟦ ⊥ₚ , V ∣ u , v ⟧ₚ)))
    --   → π-Σ ⊥ₚ V X ϕ ↦ π-⊥ X 
    -- {-# REWRITE Σₚ-zero-l-π #-}

    -- -- Multiplicative associativity
    -- Σₚ-assoc : (U : ℙ) (V : El U → ℙ)
    --   → (W : πₚ (Σₚ U V) (cst ℙ))
    --   → Σₚ (Σₚ U V) W ↦
    --       Σₚ U (lam U (λ u →
    --         Σₚ (app V u) (lam (app V u) (λ v →
    --            app W ⟦ U , V ∣ u , v ⟧ₚ))))
    -- {-# REWRITE Σₚ-assoc #-}

    -- Σₚ-assoc-intro : (U : ℙ) (V : El U → ℙ)
    --   → (W : πₚ (Σₚ U V) (cst ℙ))
    --   → (u : El U) (v : El (app V u))
    --   → (w : El (app W ⟦ U , V ∣ u , v ⟧ₚ))
    --   → ⟦ Σₚ U V , W ∣ ⟦ U , V ∣ u , v ⟧ₚ , w ⟧ₚ ↦
    --       ⟦ U , lam U (λ u →
    --         Σₚ (app V u) (lam (app V u) (λ v →
    --            app W ⟦ U , V ∣ u , v ⟧ₚ))) ∣ u ,
    --         ⟦ app V u , lam (app V u) (λ v → app W ⟦ U , V ∣ u , v ⟧ₚ) ∣
    --           v , w ⟧ₚ ⟧ₚ
    -- {-# REWRITE Σₚ-assoc-intro #-}

    -- Σₚ-assoc-π : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
    --   → (W : πₚ (Σₚ U V) (cst ℙ))
    --   → (X : El (Σₚ (Σₚ U V) W) → Set ℓ)
    --   → (ϕ : πₚ (Σₚ U V) (λ uv → πₚ (app W uv) (λ w → X ⟦ Σₚ U V , W ∣ uv , w ⟧ₚ)))
    --   → π-Σ (Σₚ U V) W X ϕ ↦ π-Σ U (lam U (λ u →
    --         Σₚ (app V u) (lam (app V u) (λ v →
    --            app W ⟦ U , V ∣ u , v ⟧ₚ)))) X
    --      (lam U (λ u → π-Σ (app V u) (lam (app V u) (λ v → app W ⟦ U , V ∣ u , v ⟧ₚ)) _
    --        (lam (app V u) (λ v → lam (app W ⟦ U , V ∣ u , v ⟧ₚ) (λ w →
    --          app (app ϕ ⟦ U , V ∣ u , v ⟧ₚ) w)))))
    -- {-# REWRITE Σₚ-assoc-π #-}

    -- -- Right Distributivity
    -- ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
    --   → (W : πₚ (U ⊔ₚ V) (cst ℙ))
    --   → Σₚ (U ⊔ₚ V) W ↦
    --       Σₚ U (lam U (λ u → app W (inlₚ V u))) ⊔ₚ
    --       Σₚ V (lam V (λ v → app W (inrₚ U v)))
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r #-}

    -- ⊔ₚ-Σₚ-distrib-r-intro-l : (U V : ℙ)
    --   → (W : πₚ (U ⊔ₚ V) (cst ℙ))
    --   → (u : El U) (w : El (app W (inlₚ V u)))
    --   → ⟦ U ⊔ₚ V , W ∣ inlₚ V u , w ⟧ₚ ↦
    --       inlₚ (Σₚ V (lam V (λ v → app W (inrₚ U v))))
    --         ⟦ U , lam U (λ u → app W (inlₚ V u)) ∣ u , w ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-l #-}

    -- ⊔ₚ-Σₚ-distrib-r-intro-r : (U V : ℙ)
    --   → (W : πₚ (U ⊔ₚ V) (cst ℙ))
    --   → (v : El V) (w : El (app W (inrₚ U v)))
    --   → ⟦ U ⊔ₚ V , W ∣ inrₚ U v , w ⟧ₚ ↦
    --       inrₚ (Σₚ U (lam U (λ u → app W (inlₚ V u))))
    --         ⟦ V , (lam V (λ v → app W (inrₚ U v))) ∣ v , w ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-r #-}
    
    -- ⊔ₚ-Σₚ-distrib-r-π : ∀ {ℓ} (U V : ℙ)
    --   → (W : πₚ (U ⊔ₚ V) (cst ℙ))
    --   → (X : El (Σₚ (U ⊔ₚ V) W) → Set ℓ)
    --   → (ϕ : πₚ (U ⊔ₚ V) (λ uv → πₚ (app W uv) (λ w → X ⟦ U ⊔ₚ V , W ∣ uv , w ⟧ₚ)))
    --   → π-Σ (U ⊔ₚ V) W X ϕ ↦
    --       π-⊔ {U = Σₚ U (lam U (λ u → app W (inlₚ V u)))}
    --           {V = Σₚ V (lam V (λ v → app W (inrₚ U v)))} X
    --           (π-Σ U (lam U (λ u → app W (inlₚ V u)))
    --             (λ uw → X (inlₚ (Σₚ V (lam V (λ v → app W (inrₚ U v)))) uw))
    --             (lam U (λ u → lam (app W (inlₚ V u)) (λ w → app (app ϕ (inlₚ V u)) w))))
    --           (π-Σ V (lam V (λ v → app W (inrₚ U v)))
    --             (λ vw → X (inrₚ (Σₚ U (lam U (λ u → app W (inlₚ V u)))) vw))
    --             (lam V (λ v → lam (app W (inrₚ U v)) (λ w → app (app ϕ (inrₚ U v)) w))))
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r-π #-}

    -- -- Left Distributivity
    -- ⊔ₚ-Σₚ-distrib-l : {U : ℙ}
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → Σₚ U (lam U (λ u → app V u ⊔ₚ app W u))
    --      ↦ Σₚ U V ⊔ₚ Σₚ U W
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l #-}

    -- ⊔ₚ-Σₚ-distrib-l-intro-l : {U : ℙ}
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → (u : El U) (v : El (app V u))
    --   → ⟦ U , lam U (λ u → app V u ⊔ₚ app W u) ∣
    --       u , inlₚ (app W u) v ⟧ₚ ↦
    --       inlₚ (Σₚ U W) ⟦ U , V ∣ u , v ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-l #-}

    -- ⊔ₚ-Σₚ-distrib-l-intro-r : {U : ℙ}
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → (u : El U) (w : El (app W u))
    --   → ⟦ U , lam U (λ u → app V u ⊔ₚ app W u) ∣
    --       u , inrₚ (app V u) w ⟧ₚ ↦
    --       inrₚ (Σₚ U V) ⟦ U , W ∣ u , w ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-r #-}

    -- ⊔ₚ-Σₚ-distrib-l-π : ∀ {ℓ} {U : ℙ}
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → (X : El (Σₚ U (lam U (λ u → app V u ⊔ₚ app W u))) → Set ℓ)
    --   → (ϕ : πₚ U (λ u → πₚ (app V u ⊔ₚ app W u)
    --              (λ vw → X ⟦ U , lam U (λ u → app V u ⊔ₚ app W u) ∣ u , vw ⟧ₚ)))
    --   → π-Σ U (lam U (λ u → app V u ⊔ₚ app W u)) X ϕ ↦
    --       π-⊔ {U = Σₚ U V} {V = Σₚ U W} X
    --         (π-Σ U V (λ uv → X (inlₚ (Σₚ U W) uv) )
    --           (lam U (λ u → lam (app V u) (λ v → app (app ϕ u) (inlₚ (app W u) v)))))
    --         (π-Σ U W (λ uw → X (inrₚ (Σₚ U V) uw))
    --           (lam U (λ u → lam (app W u) (λ w → app (app ϕ u) (inrₚ (app V u) w)))))
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l-π #-}
    
    -- --
    -- --  Question: given that we have added the relations to π, do we
    -- --  *also* need to add them to app?  Or should they just compute
    -- --  to the same thing?  Does this introduce confluence problems?
    -- -- 
