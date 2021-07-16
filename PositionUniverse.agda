{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module PositionUniverse where

  infixr 40 _⊔ₚ_

  postulate

    ℙ : Set
    El : ℙ → Set

    -- Small π types and application
    πₚ : ∀ {ℓ} (P : ℙ) (X : El P → Set ℓ) → Set ℓ
    app : ∀ {ℓ} {P : ℙ} {X : El P → Set ℓ}
      → πₚ P X → (p : El P) → X p

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
    Σₚ : (U : ℙ) (V : πₚ U (cst ℙ)) → ℙ
    ⟦_,_∣_,_⟧ₚ : (U : ℙ) (V : πₚ U (cst ℙ))
      → (u : El U) (v : El (app V u))
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
    
    π-Σ : ∀ {ℓ} (U : ℙ) (V : πₚ U (cst ℙ))
      → (X : El (Σₚ U V) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ (app V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ)))
      → πₚ (Σₚ U V) X

    --
    --  Definition of App
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

    app-Σ : ∀ {ℓ} (U : ℙ) (V : πₚ U (cst ℙ))
      → (X : El (Σₚ U V) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ (app V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ)))
      → (u : El U) (v : El (app V u))
      → app (π-Σ U V X ϕ) ⟦ U , V ∣ u , v ⟧ₚ ↦ app (app ϕ u) v
    {-# REWRITE app-Σ #-}

    -- 
    --  Functorial Action
    --

    map : ∀ {ℓ₀ ℓ₁} {P : ℙ} {X : El P → Set ℓ₀}
      → {Y : (p : El P) → X p → Set ℓ₁}
      → (f : (p : El P) (x : X p) → Y p x)
      → (δ : πₚ P X) → πₚ P (λ p → Y p (app δ p))

    map-⊥ : ∀ {ℓ₀ ℓ₁} {X : El ⊥ₚ → Set ℓ₀}
      → {Y : (p : El ⊥ₚ) → X p → Set ℓ₁}
      → (f : (p : El ⊥ₚ) (x : X p) → Y p x)
      → (δ : πₚ ⊥ₚ X)
      → map f δ ↦ π-⊥ _ 
    {-# REWRITE map-⊥ #-}

    map-⊤ : ∀ {ℓ₀ ℓ₁} {X : El ⊤ₚ → Set ℓ₀}
      → {Y : (p : El ⊤ₚ) → X p → Set ℓ₁}
      → (f : (p : El ⊤ₚ) (x : X p) → Y p x)
      → (δ  : πₚ ⊤ₚ X)
      → map f δ ↦ π-⊤ _ (f ttₚ (app δ ttₚ))
    {-# REWRITE map-⊤ #-}

    map-⊔ : ∀ {ℓ₀ ℓ₁ U V} {X : El (U ⊔ₚ V) → Set ℓ₀}
      → {Y : (p : El (U ⊔ₚ V)) → X p → Set ℓ₁}
      → (f : (p : El (U ⊔ₚ V)) (x : X p) → Y p x)
      → (l : πₚ U (λ u → X (inlₚ V u)))
      → (r : πₚ V (λ v → X (inrₚ U v)))
      → map f (π-⊔ _ l r) ↦
          π-⊔ _ (map (λ u x → f (inlₚ V u) x) l)
                 (map (λ v x → f (inrₚ U v) x) r)
    {-# REWRITE map-⊔ #-} 

    map-Σ : ∀ {ℓ₀ ℓ₁} {U : ℙ} {V : πₚ U (cst ℙ)}
      → {X : El (Σₚ U V) → Set ℓ₀}
      → {Y : (p : El (Σₚ U V)) → X p → Set ℓ₁}
      → (f : (p : El (Σₚ U V)) (x : X p) → Y p x)
      → (ϕ : πₚ U (λ u → πₚ (app V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ)))
      → map f (π-Σ U V X ϕ) ↦
          π-Σ U V (λ p → Y p (app (π-Σ U V X ϕ) p))
            (map (λ u δ → map (λ v x → f ⟦ U , V ∣ u , v ⟧ₚ x) δ) ϕ)
    {-# REWRITE map-Σ #-}
      
    --
    --  Constant decorations 
    --
    
    cstₚ : ∀ {ℓ} {X : Set ℓ} (P : ℙ) (x : X)
      → πₚ P (cst X)

    cst-⊥ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → cstₚ ⊥ₚ x ↦ π-⊥ (cst X)
    {-# REWRITE cst-⊥ #-}
      
    cst-⊤ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → cstₚ ⊤ₚ x ↦ π-⊤ (cst X) x
    {-# REWRITE cst-⊤ #-}

    cst-⊔ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → {U V : ℙ}
      → cstₚ (U ⊔ₚ V) x ↦ π-⊔ (cst X) (cstₚ U x) (cstₚ V x)
    {-# REWRITE cst-⊔ #-}

    cst-Σ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → (U : ℙ) (V : πₚ U (cst ℙ))
      → cstₚ (Σₚ U V) x ↦ π-Σ U V (cst X)
        (map (λ _ P → cstₚ P x) V)
    {-# REWRITE cst-Σ #-}

    --
    --  Combinator Laws
    --

    app-cst : ∀ {ℓ} {X : Set ℓ} (P : ℙ)
      → (x : X) (p : El P)
      → app (cstₚ P x) p ↦ x
    {-# REWRITE app-cst #-} 

    map-cst : ∀ {ℓ₀ ℓ₁} {P : ℙ} {X : El P → Set ℓ₀}
      → {Y : Set ℓ₁} (y : Y)
      → (δ : πₚ P X)
      → map (λ _ _ → y) δ ↦ cstₚ P y
    {-# REWRITE map-cst #-}

    app-map : ∀ {ℓ₀ ℓ₁} {P : ℙ} {X : El P → Set ℓ₀}
      → {Y : (p : El P) → X p → Set ℓ₁}
      → (f : (p : El P) (x : X p) → Y p x)
      → (δ : πₚ P X) (p : El P)
      → app (map f δ) p ↦ f p (app δ p)
    {-# REWRITE app-map #-}

    map-app : ∀ {ℓ₀ ℓ₁} {P : ℙ} {X : El P → Set ℓ₀}
      → {Y : (p : El P) → X p → Set ℓ₁}
      → (f : (p : El P) (x : X p) → Y p x)
      → (δ : πₚ P X) (p : El P)
      → map (λ p _ → app δ p) δ ↦ δ 
    {-# REWRITE map-app #-}

    -- This version is non-dependent in the second factor.  It
    -- seems that the full, doubly dependent version does not
    -- give a valid rewrite rule.  Is this a problem?
    map-map : ∀ {ℓ₀ ℓ₁ ℓ₂} {P : ℙ} {X : El P → Set ℓ₀}
      → {Y : (p : El P) → X p → Set ℓ₁}
      → (f : (p : El P) (x : X p) → Y p x)
      → {Z : (p : El P) → Set ℓ₂}
      → (δ : πₚ P X)
      → (g : (p : El P) → Y p (app δ p) → Z p)
      → map g (map f δ) ↦ map (λ p _ → g p (f p (app δ p))) δ 
    {-# REWRITE map-map #-}

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

--     ⊔ₚ-assoc-π : ∀ {ℓ} (U V W : ℙ)
--       → (X : El ((U ⊔ₚ V) ⊔ₚ W) → Set ℓ)
--       → (in-uv : πₚ (U ⊔ₚ V) (λ uv → X (inlₚ W uv)))
--       → (in-w : πₚ W (λ w → X (inrₚ (U ⊔ₚ V) w)))
--       → π-⊔ {U = U ⊔ₚ V} {V = W} X in-uv in-w ↦
--           π-⊔ {U = U} {V = V ⊔ₚ W} X (restrict-l V in-uv)
--             (π-⊔ {U = V} {V = W} _ (restrict-r U in-uv) in-w)
--     {-# REWRITE ⊔ₚ-assoc-π #-}

    -- Multiplicative right unit
    Σₚ-unit-r : (U : ℙ)
      → Σₚ U (cstₚ U ⊤ₚ) ↦ U
    {-# REWRITE Σₚ-unit-r #-}

    Σₚ-unit-r-intro : (U : ℙ) (u : El U) (t : El ⊤ₚ)
      → ⟦ U , cstₚ U ⊤ₚ ∣ u , t ⟧ₚ ↦ u
    {-# REWRITE Σₚ-unit-r-intro #-}

    Σₚ-unit-r-π : ∀ {ℓ} (U : ℙ)
      → (X : El (Σₚ U (cstₚ U ⊤ₚ)) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ ⊤ₚ (λ t → X ⟦ U , cstₚ U ⊤ₚ ∣ u , t ⟧ₚ)))
      → π-Σ U (cstₚ U ⊤ₚ) X ϕ ↦
          map (λ _ δ → app δ ttₚ) ϕ
    {-# REWRITE Σₚ-unit-r-π #-}

    -- Multiplicative left unit
    Σₚ-unit-l : (V : πₚ ⊤ₚ (cst ℙ))
      → Σₚ ⊤ₚ V ↦ app V ttₚ
    {-# REWRITE Σₚ-unit-l #-}

    Σₚ-unit-l-intro : (V : πₚ ⊤ₚ (cst ℙ)) (v : El (app V ttₚ))
      → ⟦ ⊤ₚ , V ∣ ttₚ , v ⟧ₚ ↦ v
    {-# REWRITE Σₚ-unit-l-intro #-}

    Σₚ-unit-l-π : ∀ {ℓ} (V : πₚ ⊤ₚ (cst ℙ))
      → (X : El (Σₚ ⊤ₚ V) → Set ℓ)
      → (ϕ : πₚ ⊤ₚ (λ t → πₚ (app V t) (λ v → X ⟦ ⊤ₚ , V ∣ t , v ⟧ₚ)))
      → π-Σ ⊤ₚ V X ϕ ↦ app ϕ ttₚ 
    {-# REWRITE Σₚ-unit-l-π #-}

    -- Multiplicative left zero
    Σₚ-zero-r : (U : ℙ)
      → Σₚ U (cstₚ U ⊥ₚ) ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-r #-}

    Σₚ-zero-r-intro : (U : ℙ)
      → (u : El U) (v : El ⊥ₚ)
      → ⟦ U , cstₚ U ⊥ₚ ∣ u , v ⟧ₚ ↦ v
    {-# REWRITE Σₚ-zero-r-intro #-}

    Σₚ-zero-r-π : ∀ {ℓ} (U : ℙ)
      → (X : El (Σₚ U (cstₚ U ⊥ₚ)) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ ⊥ₚ (λ v → X ⟦ U , cstₚ U ⊥ₚ ∣ u , v ⟧ₚ)))
      → π-Σ U (cstₚ U ⊥ₚ) X ϕ ↦ π-⊥ X 
    {-# REWRITE Σₚ-zero-r-π #-}

    -- Multiplicative right zero
    Σₚ-zero-l : (V : πₚ ⊥ₚ (cst ℙ))
      → Σₚ ⊥ₚ V ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-l #-}

    Σₚ-zero-l-intro : (V : πₚ ⊥ₚ (cst ℙ))
      → (u : El ⊥ₚ) (v : El (app V u))
      → ⟦ ⊥ₚ , V ∣ u , v ⟧ₚ ↦ u
    {-# REWRITE Σₚ-zero-l-intro #-}

    Σₚ-zero-l-π : ∀ {ℓ} (V : πₚ ⊥ₚ (cst ℙ))
      → (X : El (Σₚ ⊥ₚ V) → Set ℓ)
      → (ϕ : πₚ ⊥ₚ (λ u → πₚ (app V u) (λ v → X ⟦ ⊥ₚ , V ∣ u , v ⟧ₚ)))
      → π-Σ ⊥ₚ V X ϕ ↦ π-⊥ X 
    {-# REWRITE Σₚ-zero-l-π #-}

    -- Multiplicative associativity
    Σₚ-assoc : (U : ℙ) (V : πₚ U (cst ℙ))
      → (W : πₚ U (λ u → πₚ (app V u) (cst ℙ)))
      → Σₚ (Σₚ U V) (π-Σ U V (cst ℙ) W) ↦
          Σₚ U (map (λ u δ → Σₚ (app V u) δ) W)
    {-# REWRITE Σₚ-assoc #-}

    Σₚ-assoc-intro : (U : ℙ) (V : πₚ U (cst ℙ))
      → (W : πₚ U (λ u → πₚ (app V u) (cst ℙ)))
      → (u : El U) (v : El (app V u))
      → (w : El (app (app W u) v))
      → ⟦ Σₚ U V , π-Σ U V (cst ℙ) W ∣ ⟦ U , V ∣ u , v ⟧ₚ , w ⟧ₚ ↦
          ⟦ U , map (λ u δ → Σₚ (app V u) δ) W ∣
              u , ⟦ app V u , app W u ∣ v , w ⟧ₚ ⟧ₚ
    {-# REWRITE Σₚ-assoc-intro #-}

    Σₚ-assoc-π : ∀ {ℓ} (U : ℙ) (V : πₚ U (cst ℙ))
      → (W : πₚ U (λ u → πₚ (app V u) (cst ℙ)))
      → (X : El (Σₚ (Σₚ U V) (π-Σ U V (cst ℙ) W)) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ (app V u) (λ v → πₚ (app (app W u) v) (λ w →
               X ⟦ U , map (λ u₁ → Σₚ (app V u₁)) W ∣ u ,
                   ⟦ app V u , app W u ∣ v , w ⟧ₚ ⟧ₚ))))
      → π-Σ (Σₚ U V) (π-Σ U V (cst ℙ) W) X
          (π-Σ U V (λ uv → πₚ (app (π-Σ U V (cst ℙ) W) uv) (λ w → X ⟦ Σₚ U V , π-Σ U V (cst ℙ) W ∣ uv , w ⟧ₚ)) ϕ) ↦
        π-Σ U (map (λ u → Σₚ (app V u)) W) X
          (map (λ u δ → π-Σ (app V u) (app W u) (λ vw → X ⟦ U , map (λ u₁ → Σₚ (app V u₁)) W ∣ u , vw ⟧ₚ) δ) ϕ)
    {-# REWRITE Σₚ-assoc-π #-} 

--     -- Right Distributivity
--     ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
--       → (W : πₚ (U ⊔ₚ V) (cst ℙ))
--       → Σₚ (U ⊔ₚ V) W ↦
--           Σₚ U (restrict-l V W) ⊔ₚ Σₚ V (restrict-r U W)
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-r #-}

--     ⊔ₚ-Σₚ-distrib-r-intro-l : (U V : ℙ)
--       → (W : πₚ (U ⊔ₚ V) (cst ℙ))
--       → (u : El U) (w : El (app W (inlₚ V u)))
--       → ⟦ U ⊔ₚ V , W ∣ inlₚ V u , w ⟧ₚ ↦
--           inlₚ (Σₚ V (restrict-r U W)) ⟦ U , restrict-l V W ∣ u , w ⟧ₚ
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-l #-}

--     ⊔ₚ-Σₚ-distrib-r-intro-r : (U V : ℙ)
--       → (W : πₚ (U ⊔ₚ V) (cst ℙ))
--       → (v : El V) (w : El (app W (inrₚ U v)))
--       → ⟦ U ⊔ₚ V , W ∣ inrₚ U v , w ⟧ₚ ↦
--           inrₚ (Σₚ U (restrict-l V W)) ⟦ V , restrict-r U W ∣ v , w ⟧ₚ 
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-r #-}
    
--     ⊔ₚ-Σₚ-distrib-r-π : ∀ {ℓ} (U V : ℙ)
--       → (W : πₚ (U ⊔ₚ V) (cst ℙ))
--       → (X : El (Σₚ (U ⊔ₚ V) W) → Set ℓ)
--       → (ϕ : πₚ (U ⊔ₚ V) (λ uv → πₚ (app W uv) (λ w → X ⟦ U ⊔ₚ V , W ∣ uv , w ⟧ₚ)))
--       → π-Σ (U ⊔ₚ V) W X ϕ ↦
--           π-⊔ {U = Σₚ U (restrict-l V W)}
--               {V = Σₚ V (restrict-r U W)} X
--               (π-Σ U (restrict-l V W) (λ u →
--                 X (inlₚ (Σₚ V (restrict-r U W)) u)) (restrict-l {U = U} V ϕ))
--               (π-Σ V (restrict-r U W) (λ v →
--                 X (inrₚ (Σₚ U (restrict-l V W)) v)) (restrict-r U {V = V} ϕ)) 
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-r-π #-}

--     -- Left Distributivity
--     ⊔ₚ-Σₚ-distrib-l : {U : ℙ}
--       → (V : πₚ U (cst ℙ)) (W : πₚ U (cst ℙ))
--       → Σₚ U (map (λ u ϕ → ϕ (app W u))
--                (map (λ _ P Q → P ⊔ₚ Q) V))
--          ↦ Σₚ U V ⊔ₚ Σₚ U W
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-l #-}

--     ⊔ₚ-Σₚ-distrib-l-intro-l : {U : ℙ}
--       → (V : πₚ U (cst ℙ)) (W : πₚ U (cst ℙ))
--       → (u : El U) (v : El (app V u))
--       → ⟦ U , (map (λ u ϕ → ϕ (app W u))
--                (map (λ _ P Q → P ⊔ₚ Q) V)) ∣ u , inlₚ (app W u) v ⟧ₚ ↦
--           inlₚ (Σₚ U W) ⟦ U , V ∣ u , v ⟧ₚ
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-l #-}

--     ⊔ₚ-Σₚ-distrib-l-intro-r : {U : ℙ}
--       → (V : πₚ U (cst ℙ)) (W : πₚ U (cst ℙ))
--       → (u : El U) (w : El (app W u))
--       → ⟦ U , (map (λ u ϕ → ϕ (app W u))
--                (map (λ _ P Q → P ⊔ₚ Q) V)) ∣ u , inrₚ (app V u) w ⟧ₚ ↦
--           inrₚ (Σₚ U V) ⟦ U , W ∣ u , w ⟧ₚ
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-r #-}

--     -- Perhaps define the fiberwise application
--     -- of _⊔_ separately to clean this up ...
--     ⊔ₚ-Σₚ-distrib-l-π : ∀ {ℓ} {U : ℙ}
--       → (V : πₚ U (cst ℙ)) (W : πₚ U (cst ℙ))
--       → (X : El (Σₚ U (map (λ u ϕ → ϕ (app W u))
--                       (map (λ _ P Q → P ⊔ₚ Q) V))) → Set ℓ)
--       → (ϕ : πₚ U (λ u → πₚ (app V u ⊔ₚ app W u)
--                  (λ vw → X ⟦ U , map (λ u ϕ → ϕ (app W u)) (map (λ _ P Q → P ⊔ₚ Q) V) ∣ u , vw ⟧ₚ)))
--       → π-Σ U (map (λ u ϕ → ϕ (app W u))
--                       (map (λ _ P Q → P ⊔ₚ Q) V)) X ϕ ↦
--         π-⊔ {U = Σₚ U V} {V = Σₚ U W} X
--           (π-Σ U V (λ u → X (inlₚ (Σₚ U W) u))
--             (map {Y = λ u _ → πₚ (app V u) (λ v → X (inlₚ (Σₚ U W) ⟦ U , V ∣ u , v ⟧ₚ))}
--               (λ u δ → restrict-l {U = app V u} (app W u) δ) ϕ))
--           (π-Σ U W (λ v → X (inrₚ (Σₚ U V) v))
--             (map {Y = λ u _ → πₚ (app W u) (λ v → X (inrₚ (Σₚ U V) ⟦ U , W ∣ u , v ⟧ₚ))}
--               (λ u δ → restrict-r (app V u) {V = app W u} δ) ϕ))
--     {-# REWRITE ⊔ₚ-Σₚ-distrib-l-π #-}
    
--     --
--     --  Question: given that we have added the relations to π, do we
--     --  *also* need to add them to app?  Or should they just compute
--     --  to the same thing?  Does this introduce confluence problems?
--     -- 
