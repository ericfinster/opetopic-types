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

    --  Functorial Action
    --

    -- Okay.  This seems to really be the one you want...
    -- The previous is a special case....
    map-dep : ∀ {ℓ₀ ℓ₁} {P : ℙ} {X : El P → Set ℓ₀}
      → {Y : (p : El P) → X p → Set ℓ₁}
      → (f : (p : El P) (x : X p) → Y p x)
      → (δ : πₚ P X) → πₚ P (λ p → Y p (app δ p))

    -- I guess the next two are definable in terms
    -- of the previous guy?
    -- map : ∀ {ℓ₀ ℓ₁} {P : ℙ} {X : El P → Set ℓ₀}
    --   → {Y : El P → Set ℓ₁}
    --   → (f : (p : El P) → X p → Y p)
    --   → πₚ P X → πₚ P Y 

    -- map2 : ∀ {ℓ₀ ℓ₁ ℓ₂} {P : ℙ} {X : El P → Set ℓ₀}
    --   → {Y : El P → Set ℓ₁} {Z : El P → Set ℓ₂}
    --   → (f : (p : El P) → X p → Y p → Z p)
    --   → πₚ P X → πₚ P Y → πₚ P Z  


    --
    --  Constant decorations  (is this "return" for the monad?)
    --
    
    cstₚ : ∀ {ℓ} {X : Set ℓ} (P : ℙ) (x : X)
      → πₚ P (cst X)

    cst-⊥ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → cstₚ ⊥ₚ x ↦ π-⊥ (cst X)
      
    cst-⊤ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → cstₚ ⊤ₚ x ↦ π-⊤ (cst X) x

    cst-⊔ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → {U V : ℙ}
      → cstₚ (U ⊔ₚ V) x ↦ π-⊔ (cst X) (cstₚ U x) (cstₚ V x)

    cst-Σ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → (U : ℙ) (V : πₚ U (cst ℙ))
      → cstₚ (Σₚ U V) x ↦ π-Σ U V (cst X)
        (map-dep {X = cst ℙ} {Y = λ p P → πₚ P (cst X)} (λ _ P → cstₚ P x) V) 

    cst-app : ∀ {ℓ} {X : Set ℓ} (P : ℙ)
      → (x : X) (p : El P)
      → app (cstₚ P x) p ↦ x
    {-# REWRITE cst-app #-} 
  
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
      → (in-u* : πₚ U (λ u → X (inlₚ W (inlₚ V u))))
      → (in-v* : πₚ V (λ v → X (inlₚ W (inrₚ U v))))
      → (in-w* : πₚ W (λ w → X (inrₚ (U ⊔ₚ V) w)))
      → π-⊔ {U = U ⊔ₚ V} {V = W} X
          (π-⊔ {U = U} {V = V} (λ uv → X (inlₚ W uv)) in-u* in-v*) in-w*
          ↦ π-⊔ {U = U} {V = V ⊔ₚ W} X in-u*
              (π-⊔ {U = V} {V = W} (λ vw → X (inrₚ U vw)) in-v* in-w*)
    {-# REWRITE ⊔ₚ-assoc-π #-}

    -- Multiplicative right unit
    Σₚ-unit-r : (U : ℙ)
      → Σₚ U (cstₚ U ⊤ₚ) ↦ U
    {-# REWRITE Σₚ-unit-r #-}

    Σₚ-unit-r-intro : (U : ℙ) (u : El U) (t : El ⊤ₚ)
      → ⟦ U , cstₚ U ⊤ₚ ∣ u , t ⟧ₚ ↦ u
    {-# REWRITE Σₚ-unit-r-intro #-}

    -- Can this be done more simply?
    Σₚ-unit-r-π : ∀ {ℓ} (U : ℙ)
      → (X : El (Σₚ U (cstₚ U ⊤ₚ)) → Set ℓ)
      → (ϕ : πₚ U (λ u → πₚ ⊤ₚ (λ t → X ⟦ U , cstₚ U ⊤ₚ ∣ u , t ⟧ₚ)))
      → π-Σ U (cstₚ U ⊤ₚ) X ϕ ↦
          map-dep {X = λ u → πₚ ⊤ₚ (cst (X u))}
                  {Y = λ u δ → X u}
                  (λ _ δ → app δ ttₚ) ϕ
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

    -- -- Multiplicative associativity
    -- Σₚ-assoc : (U : ℙ) (V : El U → ℙ)
    --   → (W : El (Σₚ U V) → ℙ)
    --   → Σₚ (Σₚ U V) W ↦ Σₚ U (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ))
    -- {-# REWRITE Σₚ-assoc #-}

    -- Σₚ-assoc-intro : (U : ℙ) (V : El U → ℙ)
    --   → (W : El (Σₚ U V) → ℙ)
    --   → (u : El U) (v : El (V u))
    --   → (w : El (W ⟦ U , V ∣ u , v ⟧ₚ))
    --   → ⟦ Σₚ U V , W ∣ ⟦ U , V ∣ u , v ⟧ₚ , w ⟧ₚ ↦
    --     ⟦ U , (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)) ∣
    --       u , ⟦ V u , (λ v → W ⟦ U , V ∣ u , v ⟧ₚ) ∣ v , w ⟧ₚ ⟧ₚ
    -- {-# REWRITE Σₚ-assoc-intro #-}

    -- -- Right Distributivity
    -- ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
    --   → (W : El (U ⊔ₚ V) → ℙ)
    --   → Σₚ (U ⊔ₚ V) W ↦ Σₚ U (λ u → W (inlₚ V u)) ⊔ₚ Σₚ V (λ v → W (inrₚ U v))
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r #-}

    -- ⊔ₚ-Σₚ-distrib-r-intro-l : (U V : ℙ)
    --   → (W : El (U ⊔ₚ V) → ℙ)
    --   → (u : El U) (w : El (W (inlₚ V u)))
    --   → ⟦ U ⊔ₚ V , W ∣ inlₚ V u , w ⟧ₚ ↦
    --       inlₚ (Σₚ V (λ v → W (inrₚ U v)))
    --            ⟦ U , (λ u → W (inlₚ V u)) ∣ u , w ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-l #-}

    -- ⊔ₚ-Σₚ-distrib-r-intro-r : (U V : ℙ)
    --   → (W : El (U ⊔ₚ V) → ℙ)
    --   → (v : El V) (w : El (W (inrₚ U v)))
    --   → ⟦ U ⊔ₚ V , W ∣ inrₚ U v , w ⟧ₚ ↦
    --       inrₚ (Σₚ U (λ u → W (inlₚ V u)))
    --            ⟦ V , (λ v → W (inrₚ U v)) ∣ v , w ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-r-intro-r #-}

    -- -- Left Distributivity
    -- ⊔ₚ-Σₚ-distrib-l : {U : ℙ}
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → Σₚ U (λ u → V u ⊔ₚ W u) ↦ Σₚ U V ⊔ₚ Σₚ U W
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l #-}

    -- ⊔ₚ-Σₚ-distrib-l-intro-l : (U : ℙ)
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → (u : El U) (v : El (V u))
    --   → ⟦ U , (λ u → V u ⊔ₚ W u) ∣ u , inlₚ (W u) v ⟧ₚ ↦
    --     inlₚ (Σₚ U W) ⟦ U , V ∣ u , v ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-l #-}

    -- ⊔ₚ-Σₚ-distrib-l-intro-r : (U : ℙ)
    --   → (V : El U → ℙ) (W : El U → ℙ)
    --   → (u : El U) (w : El (W u))
    --   → ⟦ U , (λ u → V u ⊔ₚ W u) ∣ u , inrₚ (V u) w ⟧ₚ ↦
    --     inrₚ (Σₚ U V) ⟦ U , W ∣ u , w ⟧ₚ
    -- {-# REWRITE ⊔ₚ-Σₚ-distrib-l-intro-r #-}

    --
    --  Question: given that we have added the relations to π, do we
    --  *also* need to add them to app?  Or should they just compute
    --  to the same thing?  Does this introduce confluence problems?
    -- 
