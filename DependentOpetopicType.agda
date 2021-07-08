{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse
open import AbsoluteOpetopicTypes

module DependentOpetopicType where

  --
  --  The Universe of Dependent Opetopic Types
  --

  𝕆↓ : ∀ {ℓ : Level} {n : ℕ} (ℓ↓ : Level) (X : 𝕆 ℓ n)
    → Set (ℓ-max ℓ (ℓ-suc ℓ↓))
    
  Frm↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    (f : Frm X) → Set ℓ↓

  postulate

    --
    -- Dependent Frame Decorations
    --
    
    FrmDec↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → (X↓ : 𝕆↓ ℓ↓ X) {P : ℙ}
      → FrmDec X P → Set ℓ↓

    ⊥-dec↓ :  ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X}
      → FrmDec↓ X↓ ⊥-dec
      
    ⊤-dec↓ :  ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {f : Frm X} (f↓ : Frm↓ X↓ f)
      → FrmDec↓ X↓ (⊤-dec f)
  
    ⊔-dec↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U V : ℙ}
      → {l : FrmDec X U} {r : FrmDec X V}
      → FrmDec↓ X↓ l → FrmDec↓ X↓ r
      → FrmDec↓ X↓ (⊔-dec l r)

    Σ-dec↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U : ℙ} {V : El U → ℙ}
      → {ρ : (u : El U) → FrmDec X (V u)}
      → (ρ↓ : (u : El U) → FrmDec↓ X↓ (ρ u))
      → FrmDec↓ X↓ (Σ-dec ρ)

    --
    --  Application for Dependent Frame Decorations
    --
    
    app↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {P : ℙ} {D : FrmDec X P}
      → FrmDec↓ X↓ D → (p : El P) → Frm↓ X↓ (app D p)

    app↓-⊤-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {f : Frm X}
      → (f↓ : Frm↓ X↓ f) (p : El ⊤ₚ)
      → app↓ (⊤-dec↓ f↓) p ↦ f↓
    {-# REWRITE app↓-⊤-β #-}

    app↓-⊔-inl-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U V : ℙ}
      → {l : FrmDec X U} {r : FrmDec X V}
      → (l↓ : FrmDec↓ X↓ l) (r↓ : FrmDec↓ X↓ r)
      → (u : El U)
      → app↓ (⊔-dec↓ l↓ r↓) (inlₚ V u) ↦ app↓ l↓ u
    {-# REWRITE app↓-⊔-inl-β #-}

    app↓-⊔-inr-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U V : ℙ}
      → {l : FrmDec X U} {r : FrmDec X V}
      → (l↓ : FrmDec↓ X↓ l) (r↓ : FrmDec↓ X↓ r)
      → (v : El V)
      → app↓ (⊔-dec↓ l↓ r↓) (inrₚ U v) ↦ app↓ r↓ v
    {-# REWRITE app↓-⊔-inr-β #-}

    app↓-Σ-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U : ℙ} {V : El U → ℙ}
      → {ρ : (u : El U) → FrmDec X (V u)}
      → (ρ↓ : (u : El U) → FrmDec↓ X↓ (ρ u))
      → (u : El U) (v : El (V u))
      → app↓ (Σ-dec↓ ρ↓) ⟦ U , V ∣ u , v ⟧ₚ ↦ app↓ (ρ↓ u) v
    {-# REWRITE app↓-Σ-β #-}

    --
    --  Laws for Dependent Frame Decorations
    --

    ⊔↓-unit-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {V : ℙ}
      → {l : FrmDec X ⊥ₚ} {r : FrmDec X V}
      → (l↓ : FrmDec↓ X↓ l) (r↓ : FrmDec↓ X↓ r)
      → ⊔-dec↓ l↓ r↓ ↦ r↓ 
    {-# REWRITE ⊔↓-unit-l #-}

    ⊔↓-unit-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U : ℙ}
      → {l : FrmDec X U} {r : FrmDec X ⊥ₚ}
      → (l↓ : FrmDec↓ X↓ l) (r↓ : FrmDec↓ X↓ r)
      → ⊔-dec↓ l↓ r↓ ↦ l↓ 
    {-# REWRITE ⊔↓-unit-r #-}

    ⊔↓-assoc : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U V W : ℙ}
      → {l : FrmDec X U} {m : FrmDec X V} {r : FrmDec X W}
      → (l↓ : FrmDec↓ X↓ l) (m↓ : FrmDec↓ X↓ m) (r↓ : FrmDec↓ X↓ r)
      → ⊔-dec↓ (⊔-dec↓ l↓ m↓) r↓ ↦
          ⊔-dec↓ l↓ (⊔-dec↓ m↓ r↓)
    {-# REWRITE ⊔↓-assoc #-}

    Σ↓-unit-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U : ℙ} {l : FrmDec X U}
      → (l↓ : FrmDec↓ X↓ l)
      → Σ-dec↓ (λ u → ⊤-dec↓ (app↓ l↓ u)) ↦ l↓ 
    {-# REWRITE Σ↓-unit-r #-}

    Σ↓-unit-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {V : El ⊤ₚ → ℙ}
      → {r : (t : El ⊤ₚ) → FrmDec X (V t)}
      → (r↓ : (t : El ⊤ₚ) → FrmDec↓ X↓ (r t))
      → Σ-dec↓ r↓ ↦ r↓ ttₚ
    {-# REWRITE Σ↓-unit-l #-}

    Σ↓-zero-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U : ℙ}
      → Σ-dec↓ {X↓ = X↓} {U = U} {V = λ _ → ⊥ₚ} (λ u → ⊥-dec↓) ↦ ⊥-dec↓
    {-# REWRITE Σ↓-zero-r #-} 

    Σ↓-zero-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} 
      → {X↓ : 𝕆↓ ℓ↓ X} {U : ℙ} {V : El ⊥ₚ → ℙ}
      → {r : (b : El ⊥ₚ) → FrmDec X (V b)}
      → (r↓ : (b : El ⊥ₚ) → FrmDec↓ X↓ (r b))
      → Σ-dec↓ r↓ ↦ ⊥-dec↓
    {-# REWRITE Σ↓-zero-l #-}

    Σ↓-assoc : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n}
      → {X↓ : 𝕆↓ ℓ↓ X} (U : ℙ) (V : El U → ℙ)
      → (W : El (Σₚ U V) → ℙ)
      → (w : (uv : El (Σₚ U V)) → FrmDec X (W uv))
      → (w↓ : (uv : El (Σₚ U V)) → FrmDec↓ X↓ (w uv))
      → Σ-dec↓ w↓ ↦ Σ-dec↓ (λ u → Σ-dec↓ (λ v → w↓ ⟦ U , V ∣ u , v ⟧ₚ))
    {-# REWRITE Σ↓-assoc #-}

    ⊔↓-Σ↓-distrib-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n}
      → {X↓ : 𝕆↓ ℓ↓ X} (U V : ℙ) (W : El (U ⊔ₚ V) → ℙ)
      → (w : (uv : El (U ⊔ₚ V)) → FrmDec X (W uv))
      → (w↓ : (uv : El (U ⊔ₚ V)) → FrmDec↓ X↓ (w uv))
      → Σ-dec↓ w↓ ↦ ⊔-dec↓ (Σ-dec↓ {U = U} (λ u → w↓ (inlₚ V u)))
                            (Σ-dec↓ {U = V} (λ v → w↓ (inrₚ U v)))
    {-# REWRITE ⊔↓-Σ↓-distrib-r #-} 
    
    ⊔↓-Σ↓-distrib-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → (U : ℙ) (V : El U → ℙ) (W : El U → ℙ)
      → (l : (u : El U) → FrmDec X (V u))
      → (r : (u : El U) → FrmDec X (W u))
      → (l↓ : (u : El U) → FrmDec↓ X↓ (l u))
      → (r↓ : (u : El U) → FrmDec↓ X↓ (r u))
      → Σ-dec↓ (λ u → ⊔-dec↓ (l↓ u) (r↓ u)) ↦
          ⊔-dec↓ {U = Σₚ U V} {V = Σₚ U W} (Σ-dec↓ l↓) (Σ-dec↓ r↓)
    {-# REWRITE ⊔↓-Σ↓-distrib-l #-} 

  --
  --  Dependent Constructors and Operations 
  --

  Cns↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    → {f : Frm X} {P : ℙ} {t : FrmDec X P} (c : Cns X f P t)
    → (f↓ : Frm↓ X↓ f) (t↓ : FrmDec↓ X↓ t)
    → Set ℓ↓

  
  record Opr↓ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {f : Frm X}
      (X↓ : 𝕆↓ ℓ↓ X) (f↓ : Frm↓ X↓ f) (op : Opr X f) : Set ℓ↓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫ₒₚ↓
    field
      typ↓ : FrmDec↓ X↓ (typ op) -- (p : El (pos op)) → Frm↓ X↓ (app (typ op) p)
      cns↓ : Cns↓ X↓ (cns op) f↓ typ↓ 

  open Opr↓ public

  --
  --  Higher Dependent Frames
  --

  record Frm↓ₛ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ} {X↓ₙ : 𝕆↓ ℓ↓ Xₙ}
    (X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓)
    {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    (f↓ : Frm↓ X↓ₙ f) (x↓ : X↓ₛₙ f↓ x) : Set ℓ↓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫f↓
    field
      opr↓ : Opr↓ X↓ₙ f↓ (opr fₛ)
      dec↓ : (p : El (pos (opr fₛ))) → X↓ₛₙ (app↓ (typ↓ opr↓) p) (dec fₛ p)

  open Frm↓ₛ public
      
  --
  --  Dependent Opetopic Types 
  --
  
  𝕆↓ {n = O} ℓ↓ X = X → Set ℓ↓
  𝕆↓ {n = S n} ℓ↓ (Xₙ , Xₛₙ) =
    Σ (𝕆↓ ℓ↓ Xₙ) (λ X↓ₙ →
    {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓)
  
  Frm↓ {n = O} {X} X↓ ( x , P , t ) =
    (X↓ x) × ((p : El P) → X↓ (t p))
  Frm↓ {n = S n} {Xₙ , Xₛₙ} (X↓ₙ , X↓ₛₙ) (f , x , fₛ) =
    Σ (Frm↓ X↓ₙ f) (λ f↓ →
    Σ (X↓ₛₙ f↓ x) (λ x↓ →
    Frm↓ₛ X↓ₛₙ fₛ f↓ x↓))

  --
  --  Dependent Monadic Structure
  --

  η↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm X} (f↓ : Frm↓ X↓ f)
    → Cns↓ X↓ (η-cns f) f↓ (⊤-dec↓ f↓)

  η↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm X} (f↓ : Frm↓ X↓ f)
    → Opr↓ X↓ f↓ (η f)
  η↓ f↓ = ⟪ _ , η↓-cns f↓ ⟫ₒₚ↓

  η↓-frm : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {f : Frm Xₙ} {x : Xₛₙ f}
    → (f↓ : Frm↓ X↓ₙ f) (x↓ : X↓ₛₙ f↓ x)
    → Frm↓ₛ X↓ₛₙ (η-frm f x) f↓ x↓
  η↓-frm {Xₛₙ = Xₛₙ} {X↓ₛₙ = X↓ₛₙ} {f} {x} f↓ x↓ =
    ⟪ η↓ f↓ , ⊤ₚ-elim (λ p → X↓ₛₙ (app↓ (typ↓ (η↓ f↓)) p) (dec (η-frm {Xₛₙ = Xₛₙ} f x) p)) x↓ ⟫f↓ 

  μ↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm X} {c : Opr X f}
    → {δ : (p : El (pos c)) → Opr X (app (typ c) p)}
    → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
    → (δ↓ : (p : El (pos c)) → Opr↓ X↓ (app↓ (typ↓ c↓) p) (δ p))
    → Cns↓ X↓ (μ-cns c δ ) f↓ (Σ-dec↓ (λ p → typ↓ (δ↓ p)))

  μ↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm X} {c : Opr X f}
    → {δ : (p : El (pos c)) → Opr X (app (typ c) p)}
    → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
    → (δ↓ : (p : El (pos c)) → Opr↓ X↓ (app↓ (typ↓ c↓) p) (δ p))
    → Opr↓ X↓ f↓ (μ c δ)
  μ↓ c↓ δ↓ =  ⟪ _ , μ↓-cns c↓ δ↓  ⟫ₒₚ↓ 

  μ↓-frm : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {f : Frm Xₙ} {x : Xₛₙ f} {fₛ : Frmₛ Xₛₙ f x}
    → {ϕ : (p : El (pos (opr fₛ))) → Frmₛ Xₛₙ (app (typ (opr fₛ)) p) (dec fₛ p)}
    → {f↓ : Frm↓ X↓ₙ f} {x↓ : X↓ₛₙ f↓ x} (f↓ₛ : Frm↓ₛ X↓ₛₙ fₛ f↓ x↓)
    → (ϕ↓ : (p : El (pos (opr fₛ))) → Frm↓ₛ X↓ₛₙ (ϕ p) (app↓ (typ↓ (opr↓ f↓ₛ)) p) (dec↓ f↓ₛ p))
    → Frm↓ₛ X↓ₛₙ (μ-frm fₛ ϕ) f↓ x↓
  μ↓-frm f↓ₛ ϕ↓ = ⟪ μ↓ (opr↓ f↓ₛ) (λ p → opr↓ (ϕ↓ p)) ,
    Σₚ-elim _ _ _ (λ p q → dec↓ (ϕ↓ p) q) ⟫f↓

  --
  --  Dependent Monadic Laws
  --

  postulate

    μ↓-unit-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {c : Opr X f}
      → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
      → μ↓-cns c↓ (λ p → η↓ (app↓ (typ↓ c↓) p)) ↦ cns↓ c↓
    {-# REWRITE μ↓-unit-r #-}

    μ↓-unit-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {δ : (p : El (pos (η f))) → Opr X (app (typ (η f)) p)}
      → (f↓ : Frm↓ X↓ f) (δ↓ : (p : El (pos (η f))) → Opr↓ X↓ (app↓ (typ↓ (η↓ f↓)) p) (δ p))
      → μ↓-cns (η↓ f↓) δ↓ ↦ cns↓ (δ↓ ttₚ)
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {c : Opr X f}
      → {δ : (p : El (pos c)) → Opr X (app (typ c) p)}
      → {ε : (p : El (pos (μ c δ))) → Opr X (app (typ (μ c δ)) p)}
      → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
      → (δ↓ : (p : El (pos c)) → Opr↓ X↓ (app↓ (typ↓ c↓) p) (δ p))
      → (ε↓ : (p : El (pos (μ c δ))) → Opr↓ X↓ (app↓ (typ↓ (μ↓ c↓ δ↓)) p) (ε p))
      → μ↓-cns (μ↓ c↓ δ↓) ε↓ ↦
          μ↓-cns c↓ (λ p → μ↓ (δ↓ p) (λ q → ε↓ ⟦ pos c , (λ p → pos (δ p)) ∣ p , q ⟧ₚ))
    {-# REWRITE μ↓-assoc #-}

  --
  --  Dependent constructors
  --

  Cns↓ {n = O} X↓ _ _ _ = ⊤
  Cns↓ {n = S n} (X↓ₙ , X↓ₛₙ) (lf f x) (f↓ , x↓ , ηf↓ₛ) τ =
    (ηf↓ₛ ≡ η↓-frm f↓ x↓) ×
    (τ ≡ ⊥-dec↓)
  Cns↓ {n = S n} (X↓ₙ , X↓ₛₙ) (nd x fₛₙ δ ε) (f↓ , x↓ , μf↓ₛ) τ =
    Σ (Frm↓ₛ X↓ₛₙ fₛₙ f↓ x↓) (λ f↓ₛₙ →
    Σ ((p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (app↓ (typ↓ (opr↓ f↓ₛₙ)) p) (dec↓ f↓ₛₙ p)) (λ δ↓ →
    Σ ((p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (app↓ (typ↓ (opr↓ f↓ₛₙ)) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p)) (λ ε↓ → 
    (μf↓ₛ ≡ μ↓-frm f↓ₛₙ δ↓) ×
    (τ ≡ ⊔-dec↓ (⊤-dec↓ (f↓ , x↓ , f↓ₛₙ)) (Σ-dec↓ (λ p → typ↓ (ε↓ p)))))))

  --
  --  "Smart" Constructors for leaves and nodes
  --

  lf↓ : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {f : Frm Xₙ} {x : Xₛₙ f}
    → (f↓ : Frm↓ X↓ₙ f) (x↓ : X↓ₛₙ f↓ x)
    → Cns↓ (X↓ₙ , X↓ₛₙ) (lf f x)
        (f↓ , x↓ , η↓-frm f↓ x↓) ⊥-dec↓ 
  lf↓ f↓ x↓ = refl , refl 

  nd↓ : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → {δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (dec fₛₙ p)}
    → {ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , dec fₛₙ p , δ p)}
    → {f↓ₙ : Frm↓ X↓ₙ fₙ} (x↓ : X↓ₛₙ f↓ₙ x) (f↓ₛₙ : Frm↓ₛ X↓ₛₙ fₛₙ f↓ₙ x↓)
    → (δ↓ : (p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (app↓ (typ↓ (opr↓ f↓ₛₙ)) p) (dec↓ f↓ₛₙ p))
    → (ε↓ : (p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (app↓ (typ↓ (opr↓ f↓ₛₙ)) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p))
    → Cns↓ (X↓ₙ , X↓ₛₙ) (nd x fₛₙ δ ε) (f↓ₙ , x↓ , μ↓-frm f↓ₛₙ δ↓)
        (⊔-dec↓ (⊤-dec↓ (f↓ₙ , x↓ , f↓ₛₙ)) (Σ-dec↓ (λ p → typ↓ (ε↓ p)))) 
  nd↓ x↓ f↓ₛₙ δ↓ ε↓ = f↓ₛₙ , δ↓ , ε↓ , refl , refl

  --
  --  Dependent Grafting
  --

  γ↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → {c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ)}
    → {δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (dec fₛₙ p)}
    → {ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , dec fₛₙ p , δ p)}
    → {f↓ₙ : Frm↓ X↓ₙ fₙ} {x↓ : X↓ₛₙ f↓ₙ x} {f↓ₛₙ : Frm↓ₛ X↓ₛₙ fₛₙ f↓ₙ x↓}
    → (c↓ : Opr↓ (X↓ₙ , X↓ₛₙ) (f↓ₙ , x↓ , f↓ₛₙ) c)
    → (δ↓ : (p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (app↓ (typ↓ (opr↓ f↓ₛₙ)) p) (dec↓ f↓ₛₙ p))
    → (ε↓ : (p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (app↓ (typ↓ (opr↓ f↓ₛₙ)) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p))
    → Cns↓ (X↓ₙ , X↓ₛₙ) (γ-cns c δ ε) (f↓ₙ , x↓ , μ↓-frm f↓ₛₙ δ↓)
        (⊔-dec↓ (typ↓ c↓) (Σ-dec↓ (λ p → typ↓ (ε↓ p)))) 

  --
  --  Dependent Monadic Implementation
  --

  η↓-cns {n = O} f↓ = tt
  η↓-cns {n = S n} (f↓ , x↓ , μf↓ₛ) =
    nd↓ x↓ μf↓ₛ
      (λ p → η↓-frm (app↓ (typ↓ (opr↓ μf↓ₛ)) p) (dec↓ μf↓ₛ p))
      (λ p → ⟪ _ , lf↓ (app↓ (typ↓ (opr↓ μf↓ₛ)) p) (dec↓ μf↓ₛ p) ⟫ₒₚ↓)

  μ↓-cns {n = O} _ _ = tt
  μ↓-cns {n = S n} {c = ⟪ _ , _ , lf f x ⟫ₒₚ} {f↓ = f↓ₙ , x↓ , ._} ⟪ _ , (refl , refl) ⟫ₒₚ↓ κ↓ = lf↓ f↓ₙ x↓ 
  μ↓-cns {n = S n} {c = ⟪ _ , _ , nd x fₛₙ δ ε ⟫ₒₚ} {f↓ = f↓ₙ , x↓ , ._} ⟪ _ , (f↓ₛₙ , δ↓ , ε↓ , refl , refl) ⟫ₒₚ↓ κ↓ =
    let w↓ = κ↓ (inlₚ (Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p))) ttₚ)
        κ↓' p q = κ↓ (inrₚ ⊤ₚ ⟦ pos (opr fₛₙ) , (λ p₁ → pos (ε p₁)) ∣ p , q ⟧ₚ)
        ϕ↓ p = μ↓ (ε↓ p) (κ↓' p)
    in γ↓-cns w↓ δ↓ ϕ↓ 

  γ↓-cns {c = ⟪ _ , _ , lf _ _ ⟫ₒₚ} ⟪ _ , (refl , refl) ⟫ₒₚ↓ ϕ↓ ψ↓ = cns↓ (ψ↓ ttₚ)
  γ↓-cns {c = ⟪ _ , _ , nd x fₛₙ δ ε ⟫ₒₚ} {x↓ = x↓} ⟪ _ , (f↓ₛₙ , δ↓ , ε↓ , refl , refl) ⟫ₒₚ↓ ϕ↓ ψ↓ =
    let ϕ↓' p q = ϕ↓ ⟦ pos (opr fₛₙ) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
        ψ↓' p q = ψ↓ ⟦ pos (opr fₛₙ) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
        δ↓' p = μ↓-frm (δ↓ p) (ϕ↓' p)
        ε↓' p = ⟪ _ , γ↓-cns (ε↓ p) (ϕ↓' p) (ψ↓' p) ⟫ₒₚ↓
    in nd↓ x↓ f↓ₛₙ δ↓' ε↓'

  --
  --  Dependent Opetopic Types
  --

  record 𝕆↓∞ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X∞ : 𝕆∞ X) (X↓ : 𝕆↓ ℓ↓ X)  : Set (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ↓)) where
    coinductive
    field
      Head↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) (x : Head X∞ f) → Set ℓ↓
      Tail↓ : 𝕆↓∞ (Tail X∞) (X↓ , Head↓)

  open 𝕆↓∞ public 


