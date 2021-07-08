{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse

module AbsoluteOpetopicTypes where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ

  postulate

    -- 
    -- Decorations of frames
    --
    
    FrmDec : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) → ℙ → Set ℓ
    
    ⊥-dec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → FrmDec X ⊥ₚ
  
    ⊤-dec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → Frm X → FrmDec X ⊤ₚ

    ⊔-dec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {U V : ℙ}
      → FrmDec X U → FrmDec X V
      → FrmDec X (U ⊔ₚ V)
      
    Σ-dec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {U : ℙ} {V : El U → ℙ}
      → (ρ : (u : El U) → FrmDec X (V u))
      → FrmDec X (Σₚ U V)

    --
    -- Application for decorations
    --
    
    app : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {P : ℙ}
      → FrmDec X P → El P → Frm X

    app-⊤-dec-β : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {P : ℙ}
      → (f : Frm X) (p : El ⊤ₚ)
      → app (⊤-dec f) p ↦ f
    {-# REWRITE app-⊤-dec-β #-}
      
    app-⊔-dec-l-β : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {P : ℙ}
      → {U V : ℙ} (DU : FrmDec X U) (DV : FrmDec X V)
      → (u : El U)
      → app (⊔-dec DU DV) (inlₚ V u) ↦ app DU u 
    {-# REWRITE app-⊔-dec-l-β #-}

    app-⊔-dec-r-β : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {P : ℙ}
      → {U V : ℙ} (DU : FrmDec X U) (DV : FrmDec X V)
      → (v : El V)
      → app (⊔-dec DU DV) (inrₚ U v) ↦ app DV v 
    {-# REWRITE app-⊔-dec-r-β #-}

    app-Σ-dec-β : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {U : ℙ} {V : El U → ℙ}
      → (ρ : (u : El U) → FrmDec X (V u))
      → (u : El U) (v : El (V u))
      → app (Σ-dec ρ) ⟦ U , V ∣ u , v ⟧ₚ ↦ app (ρ u) v
    {-# REWRITE app-Σ-dec-β #-}

    --
    -- Laws for decorations
    --
    
    ⊔-dec-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (V : ℙ) (DV : FrmDec X V)
      → (D⊥ : FrmDec X ⊥ₚ)
      → ⊔-dec D⊥ DV ↦ DV
    {-# REWRITE ⊔-dec-unit-l #-}

    ⊔-dec-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U : ℙ) (DU : FrmDec X U)
      → (D⊥ : FrmDec X ⊥ₚ)
      → ⊔-dec DU D⊥ ↦ DU
    {-# REWRITE ⊔-dec-unit-r #-}

    ⊔-dec-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U V W : ℙ)(DU : FrmDec X U)
      → (DV : FrmDec X V) (DW : FrmDec X W)
      → ⊔-dec (⊔-dec DU DV) DW ↦
        ⊔-dec DU (⊔-dec DV DW)
    {-# REWRITE ⊔-dec-assoc #-}

    Σ-dec-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U : ℙ) (UD : FrmDec X U)
      → Σ-dec (λ u → ⊤-dec (app UD u)) ↦ UD
    {-# REWRITE Σ-dec-unit-r #-}

    Σ-dec-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (V : El ⊤ₚ → ℙ) (DV : (t : El ⊤ₚ) → FrmDec X (V t))
      → Σ-dec DV ↦ DV ttₚ
    {-# REWRITE Σ-dec-unit-l #-}

    Σ-dec-zero-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (U : ℙ) 
      → Σ-dec {X = X} {U = U} {V = λ _ → ⊥ₚ} (λ u → ⊥-dec) ↦ ⊥-dec
    {-# REWRITE Σ-dec-zero-r #-}

    Σ-dec-zero-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (V : El ⊥ₚ → ℙ)
      → (DV : (b : El ⊥ₚ) → FrmDec X (V b))
      → Σ-dec DV ↦ ⊥-dec
    {-# REWRITE Σ-dec-zero-l #-}
    
    Σ-dec-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U : ℙ) (V : El U → ℙ)
      → (W : El (Σₚ U V) → ℙ)
      → (DW : (uv : El (Σₚ U V)) → FrmDec X (W uv))
      → Σ-dec DW ↦ Σ-dec (λ u → Σ-dec (λ v → DW ⟦ U , V ∣ u , v ⟧ₚ)) 
    {-# REWRITE Σ-dec-assoc #-}

    ⊔-Σ-dec-distrib-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U V : ℙ) (W : El (U ⊔ₚ V) → ℙ)
      → (DW : (uv : El (U ⊔ₚ V)) → FrmDec X (W uv))
      → Σ-dec DW ↦ ⊔-dec (Σ-dec {U = U} (λ u → DW (inlₚ V u)))
                          (Σ-dec {U = V} (λ v → DW (inrₚ U v))) 
    {-# REWRITE ⊔-Σ-dec-distrib-r #-}

    ⊔-Σ-dec-distrib-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U : ℙ) (V : El U → ℙ) (W : El U → ℙ)
      → (DV : (u : El U) → FrmDec X (V u))
      → (DW : (u : El U) → FrmDec X (W u))
      → Σ-dec (λ u → ⊔-dec (DV u) (DW u)) ↦
          ⊔-dec {U = Σₚ U V} {V = Σₚ U W} (Σ-dec DV) (Σ-dec DW)
    {-# REWRITE ⊔-Σ-dec-distrib-l #-} 

  --
  --  Constructors and Operations
  --

  Cns : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
    → (f : Frm X) (P : ℙ) (t : FrmDec X P)
    → Set ℓ

  record Opr {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (f : Frm X) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_,_⟫ₒₚ
    field
      pos : ℙ
      typ : FrmDec X pos
      cns : Cns X f pos typ

  open Opr public
  
  --
  --  Higher Frames
  --

  record Frmₛ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} (Xₛₙ : Frm Xₙ → Set ℓ) (f : Frm Xₙ) (x : Xₛₙ f) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫f
    field
      opr : Opr Xₙ f
      dec : (p : El (pos opr)) → Xₛₙ (app (typ opr) p)

  open Frmₛ public
  
  --
  --  Opetopic Types and Frames 
  --
  
  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ X → (f : Frm X) → Set ℓ)

  Frm {n = O} X = Σ X (λ x → Σ ℙ (λ P → Π (El P) (λ _ → X)))
  Frm {n = S n} (Xₙ , Xₛₙ) = Σ (Frm Xₙ) (λ f → Σ (Xₛₙ f) (λ x → Frmₛ Xₛₙ f x))

  --
  --  Monadic Signature
  --

  η-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
    → Cns X f ⊤ₚ (⊤-dec f)

  η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X) → Opr X f
  η f = ⟪ _ , _ , η-cns f ⟫ₒₚ

  η-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → (f : Frm Xₙ) (x : Xₛₙ f)
    → Frmₛ Xₛₙ f x 
  η-frm {Xₛₙ = Xₛₙ} f x = ⟪ η f , ⊤ₚ-elim (λ p → Xₛₙ (app (typ (η f)) p)) x ⟫f

  μ-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (pos c)) → Opr X (app (typ c) p))
    → Cns X f (Σₚ (pos c) (λ p → pos (δ p)))
              (Σ-dec (λ p → typ (δ p)))

  μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (pos c)) → Opr X (app (typ c) p))
    → Opr X f
  μ c δ = ⟪ _ , _ , μ-cns c δ ⟫ₒₚ

  μ-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    → (ϕ : (p : El (pos (opr fₛ))) → Frmₛ Xₛₙ (app (typ (opr fₛ)) p) (dec fₛ p)) 
    → Frmₛ Xₛₙ f x
  μ-frm fₛ ϕ = ⟪ μ (opr fₛ) (λ p → opr (ϕ p)) , Σₚ-elim _ _ _ (λ p q → dec (ϕ p) q) ⟫f
    
  --
  --  Monadic Laws
  --

  postulate

    μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → μ-cns c (λ p → η (app (typ c) p)) ↦ cns c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (f : Frm X) (δ : (p : El (pos (η f))) → Opr X (app (typ (η f)) p))
      → μ-cns (η f) δ ↦ cns (δ ttₚ)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → (δ : (p : El (pos c)) → Opr X (app (typ c) p))
      → (ε : (p : El (pos (μ c δ))) → Opr X (app (typ (μ c δ)) p))
      → μ-cns (μ c δ) ε ↦ μ-cns c (λ p → μ (δ p)
          (λ q → ε ⟦ pos c , (λ p → pos (δ p)) ∣ p , q ⟧ₚ))
    {-# REWRITE μ-assoc #-}

  --
  --  The slice construction
  --

  data Tree {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ) :
    (f : Frm (Xₙ , Xₛₙ)) (P : ℙ) (D : FrmDec (Xₙ , Xₛₙ) P) → Set ℓ where 

    lf : (f : Frm Xₙ) (x : Xₛₙ f)
      → Tree Xₙ Xₛₙ (f , x , η-frm {Xₛₙ = Xₛₙ} f x) ⊥ₚ ⊥-dec

    nd : {fₙ : Frm Xₙ} (x : Xₛₙ fₙ) (fₛₙ : Frmₛ Xₛₙ fₙ x)
      → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
      → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , dec fₛₙ p , δ p)) 
      → Tree Xₙ Xₛₙ (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ) 
          (⊤ₚ ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p)))
          (⊔-dec (⊤-dec (fₙ , x , fₛₙ))
                 (Σ-dec (λ p → typ (ε p)))) 

  Cns {n = O} X _ _ _ = ⊤
  Cns {n = S n} (Xₙ , Xₛₙ) = Tree Xₙ Xₛₙ 

  --
  --  Grafting of trees
  --

  γ-cns : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → (c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ))
    → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
    → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , dec fₛₙ p , δ p))
    → Cns (Xₙ , Xₛₙ) (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ)
        (pos c ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p)))
        (⊔-dec (typ c) (Σ-dec (λ p → typ (ε p)))) 

  -- Missing still: right unit (left is definitional), associativity
  -- and distributivity of γ ....

  --
  --  Monadic implementations
  --

  η-cns {n = O} f = tt
  η-cns {n = S n} {X = Xₙ , Xₛₙ} (fₙ , x , fₛₙ) = 
    nd x fₛₙ (λ p → η-frm {Xₛₙ = Xₛₙ} (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
            (λ p → ⟪ _ , _ , lf (app (typ (opr fₛₙ)) p) (dec fₛₙ p) ⟫ₒₚ)

  μ-cns {n = O} _ _ = tt
  μ-cns {n = S n} ⟪ _ , _ , lf f x ⟫ₒₚ κ = lf f x
  μ-cns {n = S n} {X = Xₙ , Xₛₙ} ⟪ _ , _ , nd {fₙ} x fₛₙ δ ε ⟫ₒₚ κ = 
    let w = κ (inlₚ (Σₚ (pos (opr fₛₙ)) (λ p₁ → pos (ε p₁))) ttₚ)
        κ' p q = κ (inrₚ ⊤ₚ ⟦ pos (opr fₛₙ) , (λ p₁ → pos (ε p₁)) ∣ p , q ⟧ₚ) 
        ϕ p = μ (ε p) (κ' p) 
    in γ-cns w δ ϕ

  γ-cns ⟪ _ , _ , lf f x ⟫ₒₚ δ ε = cns (ε ttₚ)
  γ-cns {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} ⟪ _ , _ , nd {fₙ} x c δ ε ⟫ₒₚ ϕ ψ =
    let ϕ' p q = ϕ ⟦ pos (opr c) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
        ψ' p q = ψ ⟦ pos (opr c) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
        δ' p = μ-frm {Xₛₙ = Xₛₙ} {x = dec c p} (δ p) (ϕ' p)
        ε' p = ⟪ _ , _ , γ-cns (ε p) (ϕ' p) (ψ' p) ⟫ₒₚ
    in nd x c δ' ε'

  --
  --  Opetopic Types
  --

  record 𝕆∞ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) : Set (ℓ-suc ℓ) where
    coinductive
    field
      Head : Frm X → Set ℓ
      Tail : 𝕆∞ {ℓ} {S n} (X , Head)

  open 𝕆∞ public 
