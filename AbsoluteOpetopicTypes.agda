{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse

-- Typechecking seems to take a lot longer now that we have
-- removed the inductive records for Opr and Frm, etc.
-- should we put them back? 
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

  Opr : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (f : Frm X) → Set ℓ
  Opr X f = Σ ℙ (λ pos → Σ (FrmDec X pos) (λ typ → Cns X f pos typ))

  posₒ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {f : Frm X}
    → Opr X f → ℙ
  posₒ (pos , _ , _) = pos

  typₒ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {f : Frm X}
    → (op : Opr X f) → FrmDec X (posₒ op)
  typₒ (_ , typ , _) = typ
  
  --
  --  Higher Frames
  --

  Frmₛ : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} (Xₛₙ : Frm Xₙ → Set ℓ)
    → (f : Frm Xₙ) (x : Xₛₙ f) → Set ℓ
  Frmₛ {Xₙ = Xₙ} Xₛₙ f x =
    Σ (Opr Xₙ f) (λ o →
    Π (El (posₒ o)) (λ p →
      Xₛₙ (app (typₒ o) p)))

  opr = fst
  dec = snd
  
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
  η f = (_ , _ , η-cns f)

  η-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → (f : Frm Xₙ) (x : Xₛₙ f)
    → Frmₛ Xₛₙ f x 
  η-frm {Xₛₙ = Xₛₙ} f x = η f , ⊤ₚ-elim (λ p → Xₛₙ (app (typₒ (η f)) p)) x 

  μ-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (posₒ c)) → Opr X (app (typₒ c) p))
    → Cns X f (Σₚ (posₒ c) (λ p → posₒ (δ p)))
              (Σ-dec (λ p → typₒ (δ p)))

  μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (posₒ c)) → Opr X (app (typₒ c) p))
    → Opr X f
  μ c δ = (_ , _ , μ-cns c δ)

  μ-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    → (ϕ : (p : El (posₒ (opr fₛ))) → Frmₛ Xₛₙ (app (typₒ (opr fₛ)) p) (dec fₛ p)) 
    → Frmₛ Xₛₙ f x
  μ-frm fₛ ϕ = μ (opr fₛ) (λ p → opr (ϕ p)) , Σₚ-elim _ _ _ (λ p q → dec (ϕ p) q) 
    
  --
  --  Monadic Laws
  --

  postulate

    μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → μ-cns c (λ p → η (app (typₒ c) p)) ↦ snd (snd c)
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (f : Frm X) (δ : (p : El (posₒ (η f))) → Opr X (app (typₒ (η f)) p))
      → μ-cns (η f) δ ↦ snd (snd (δ ttₚ))
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → (δ : (p : El (posₒ c)) → Opr X (app (typₒ c) p))
      → (ε : (p : El (posₒ (μ c δ))) → Opr X (app (typₒ (μ c δ)) p))
      → μ-cns (μ c δ) ε ↦ μ-cns c (λ p → μ (δ p)
          (λ q → ε ⟦ posₒ c , (λ p → posₒ (δ p)) ∣ p , q ⟧ₚ))
    {-# REWRITE μ-assoc #-}

  --
  --  The slice construction
  --

  data Tree {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ) :
    (f : Frm (Xₙ , Xₛₙ)) (P : ℙ) (D : FrmDec (Xₙ , Xₛₙ) P) → Set ℓ where 

    lf : (f : Frm Xₙ) (x : Xₛₙ f)
      → Tree Xₙ Xₛₙ (f , x , η-frm {Xₛₙ = Xₛₙ} f x) ⊥ₚ ⊥-dec

    nd : {fₙ : Frm Xₙ} (x : Xₛₙ fₙ) (fₛₙ : Frmₛ Xₛₙ fₙ x)
      → (δ : (p : El (posₒ (opr fₛₙ))) → Frmₛ Xₛₙ (app (typₒ (opr fₛₙ)) p) (dec fₛₙ p))
      → (ε : (p : El (posₒ (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typₒ (opr fₛₙ)) p , dec fₛₙ p , δ p)) 
      → Tree Xₙ Xₛₙ (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ) 
          (⊤ₚ ⊔ₚ Σₚ (posₒ (opr fₛₙ)) (λ p → posₒ (ε p)))
          (⊔-dec (⊤-dec (fₙ , x , fₛₙ))
                 (Σ-dec (λ p → typₒ (ε p)))) 

  Cns {n = O} X _ _ _ = ⊤
  Cns {n = S n} (Xₙ , Xₛₙ) = Tree Xₙ Xₛₙ 

  --
  --  Grafting of trees
  --

  γ-cns : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → (c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ))
    → (δ : (p : El (posₒ (opr fₛₙ))) → Frmₛ Xₛₙ (app (typₒ (opr fₛₙ)) p) (dec fₛₙ p))
    → (ε : (p : El (posₒ (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typₒ (opr fₛₙ)) p , dec fₛₙ p , δ p))
    → Cns (Xₙ , Xₛₙ) (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ)
        (posₒ c ⊔ₚ Σₚ (posₒ (opr fₛₙ)) (λ p → posₒ (ε p)))
        (⊔-dec (typₒ c) (Σ-dec (λ p → typₒ (ε p)))) 

  -- Missing still: right unit (left is definitional), associativity
  -- and distributivity of γ ....

  --
  --  Monadic implementations
  --

  η-cns {n = O} f = tt
  η-cns {n = S n} {X = Xₙ , Xₛₙ} (fₙ , x , fₛₙ) = 
    nd x fₛₙ (λ p → η-frm {Xₛₙ = Xₛₙ} (app (typₒ (opr fₛₙ)) p) (dec fₛₙ p))
            (λ p → (_ , _ , lf (app (typₒ (opr fₛₙ)) p) (dec fₛₙ p)))

  μ-cns {n = O} _ _ = tt
  μ-cns {n = S n} (_ , _ , lf f x) κ = lf f x
  μ-cns {n = S n} {X = Xₙ , Xₛₙ} (_ , _ , nd {fₙ} x fₛₙ δ ε) κ = 
    let w = κ (inlₚ (Σₚ (posₒ (opr fₛₙ)) (λ p₁ → posₒ (ε p₁))) ttₚ)
        κ' p q = κ (inrₚ ⊤ₚ ⟦ posₒ (opr fₛₙ) , (λ p₁ → posₒ (ε p₁)) ∣ p , q ⟧ₚ) 
        ϕ p = μ (ε p) (κ' p) 
    in γ-cns w δ ϕ

  γ-cns (_ , _ , lf f x) δ ε = snd (snd (ε ttₚ))
  γ-cns {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} (_ , _ , nd {fₙ} x c δ ε) ϕ ψ =
    let ϕ' p q = ϕ ⟦ posₒ (opr c) , (λ p' → posₒ (opr (δ p'))) ∣ p , q ⟧ₚ
        ψ' p q = ψ ⟦ posₒ (opr c) , (λ p' → posₒ (opr (δ p'))) ∣ p , q ⟧ₚ
        δ' p = μ-frm {Xₛₙ = Xₛₙ} {x = dec c p} (δ p) (ϕ' p)
        ε' p = (_ , _ , γ-cns (ε p) (ϕ' p) (ψ' p))
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
