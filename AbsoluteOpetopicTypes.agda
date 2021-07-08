{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import MiniUniverse

module AbsoluteOpetopicTypes where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ
  
  data FrmDec {ℓ} {n : ℕ} (X : 𝕆 ℓ n) : ℙ → Set ℓ
  FrmDec↓ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → (X↓ : Frm X → Set ℓ)
    → {P : ℙ} (D : FrmDec X P)
    → Set ℓ 

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

  Frmₛ : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} (Xₛₙ : Frm Xₙ → Set ℓ) (f : Frm Xₙ) (x : Xₛₙ f) → Set ℓ
  Frmₛ {Xₙ = Xₙ} Xₛₙ f x = Σ (Opr Xₙ f) (λ o → FrmDec↓ Xₛₙ (typₒ o))

  opr = fst
  dec = snd
  
  --
  --  Opetopic Types and Frames
  --
  
  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ X → (f : Frm X) → Set ℓ)

  Frm {n = O} X = Arity X -- probably don't want to do this now ...
  Frm {n = S n} (Xₙ , Xₛₙ) = Σ (Frm Xₙ) (λ f → Σ (Xₛₙ f) (λ x → Frmₛ Xₛₙ f x))

  data FrmDec {ℓ} {n} X where
    null : FrmDec X ⊥ₚ
    term : Frm X → FrmDec X ⊤ₚ
    plus : {U V : ℙ} → FrmDec X U → FrmDec X V
      → FrmDec X (U ⊔ₚ V)
    times : {U : ℙ} {V : El U → ℙ}
      → (ρ : (u : El U) → FrmDec X (V u))
      → FrmDec X (Σₚ U V)

  postulate
  
    app : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {P : ℙ}
      → FrmDec X P → El P → Frm X
  
    app↓ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {X↓ : Frm X → Set ℓ} {P : ℙ}
      → {D : FrmDec X P}
      → FrmDec↓ X↓ D → (p : El P) → X↓ (app D p)

  FrmDec↓ X↓ null = ⊤
  FrmDec↓ X↓ (term x) = X↓ x
  FrmDec↓ X↓ (plus DU DV) =
    FrmDec↓ X↓ DU × FrmDec↓ X↓ DV
  FrmDec↓ X↓ (times {U} ρ) =
    (u : El U) → FrmDec↓ X↓ (ρ u)

  --
  --  Monadic Structure
  --

  postulate
  
    η-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
      → Cns X f ⊤ₚ (term f)

  η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X) → Opr X f
  η f = (_ , _ , η-cns f)

  η-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → (f : Frm Xₙ) (x : Xₛₙ f)
    → Frmₛ Xₛₙ f x 
  η-frm {Xₛₙ = Xₛₙ} f x = η f , x 

  postulate
  
    μ-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {f : Frm X} (c : Opr X f)
      → (δ : (p : El (posₒ c)) → Opr X (app (typₒ c) p))
      → Cns X f (Σₚ (posₒ c) (λ p → posₒ (δ p)))
                (times (λ p → typₒ (δ p)))

  μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (posₒ c)) → Opr X (app (typₒ c) p))
    → Opr X f
  μ c δ = (_ , _ , μ-cns c δ)

  μ-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    → (ϕ : (p : El (posₒ (opr fₛ))) → Frmₛ Xₛₙ (app (typₒ (opr fₛ)) p) (app↓ {D = typₒ (opr fₛ)} (dec fₛ) p))
    → Frmₛ Xₛₙ f x
  μ-frm fₛ ϕ = μ (opr fₛ) (λ p → opr (ϕ p)) , λ p → dec (ϕ p) 
    
  --
  --  Monadic Laws
  --

  -- postulate

  --   μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
  --     → {f : Frm X} (c : Opr X f)
  --     → μ-cns c (λ p → η (typₒ c p)) ↦ cns c
  --   {-# REWRITE μ-unit-r #-}

  --   μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
  --     → (f : Frm X) (δ : (p : El (posₒ (η f))) → Opr X (typₒ (η f) p))
  --     → μ-cns (η f) δ ↦ cns (δ ttₚ)
  --   {-# REWRITE μ-unit-l #-}

  --   μ-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
  --     → {f : Frm X} (c : Opr X f)
  --     → (δ : (p : El (posₒ c)) → Opr X (typₒ c p))
  --     → (ε : (p : El (posₒ (μ c δ))) → Opr X (typₒ (μ c δ) p))
  --     → μ-cns (μ c δ) ε ↦ μ-cns c (λ p → μ (δ p)
  --         (λ q → ε ⟦ posₒ c , (λ p → posₒ (δ p)) ∣ p , q ⟧ₚ))  
  --   {-# REWRITE μ-assoc #-}

  --
  --  The slice construction
  --

  data Tree {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ) :
    (f : Frm (Xₙ , Xₛₙ)) (P : ℙ) (D : FrmDec (Xₙ , Xₛₙ) P) → Set ℓ where 

    lf : (f : Frm Xₙ) (x : Xₛₙ f)
      → Tree Xₙ Xₛₙ (f , x , η-frm f x) ⊥ₚ null

    nd : {fₙ : Frm Xₙ} (x : Xₛₙ fₙ) (fₛₙ : Frmₛ Xₛₙ fₙ x)
      → (δ : (p : El (posₒ (opr fₛₙ))) → Frmₛ Xₛₙ (app (typₒ (opr fₛₙ)) p) (app↓ {D = typₒ (opr fₛₙ)} (dec fₛₙ) p))
      → (ε : (p : El (posₒ (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typₒ (opr fₛₙ)) p , app↓ {D = typₒ (opr fₛₙ)} (dec fₛₙ) p , δ p))
      → Tree Xₙ Xₛₙ (fₙ , x , μ-frm {x = x} fₛₙ δ) 
          (⊤ₚ ⊔ₚ Σₚ (posₒ (opr fₛₙ)) (λ p → posₒ (ε p)))
          (plus (term (fₙ , x , fₛₙ))
                (times λ p → typₒ (ε p))) 

  Cns {n = O} X _ _ _ = ⊤
  Cns {n = S n} (Xₙ , Xₛₙ) = Tree Xₙ Xₛₙ 

  --
  --  Grafting of trees
  --
  
  -- γ-cns : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
  --   → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
  --   → (c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ))
  --   → (δ : (p : El (posₒ (opr fₛₙ))) → Frmₛ Xₛₙ (typₒ (opr fₛₙ) p) (dec fₛₙ p))
  --   → (ε : (p : El (posₒ (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (typₒ (opr fₛₙ) p , dec fₛₙ p , δ p))
  --   → Cns (Xₙ , Xₛₙ) (fₙ , x , μ-frm fₛₙ δ)
  --       (posₒ c ⊔ₚ Σₚ (posₒ (opr fₛₙ)) (λ p → posₒ (ε p)))
  --       (⊔ₚ-Frm-rec (typₒ c) (Σₚ-Frm-rec (λ p q → typₒ (ε p) q)))

  -- -- Missing still: right unit (left is definitional), associativity
  -- -- and distributivity of γ ....

  -- --
  -- --  Monadic implementations
  -- --

  -- η-cns {n = O} f = tt
  -- η-cns {n = S n} (fₙ , x , fₛₙ) = 
  --   nd x fₛₙ (λ p → η-frm (typₒ (opr fₛₙ) p) (dec fₛₙ p))
  --           (λ p → ⟪ _ , _ , lf (typₒ (opr fₛₙ) p) (dec fₛₙ p) ⟫ₒₚ)

  -- μ-cns {n = O} _ _ = tt
  -- μ-cns {n = S n} ⟪ _ , _ , lf f x ⟫ₒₚ κ = lf f x
  -- μ-cns {n = S n} {X = Xₙ , Xₛₙ} ⟪ _ , _ , nd {fₙ} x fₛₙ δ ε ⟫ₒₚ κ = 
  --   let w = κ (inlₚ (Σₚ (posₒ (opr fₛₙ)) (λ p₁ → posₒ (ε p₁))) ttₚ)
  --       κ' p q = κ (inrₚ ⊤ₚ ⟦ posₒ (opr fₛₙ) , (λ p₁ → posₒ (ε p₁)) ∣ p , q ⟧ₚ) 
  --       ϕ p = μ (ε p) (κ' p) 
  --   in γ-cns w δ ϕ

  -- γ-cns ⟪ _ , _ , lf f x ⟫ₒₚ δ ε = cns (ε ttₚ)
  -- γ-cns {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} ⟪ _ , _ , nd {fₙ} x c δ ε ⟫ₒₚ ϕ ψ =
  --   let ϕ' p q = ϕ ⟦ posₒ (opr c) , (λ p' → posₒ (opr (δ p'))) ∣ p , q ⟧ₚ
  --       ψ' p q = ψ ⟦ posₒ (opr c) , (λ p' → posₒ (opr (δ p'))) ∣ p , q ⟧ₚ
  --       δ' p = μ-frm (δ p) (ϕ' p)
  --       ε' p = ⟪ _ , _ , γ-cns (ε p) (ϕ' p) (ψ' p) ⟫ₒₚ
  --   in nd x c δ' ε'

  -- --
  -- --  Opetopic Types
  -- --

  -- record 𝕆∞ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) : Set (ℓ-suc ℓ) where
  --   coinductive
  --   field
  --     Head : Frm X → Set ℓ
  --     Tail : 𝕆∞ {ℓ} {S n} (X , Head)

  -- open 𝕆∞ public 
