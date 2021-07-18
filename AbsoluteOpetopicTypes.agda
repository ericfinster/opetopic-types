{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import MiniHoTT
open import PositionUniverse

module AbsoluteOpetopicTypes where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ

  --
  --  Constructors and Operations
  --

  data Web {ℓ} {n : ℕ} (X : 𝕆 ℓ n) :
    (f : Frm X) (P : ℙ) (t : πₚ P (cst (Frm X))) → Set ℓ

  record Opr {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (f : Frm X) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_,_⟫ₒₚ
    field
      pos : ℙ
      typ : πₚ pos (cst (Frm X))
      web : Web X f pos typ

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
      dec : πₚ (pos opr) (λ p → Xₛₙ (app (typ opr) p))

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

  postulate
  
    η-web : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
      → Web X f ⊤ₚ (π-⊤ _ f)

  η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X) → Opr X f
  η f = ⟪ _ , _ , η-web f ⟫ₒₚ

  η-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → (f : Frm Xₙ) (x : Xₛₙ f)
    → Frmₛ Xₛₙ f x 
  η-frm {Xₛₙ = Xₛₙ} f x = ⟪ η f , π-⊤ _ x ⟫f 

  postulate

    μ-web : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {f : Frm X} (c : Opr X f)
      → (δ : πₚ (pos c) (λ p → Opr X (app (typ c) p)))
      → Web X f (Σₚ (pos c) (lam (pos c) (λ p → pos (app δ p))))
                (π-Σ (pos c) (lam (pos c) (λ p → pos (app δ p))) (cst (Frm X))
                  (lam (pos c) (λ p → typ (app δ p)))) 

  μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : πₚ (pos c) (λ p → Opr X (app (typ c) p)))
    → Opr X f
  μ c δ = ⟪ _ , _ , μ-web c δ ⟫ₒₚ

  μ-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    → (ϕ : πₚ (pos (opr fₛ)) (λ p → Frmₛ Xₛₙ (app (typ (opr fₛ)) p) (app (dec fₛ) p)))
    → Frmₛ Xₛₙ f x
  μ-frm fₛ ϕ = ⟪ μ (opr fₛ) (lam (pos (opr fₛ)) (λ p → opr (app ϕ p))) ,
                π-Σ (pos (opr fₛ)) (lam (pos (opr fₛ)) (λ p → pos (opr (app ϕ p)))) _
                (lam (pos (opr fₛ)) (λ p → lam (pos (opr (app ϕ p))) (λ q → app (dec (app ϕ p)) q))) ⟫f
    
  --
  --  Monadic Laws
  --

  postulate

    μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → μ-web c (lam (pos c) (λ p → η (app (typ c) p))) ↦ web c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (f : Frm X) (δ : πₚ ⊤ₚ (λ p → Opr X (app (typ (η f)) p)))
      → μ-web (η f) δ ↦ web (app δ ttₚ)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → (δ : πₚ (pos c) (λ p → Opr X (app (typ c) p)))
      → (ε : πₚ (pos (μ c δ)) (λ p → Opr X (app (typ (μ c δ)) p)))
      → μ-web (μ c δ) ε ↦ μ-web c (lam (pos c)
          (λ p → μ (app δ p) (lam (pos (app δ p))
          (λ q → app ε ⟦ pos c , lam (pos c) (λ p → pos (app δ p)) ∣ p , q ⟧ₚ))))
    {-# REWRITE μ-assoc #-}

  --
  --  The slice construction
  --

  data Web {ℓ} {n} X where
  
  -- data Tree {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ) :
  --   (f : Frm (Xₙ , Xₛₙ)) (P : ℙ) (D : FrmDec (Xₙ , Xₛₙ) P) → Set ℓ where 

  --   lf : (f : Frm Xₙ) (x : Xₛₙ f)
  --     → Tree Xₙ Xₛₙ (f , x , η-frm {Xₛₙ = Xₛₙ} f x) ⊥ₚ ⊥-dec

  --   nd : {fₙ : Frm Xₙ} (x : Xₛₙ fₙ) (fₛₙ : Frmₛ Xₛₙ fₙ x)
  --     → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
  --     → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , dec fₛₙ p , δ p)) 
  --     → Tree Xₙ Xₛₙ (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ) 
  --         (⊤ₚ ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p)))
  --         (⊔-dec (⊤-dec (fₙ , x , fₛₙ))
  --                (Σ-dec (λ p → typ (ε p)))) 

  -- Cns {n = O} X _ _ _ = ⊤
  -- Cns {n = S n} (Xₙ , Xₛₙ) = Tree Xₙ Xₛₙ 

  --
  --  Grafting of trees
  --

  -- γ-cns : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
  --   → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
  --   → (c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ))
  --   → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
  --   → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , dec fₛₙ p , δ p))
  --   → Cns (Xₙ , Xₛₙ) (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ)
  --       (pos c ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p)))
  --       (⊔-dec (typ c) (Σ-dec (λ p → typ (ε p)))) 

  -- Missing still: right unit (left is definitional), associativity
  -- and distributivity of γ ....

  --
  --  Monadic implementations
  --

  -- η-cns {n = O} f = tt
  -- η-cns {n = S n} {X = Xₙ , Xₛₙ} (fₙ , x , fₛₙ) = 
  --   nd x fₛₙ (λ p → η-frm {Xₛₙ = Xₛₙ} (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
  --           (λ p → ⟪ _ , _ , lf (app (typ (opr fₛₙ)) p) (dec fₛₙ p) ⟫ₒₚ)

  -- μ-cns {n = O} _ _ = tt
  -- μ-cns {n = S n} ⟪ _ , _ , lf f x ⟫ₒₚ κ = lf f x
  -- μ-cns {n = S n} {X = Xₙ , Xₛₙ} ⟪ _ , _ , nd {fₙ} x fₛₙ δ ε ⟫ₒₚ κ = 
  --   let w = κ (inlₚ (Σₚ (pos (opr fₛₙ)) (λ p₁ → pos (ε p₁))) ttₚ)
  --       κ' p q = κ (inrₚ ⊤ₚ ⟦ pos (opr fₛₙ) , (λ p₁ → pos (ε p₁)) ∣ p , q ⟧ₚ) 
  --       ϕ p = μ (ε p) (κ' p) 
  --   in γ-cns w δ ϕ

  -- γ-cns ⟪ _ , _ , lf f x ⟫ₒₚ δ ε = cns (ε ttₚ)
  -- γ-cns {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} ⟪ _ , _ , nd {fₙ} x c δ ε ⟫ₒₚ ϕ ψ =
  --   let ϕ' p q = ϕ ⟦ pos (opr c) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
  --       ψ' p q = ψ ⟦ pos (opr c) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
  --       δ' p = μ-frm {Xₛₙ = Xₛₙ} {x = dec c p} (δ p) (ϕ' p)
  --       ε' p = ⟪ _ , _ , γ-cns (ε p) (ϕ' p) (ψ' p) ⟫ₒₚ
  --   in nd x c δ' ε'

  --
  --  Opetopic Types
  --

  record 𝕆∞ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) : Set (ℓ-suc ℓ) where
    coinductive
    field
      Head : Frm X → Set ℓ
      Tail : 𝕆∞ {ℓ} {S n} (X , Head)

  open 𝕆∞ public 
