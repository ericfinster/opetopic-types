{-# OPTIONS --without-K --rewriting #-}

-- open import Prelude
open import HoTT
open import MiniUniverse
open import AbsoluteOpetopicTypes

module DependentOpetopicType where

  --
  --  The Universe of Dependent Opetopic Types
  --

  𝕆↓ : ∀ {ℓ : ULevel} {n : ℕ} (ℓ↓ : ULevel) (X : 𝕆 ℓ n)
    → Set (lmax ℓ (lsucc ℓ↓))
    
  Frm↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    (f : Frm X) → Set ℓ↓
    
  Cns↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    → {f : Frm X} {P : ℙ} {t : El P → Frm X} (c : Cns X f P t)
    → (f↓ : Frm↓ X↓ f) (t↓ : (p : El P) → Frm↓ X↓ (t p))
    → Set ℓ↓

  --
  --  Dependent operations and their projections
  --

  -- {-# TERMINATING #-}
  -- Opr↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
  --   → {f : Frm X} (f↓ : Frm↓ X↓ f) 
  --   → (op : Opr X f) → Set ℓ↓
  -- Opr↓ X↓ f↓ op =
  --   Σ ((p : El (pos op)) → Frm↓ X↓ (typ op p)) (λ typ↓ →
  --     Cns↓ X↓ (cns op) f↓ typ↓ ) 

  -- typ↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
  --   → {f : Frm X} {f↓ : Frm↓ X↓ f}
  --   → {op : Opr X f} → Opr↓ X↓ f↓ op 
  --   → (p : El (pos op)) → Frm↓ X↓ (typ op p)
  -- typ↓ = fst 

  -- cns↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
  --   → {f : Frm X} {f↓ : Frm↓ X↓ f}
  --   → {op : Opr X f} (op↓ : Opr↓ X↓ f↓ op)
  --   → Cns↓ X↓ (cns op) f↓ (typ↓ op↓)
  -- cns↓ = snd

  record Opr↓ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {f : Frm X}
      (X↓ : 𝕆↓ ℓ↓ X) (f↓ : Frm↓ X↓ f) (op : Opr X f) : Set ℓ↓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫ₒₚ↓
    field
      typ↓ : (p : El (pos op)) → Frm↓ X↓ (typ op p)
      cns↓ : Cns↓ X↓ (cns op) f↓ typ↓ 

  open Opr↓ public
  
  postulate

    ⊥ₚ-Frm↓-rec : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n}
      → {X↓ : 𝕆↓ ℓ↓ X} 
      → (p : El ⊥ₚ) → Frm↓ X↓ (⊥ₚ-Frm-rec p)

    ⊤ₚ-Frm↓-rec : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} (f↓ : Frm↓ X↓ f)
      → (p : El ⊤ₚ) → Frm↓ X↓ (⊤ₚ-Frm-rec f p) 

    ⊤ₚ-Frm↓-rec-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} (f↓ : Frm↓ X↓ f)
      → ⊤ₚ-Frm↓-rec f↓ ttₚ ↦ f↓
    {-# REWRITE ⊤ₚ-Frm↓-rec-β #-}

    ⊔ₚ-Frm↓-rec : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U V : ℙ} {inlₚ* : El U → Frm X} {inrₚ* : El V → Frm X}
      → (inl↓ₚ* : (u : El U) → Frm↓ X↓ (inlₚ* u))
      → (inr↓ₚ* : (v : El V) → Frm↓ X↓ (inrₚ* v))
      → (uv : El (U ⊔ₚ V)) → Frm↓ X↓ (⊔ₚ-Frm-rec inlₚ* inrₚ* uv) 

    ⊔ₚ-Frm↓-rec-inl-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U V : ℙ} {inlₚ* : El U → Frm X} {inrₚ* : El V → Frm X}
      → (inl↓ₚ* : (u : El U) → Frm↓ X↓ (inlₚ* u))
      → (inr↓ₚ* : (v : El V) → Frm↓ X↓ (inrₚ* v))
      → (u : El U) → ⊔ₚ-Frm↓-rec inl↓ₚ* inr↓ₚ* (inlₚ V u) ↦ inl↓ₚ* u
    {-# REWRITE ⊔ₚ-Frm↓-rec-inl-β #-}

    ⊔ₚ-Frm↓-rec-inr-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U V : ℙ} {inlₚ* : El U → Frm X} {inrₚ* : El V → Frm X}
      → (inl↓ₚ* : (u : El U) → Frm↓ X↓ (inlₚ* u))
      → (inr↓ₚ* : (v : El V) → Frm↓ X↓ (inrₚ* v))
      → (v : El V) → ⊔ₚ-Frm↓-rec inl↓ₚ* inr↓ₚ* (inrₚ U v) ↦ inr↓ₚ* v
    {-# REWRITE ⊔ₚ-Frm↓-rec-inr-β #-}

    Σₚ-Frm↓-rec : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {V : El U → ℙ}
      → {ρ : (u : El U) → El (V u) → Frm X}
      → (ρ↓ : (u : El U) (v : El (V u)) → Frm↓ X↓ (ρ u v))
      → (uv : El (Σₚ U V)) → Frm↓ X↓ (Σₚ-Frm-rec ρ uv)

    Σₚ-Frm↓-rec-β : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {V : El U → ℙ}
      → {ρ : (u : El U) → El (V u) → Frm X}
      → (ρ↓ : (u : El U) (v : El (V u)) → Frm↓ X↓ (ρ u v))
      → (u : El U) (v : El (V u))
      → Σₚ-Frm↓-rec ρ↓ ⟦ U , V ∣ u , v ⟧ₚ ↦ ρ↓ u v
    {-# REWRITE Σₚ-Frm↓-rec-β #-}

  --
  --  Dependent Frames
  --
  
  -- Frm↓ₛ : ∀ {ℓ ℓ↓} {n : ℕ}
  --   → {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ} {X↓ₙ : 𝕆↓ ℓ↓ Xₙ}
  --   → (X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓)
  --   → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
  --   → (f↓ : Frm↓ X↓ₙ f) (x↓ : X↓ₛₙ f↓ x) → Set ℓ↓
  -- Frm↓ₛ {X↓ₙ = X↓ₙ} X↓ₛₙ fₛ f↓ x↓ = 
  --   Σ (Opr↓ X↓ₙ f↓ (opr fₛ)) (λ opr↓ →
  --     (p : El (pos (opr fₛ))) → X↓ₛₙ (typ↓ opr↓ p) (dec fₛ p))

  -- opr↓ : ∀ {ℓ ℓ↓} {n : ℕ}
  --   → {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ} {X↓ₙ : 𝕆↓ ℓ↓ Xₙ}
  --   → {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
  --   → {f : Frm Xₙ} {x : Xₛₙ f} {fₛ : Frmₛ Xₛₙ f x}
  --   → {f↓ : Frm↓ X↓ₙ f} {x↓ : X↓ₛₙ f↓ x}
  --   → Frm↓ₛ X↓ₛₙ fₛ f↓ x↓ → Opr↓ X↓ₙ f↓ (opr fₛ) 
  -- opr↓ = fst

  -- dec↓ : ∀ {ℓ ℓ↓} {n : ℕ}
  --   → {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ} {X↓ₙ : 𝕆↓ ℓ↓ Xₙ}
  --   → {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
  --   → {f : Frm Xₙ} {x : Xₛₙ f} {fₛ : Frmₛ Xₛₙ f x}
  --   → {f↓ : Frm↓ X↓ₙ f} {x↓ : X↓ₛₙ f↓ x}
  --   → (f↓ₛ : Frm↓ₛ X↓ₛₙ fₛ f↓ x↓)
  --   → (p : El (pos (opr fₛ))) → X↓ₛₙ (typ↓ (opr↓ {X↓ₛₙ = X↓ₛₙ} {x↓ = x↓} f↓ₛ) p) (dec fₛ p)
  -- dec↓ = snd 

  record Frm↓ₛ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ} {X↓ₙ : 𝕆↓ ℓ↓ Xₙ}
    (X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓)
    {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    (f↓ : Frm↓ X↓ₙ f) (x↓ : X↓ₛₙ f↓ x) : Set ℓ↓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫f↓
    field
      opr↓ : Opr↓ X↓ₙ f↓ (opr fₛ)
      dec↓ : (p : El (pos (opr fₛ))) → X↓ₛₙ (typ↓ opr↓ p) (dec fₛ p)

  open Frm↓ₛ
      
  --
  --  Dependent Opetopic Types and Frames
  --
  
  𝕆↓ {n = O} ℓ↓ X = X → Set ℓ↓
  𝕆↓ {n = S n} ℓ↓ (Xₙ , Xₛₙ) =
    Σ (𝕆↓ ℓ↓ Xₙ) (λ X↓ₙ →
    {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓)
  
  Frm↓ {n = O} {X} X↓ ⟪ x , P , t ⟫ =
    (X↓ x) × ((p : El P) → X↓ (t p))
  Frm↓ {n = S n} {Xₙ , Xₛₙ} (X↓ₙ , X↓ₛₙ) (f , x , fₛ) =
    Σ (Frm↓ X↓ₙ f) (λ f↓ →
    Σ (X↓ₛₙ f↓ x) (λ x↓ →
    Frm↓ₛ X↓ₛₙ fₛ f↓ x↓))

  --
  --  Dependent Monadic Structure
  --

  postulate
  
    η↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} (f↓ : Frm↓ X↓ f)
      → Cns↓ X↓ (η-cns f) f↓ (⊤ₚ-Frm↓-rec f↓) 

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
    ⟪ η↓ f↓ , ⊤ₚ-elim (λ p → X↓ₛₙ (typ↓ (η↓ f↓) p) (dec (η-frm {Xₛₙ = Xₛₙ} f x) p)) x↓ ⟫f↓ 

  postulate
  
    μ↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {c : Opr X f}
      → {δ : (p : El (pos c)) → Opr X (typ c p)}
      → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
      → (δ↓ : (p : El (pos c)) → Opr↓ X↓ (typ↓ c↓ p) (δ p))
      → Cns↓ X↓ (μ-cns c δ ) f↓ (Σₚ-Frm↓-rec (λ p q → typ↓ (δ↓ p) q)) 

  μ↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
    → {f : Frm X} {c : Opr X f}
    → {δ : (p : El (pos c)) → Opr X (typ c p)}
    → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
    → (δ↓ : (p : El (pos c)) → Opr↓ X↓ (typ↓ c↓ p) (δ p))
    → Opr↓ X↓ f↓ (μ c δ)
  μ↓ c↓ δ↓ =  ⟪ _ , μ↓-cns c↓ δ↓  ⟫ₒₚ↓ 

  μ↓-frm : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {f : Frm Xₙ} {x : Xₛₙ f} {fₛ : Frmₛ Xₛₙ f x}
    → {ϕ : (p : El (pos (opr fₛ))) → Frmₛ Xₛₙ (typ (opr fₛ) p) (dec fₛ p)}
    → {f↓ : Frm↓ X↓ₙ f} {x↓ : X↓ₛₙ f↓ x} (f↓ₛ : Frm↓ₛ X↓ₛₙ fₛ f↓ x↓)
    → (ϕ↓ : (p : El (pos (opr fₛ))) → Frm↓ₛ X↓ₛₙ (ϕ p) (typ↓ (opr↓ f↓ₛ) p) (dec↓ f↓ₛ p))
    → Frm↓ₛ X↓ₛₙ (μ-frm fₛ ϕ) f↓ x↓
  μ↓-frm f↓ₛ ϕ↓ = ⟪ μ↓ (opr↓ f↓ₛ) (λ p → opr↓ (ϕ↓ p)) ,
    Σₚ-elim _ _ _ (λ p q → dec↓ (ϕ↓ p) q) ⟫f↓
    
  --
  --  Dependent constructors
  --

  Cns↓ {n = O} X↓ _ _ _ = Lift ⊤
  Cns↓ {n = S n} (X↓ₙ , X↓ₛₙ) (lf f x) (f↓ , x↓ , ηf↓ₛ) τ =
    (ηf↓ₛ == η↓-frm f↓ x↓) ×
    (τ == ⊥ₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ})
  Cns↓ {n = S n} (X↓ₙ , X↓ₛₙ) (nd x fₛₙ δ ε) (f↓ , x↓ , μf↓ₛ) τ =
    Σ (Frm↓ₛ X↓ₛₙ fₛₙ f↓ x↓) (λ f↓ₛₙ →
    Σ ((p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (typ↓ (opr↓ f↓ₛₙ) p) (dec↓ f↓ₛₙ p)) (λ δ↓ →
    Σ ((p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (typ↓ (opr↓ f↓ₛₙ) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p)) (λ ε↓ → 
    (μf↓ₛ == μ↓-frm f↓ₛₙ δ↓) ×
    (τ == ⊔ₚ-Frm↓-rec {X↓ = (X↓ₙ , X↓ₛₙ)} (⊤ₚ-Frm↓-rec {X↓ = (X↓ₙ , X↓ₛₙ)} (f↓ , x↓ , f↓ₛₙ))
         (Σₚ-Frm↓-rec {X↓ = (X↓ₙ , X↓ₛₙ)} (λ p q → typ↓ (ε↓ p) q))))))

  
