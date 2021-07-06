{-# OPTIONS --without-K --rewriting #-}

-- open import Prelude
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
    
  Cns↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    → {f : Frm X} {P : ℙ} {t : El P → Frm X} (c : Cns X f P t)
    → (f↓ : Frm↓ X↓ f) (t↓ : (p : El P) → Frm↓ X↓ (t p))
    → Set ℓ↓

  --
  --  Dependent Operations 
  --
  
  record Opr↓ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {f : Frm X}
      (X↓ : 𝕆↓ ℓ↓ X) (f↓ : Frm↓ X↓ f) (op : Opr X f) : Set ℓ↓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫ₒₚ↓
    field
      typ↓ : (p : El (pos op)) → Frm↓ X↓ (typ op p)
      cns↓ : Cns↓ X↓ (cns op) f↓ typ↓ 

  open Opr↓ public

  --
  --  Dependent Frame Eliminators
  --

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
    --  Dependent Frame Recursor Laws
    --
    
    ⊔ₚ-Frm↓-rec-unit-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {inlₚ* : El U → Frm X} {inrₚ* : El ⊥ₚ → Frm X}
      → (inl↓ₚ* : (u : El U) → Frm↓ X↓ (inlₚ* u))
      → (inr↓ₚ* : (b : El ⊥ₚ) → Frm↓ X↓ (inrₚ* b))
      → ⊔ₚ-Frm↓-rec inl↓ₚ* inr↓ₚ* ↦ inl↓ₚ* 
    {-# REWRITE ⊔ₚ-Frm↓-rec-unit-r #-}
    
    ⊔ₚ-Frm↓-rec-unit-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {V : ℙ} {inlₚ* : El ⊥ₚ → Frm X} {inrₚ* : El V → Frm X}
      → (inl↓ₚ* : (b : El ⊥ₚ) → Frm↓ X↓ (inlₚ* b))
      → (inr↓ₚ* : (v : El V) → Frm↓ X↓ (inrₚ* v))
      → ⊔ₚ-Frm↓-rec inl↓ₚ* inr↓ₚ* ↦ inr↓ₚ* 
    {-# REWRITE ⊔ₚ-Frm↓-rec-unit-l #-}
    
    ⊔ₚ-Frm↓-rec-assoc : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U V W : ℙ} {inlₚ* : El (U ⊔ₚ V) → Frm X}
      → {inrₚ* : El W → Frm X}
      → (inl↓ₚ* : (uv : El (U ⊔ₚ V)) → Frm↓ X↓ (inlₚ* uv))
      → (inr↓ₚ* : (w : El W) → Frm↓ X↓ (inrₚ* w))
      → ⊔ₚ-Frm↓-rec {U = U ⊔ₚ V} {V = W} inl↓ₚ* inr↓ₚ* ↦
          ⊔ₚ-Frm↓-rec {U = U} {V = V ⊔ₚ W} (λ u → inl↓ₚ* (inlₚ V u))
            (⊔ₚ-Frm↓-rec {U = V} {V = W} (λ v → inl↓ₚ* (inrₚ U v)) inr↓ₚ*) 
    {-# REWRITE ⊔ₚ-Frm↓-rec-assoc #-}

    Σₚ-Frm↓-rec-unit-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {ρ : (u : El U) (t : El ⊤ₚ) → Frm X}
      → (ρ↓ : (u : El U) (t : El ⊤ₚ) → Frm↓ X↓ (ρ u t))
      → Σₚ-Frm↓-rec ρ↓ ↦ (λ u → ρ↓ u ttₚ)
    {-# REWRITE Σₚ-Frm↓-rec-unit-r #-}

    Σₚ-Frm↓-rec-unit-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {V : El ⊤ₚ → ℙ} {ρ : (t : El ⊤ₚ) → El (V t) → Frm X}
      → (ρ↓ : (t : El ⊤ₚ) (v : El (V t)) → Frm↓ X↓ (ρ t v))
      → Σₚ-Frm↓-rec ρ↓ ↦ ρ↓ ttₚ
    {-# REWRITE Σₚ-Frm↓-rec-unit-l #-}

    Σₚ-Frm↓-rec-zero-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {ρ : (u : El U) → El ⊥ₚ → Frm X}
      → (ρ↓ : (u : El U) (b : El ⊥ₚ) → Frm↓ X↓ (ρ u b))
      → Σₚ-Frm↓-rec ρ↓ ↦ ⊥ₚ-Frm↓-rec 
    {-# REWRITE Σₚ-Frm↓-rec-zero-r #-}

    Σₚ-Frm↓-rec-zero-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {V : El ⊥ₚ → ℙ} {ρ : (b : El ⊥ₚ) → El (V b) → Frm X}
      → (ρ↓ : (b : El ⊥ₚ) (v : El (V b)) → Frm↓ X↓ (ρ b v))
      → Σₚ-Frm↓-rec ρ↓ ↦ ⊥ₚ-Frm↓-rec
    {-# REWRITE Σₚ-Frm↓-rec-zero-l #-}

    Σₚ-Frm↓-rec-assoc : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {V : El U → ℙ} {W : El (Σₚ U V) → ℙ}
      → {ρ : (uv : El (Σₚ U V)) → El (W uv) → Frm X}
      → (ρ↓ : (uv : El (Σₚ U V)) (w : El (W uv)) → Frm↓ X↓ (ρ uv w))
      → Σₚ-Frm↓-rec {U = Σₚ U V} {V = W} ρ↓ ↦
          Σₚ-Frm↓-rec {U = U} {V = λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)}
            (λ u → Σₚ-Frm↓-rec {U = V u} {V = (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)}
                     (λ v w → ρ↓ ⟦ U , V ∣ u , v ⟧ₚ w))
    {-# REWRITE Σₚ-Frm↓-rec-assoc #-}

    ⊔ₚ-Σₚ-Frm↓-rec-distrib-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U V : ℙ} {W : El (U ⊔ₚ V) → ℙ}
      → {ρ : (uv : El (U ⊔ₚ V)) → El (W uv) → Frm X}
      → (ρ↓ : (uv : El (U ⊔ₚ V)) (w : El (W uv)) → Frm↓ X↓ (ρ uv w))
      → Σₚ-Frm↓-rec ρ↓ ↦
          ⊔ₚ-Frm↓-rec {U = Σₚ U (λ u → W (inlₚ V u))}
                      {V = Σₚ V (λ v → W (inrₚ U v))}
            (Σₚ-Frm↓-rec {U = U} {V = (λ u → W (inlₚ V u))} (λ u w → ρ↓ (inlₚ V u) w))
            (Σₚ-Frm↓-rec {U = V} {V = (λ v → W (inrₚ U v))} (λ v w → ρ↓ (inrₚ U v) w))
    {-# REWRITE ⊔ₚ-Σₚ-Frm↓-rec-distrib-r #-}

    ⊔ₚ-Σₚ-Frm↓-rec-distrib-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {U : ℙ} {V : El U → ℙ} {W : El U → ℙ}
      → {ρ : (u : El U) (vw : El (V u ⊔ₚ W u)) → Frm X}
      → (ρ↓ : (u : El U) (vw : El (V u ⊔ₚ W u)) → Frm↓ X↓ (ρ u vw))
      → Σₚ-Frm↓-rec ρ↓ ↦
          ⊔ₚ-Frm↓-rec {U = Σₚ U V} {V = Σₚ U W}
            (Σₚ-Frm↓-rec {V = V} (λ u v → ρ↓ u (inlₚ (W u) v)))
            (Σₚ-Frm↓-rec {V = W} (λ u w → ρ↓ u (inrₚ (V u) w))) 
    {-# REWRITE ⊔ₚ-Σₚ-Frm↓-rec-distrib-l #-}

  --
  --  Dependent Frames
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
      dec↓ : (p : El (pos (opr fₛ))) → X↓ₛₙ (typ↓ opr↓ p) (dec fₛ p)

  open Frm↓ₛ
      
  --
  --  Dependent Opetopic Types 
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

  Cns↓ {n = O} X↓ _ _ _ = ⊤
  Cns↓ {n = S n} (X↓ₙ , X↓ₛₙ) (lf f x) (f↓ , x↓ , ηf↓ₛ) τ =
    (ηf↓ₛ ≡ η↓-frm f↓ x↓) ×
    (τ ≡ ⊥ₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ})
  Cns↓ {n = S n} (X↓ₙ , X↓ₛₙ) (nd x fₛₙ δ ε) (f↓ , x↓ , μf↓ₛ) τ =
    Σ (Frm↓ₛ X↓ₛₙ fₛₙ f↓ x↓) (λ f↓ₛₙ →
    Σ ((p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (typ↓ (opr↓ f↓ₛₙ) p) (dec↓ f↓ₛₙ p)) (λ δ↓ →
    Σ ((p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (typ↓ (opr↓ f↓ₛₙ) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p)) (λ ε↓ → 
    (μf↓ₛ ≡ μ↓-frm f↓ₛₙ δ↓) ×
    (τ ≡ ⊔ₚ-Frm↓-rec {X↓ = (X↓ₙ , X↓ₛₙ)} (⊤ₚ-Frm↓-rec {X↓ = (X↓ₙ , X↓ₛₙ)} (f↓ , x↓ , f↓ₛₙ))
         (Σₚ-Frm↓-rec {X↓ = (X↓ₙ , X↓ₛₙ)} (λ p q → typ↓ (ε↓ p) q))))))

  --
  --  "Smart" Constructors for leaves and nodes
  --

  lf↓ : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {f : Frm Xₙ} {x : Xₛₙ f}
    → (f↓ : Frm↓ X↓ₙ f) (x↓ : X↓ₛₙ f↓ x)
    → Cns↓ (X↓ₙ , X↓ₛₙ) (lf f x) (f↓ , x↓ , η↓-frm f↓ x↓)
      (⊥ₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ})
  lf↓ f↓ x↓ = refl , refl 


  -- η↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
  --   → {f : Frm X} (f↓ : Frm↓ X↓ f)
  --   → Cns↓ X↓ (η-cns f) f↓ (⊤ₚ-Frm↓-rec f↓) 
  η↓-cns {n = O} f↓ = tt
  η↓-cns {n = S n} {X = Xₙ , Xₛₙ} {X↓ = X↓ₙ , X↓ₛₙ} {f = f , x , μfₛ} (f↓ , x↓ , μf↓ₛ) =
    μf↓ₛ , (λ p → η↓-frm (typ↓ (opr↓ μf↓ₛ) p) (dec↓ μf↓ₛ p)) ,
          (λ p → ⟪ ⊥ₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ} , lf↓ (typ↓ (opr↓ μf↓ₛ) p) (dec↓ μf↓ₛ p) ⟫ₒₚ↓) , {!!} , {!!}

  -- I see.  And now we need the equations for the frame
  -- eliminators and whatnot ...