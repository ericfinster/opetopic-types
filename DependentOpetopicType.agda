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

  open Frm↓ₛ public
      
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
  --  Dependent Monadic Laws
  --

  postulate

    μ↓-unit-r : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {c : Opr X f}
      → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
      → μ↓-cns c↓ (λ p → η↓ (typ↓ c↓ p)) ↦ cns↓ c↓
    {-# REWRITE μ↓-unit-r #-}

    μ↓-unit-l : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {δ : (p : El (pos (η f))) → Opr X (typ (η f) p)}
      → (f↓ : Frm↓ X↓ f) (δ↓ : (p : El (pos (η f))) → Opr↓ X↓ (typ↓ (η↓ f↓) p) (δ p))
      → μ↓-cns (η↓ f↓) δ↓ ↦ cns↓ (δ↓ ttₚ)
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} {X↓ : 𝕆↓ ℓ↓ X}
      → {f : Frm X} {c : Opr X f}
      → {δ : (p : El (pos c)) → Opr X (typ c p)}
      → {ε : (p : El (pos (μ c δ))) → Opr X (typ (μ c δ) p)}
      → {f↓ : Frm↓ X↓ f} (c↓ : Opr↓ X↓ f↓ c)
      → (δ↓ : (p : El (pos c)) → Opr↓ X↓ (typ↓ c↓ p) (δ p))
      → (ε↓ : (p : El (pos (μ c δ))) → Opr↓ X↓ (typ↓ (μ↓ c↓ δ↓) p) (ε p))
      → μ↓-cns (μ↓ c↓ δ↓) ε↓ ↦
          μ↓-cns c↓ (λ p → μ↓ (δ↓ p) (λ q → ε↓ ⟦ pos c , (λ p → pos (δ p)) ∣ p , q ⟧ₚ))
    {-# REWRITE μ↓-assoc #-}

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
    → Cns↓ (X↓ₙ , X↓ₛₙ) (lf f x)
        (f↓ , x↓ , η↓-frm f↓ x↓)
        (⊥ₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ})
  lf↓ f↓ x↓ = refl , refl 

  nd↓ : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → {δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (typ (opr fₛₙ) p) (dec fₛₙ p)}
    → {ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (typ (opr fₛₙ) p , dec fₛₙ p , δ p)}
    → {f↓ₙ : Frm↓ X↓ₙ fₙ} (x↓ : X↓ₛₙ f↓ₙ x) (f↓ₛₙ : Frm↓ₛ X↓ₛₙ fₛₙ f↓ₙ x↓)
    → (δ↓ : (p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (typ↓ (opr↓ f↓ₛₙ) p) (dec↓ f↓ₛₙ p))
    → (ε↓ : (p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (typ↓ (opr↓ f↓ₛₙ) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p))
    → Cns↓ (X↓ₙ , X↓ₛₙ) (nd x fₛₙ δ ε) (f↓ₙ , x↓ , μ↓-frm f↓ₛₙ δ↓)
        (⊔ₚ-Frm↓-rec {inlₚ* = ⊤ₚ-Frm-rec (fₙ , x , fₛₙ)}
                     {inrₚ* = Σₚ-Frm-rec (λ p q → typ (ε p) q)}
                     (⊤ₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ} (f↓ₙ , x↓ , f↓ₛₙ) )
                     (Σₚ-Frm↓-rec {X↓ = X↓ₙ , X↓ₛₙ} (λ p q → typ↓ (ε↓ p) q)))
  nd↓ x↓ f↓ₛₙ δ↓ ε↓ = f↓ₛₙ , δ↓ , ε↓ , refl , refl

  --
  --  Dependent Grafting
  --

  γ↓-cns : ∀ {ℓ ℓ↓} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {X↓ₙ : 𝕆↓ ℓ↓ Xₙ} {X↓ₛₙ : {f : Frm Xₙ} (f↓ : Frm↓ X↓ₙ f) (x : Xₛₙ f) → Set ℓ↓}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → {c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ)}
    → {δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (typ (opr fₛₙ) p) (dec fₛₙ p)}
    → {ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (typ (opr fₛₙ) p , dec fₛₙ p , δ p)}
    → {f↓ₙ : Frm↓ X↓ₙ fₙ} {x↓ : X↓ₛₙ f↓ₙ x} {f↓ₛₙ : Frm↓ₛ X↓ₛₙ fₛₙ f↓ₙ x↓}
    → (c↓ : Opr↓ (X↓ₙ , X↓ₛₙ) (f↓ₙ , x↓ , f↓ₛₙ) c)
    → (δ↓ : (p : El (pos (opr fₛₙ))) → Frm↓ₛ X↓ₛₙ (δ p) (typ↓ (opr↓ f↓ₛₙ) p) (dec↓ f↓ₛₙ p))
    → (ε↓ : (p : El (pos (opr fₛₙ))) → Opr↓ (X↓ₙ , X↓ₛₙ) (typ↓ (opr↓ f↓ₛₙ) p , dec↓ f↓ₛₙ p , δ↓ p) (ε p))
    → Cns↓ (X↓ₙ , X↓ₛₙ) (γ-cns c δ ε) (f↓ₙ , x↓ , μ↓-frm f↓ₛₙ δ↓)
        (⊔ₚ-Frm↓-rec {inlₚ* = typ c} {inrₚ* = Σₚ-Frm-rec (λ p q → typ (ε p) q)}
          (typ↓ c↓) (Σₚ-Frm↓-rec {ρ = λ p q → typ (ε p) q} (λ p q → typ↓ (ε↓ p) q))) 

  --
  --  Dependent Monadic Implementation
  --

  η↓-cns {n = O} f↓ = tt
  η↓-cns {n = S n} (f↓ , x↓ , μf↓ₛ) =
    nd↓ x↓ μf↓ₛ
      (λ p → η↓-frm (typ↓ (opr↓ μf↓ₛ) p) (dec↓ μf↓ₛ p))
      (λ p → ⟪ _ , lf↓ (typ↓ (opr↓ μf↓ₛ) p) (dec↓ μf↓ₛ p) ⟫ₒₚ↓)

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
