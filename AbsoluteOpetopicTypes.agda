{-# OPTIONS --without-K --rewriting --guardedness #-}

open import MiniHoTT
open import MiniUniverse

module AbsoluteOpetopicTypes where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ
  Cns : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
    → (f : Frm X) (P : ℙ) (t : El P → Frm X)
    → Set ℓ

  record Opr {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (f : Frm X) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_,_⟫ₒₚ
    field
      pos : ℙ
      typ : El pos → Frm X 
      cns : Cns X f pos typ

  open Opr public
  
  -- Custom recursors for Frm's to avoid positivity
  -- problems when naively using the corresponding
  -- eliminators.
  postulate
  
    ⊥ₚ-Frm-rec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → El ⊥ₚ → Frm X

    ⊤ₚ-Frm-rec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → (f : Frm X)
      → El ⊤ₚ → Frm X
      
    ⊤ₚ-Frm-rec-β : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (p : El ⊤ₚ) (f : Frm X)
      → ⊤ₚ-Frm-rec f p ↦ f
    {-# REWRITE ⊤ₚ-Frm-rec-β #-}

    ⊔ₚ-Frm-rec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {U V : ℙ}
      → (inlₚ* : El U → Frm X)
      → (inrₚ* : El V → Frm X)
      → El (U ⊔ₚ V) → Frm X

    ⊔ₚ-Frm-rec-inl-β : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) {U V : ℙ} 
      → (inlₚ* : El U → Frm X)
      → (inrₚ* : El V → Frm X)
      → (u : El U)
      → ⊔ₚ-Frm-rec inlₚ* inrₚ* (inlₚ V u) ↦ inlₚ* u
    {-# REWRITE ⊔ₚ-Frm-rec-inl-β #-}

    ⊔ₚ-Frm-rec-inr-β : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) {U V : ℙ} 
      → (inlₚ* : El U → Frm X)
      → (inrₚ* : El V → Frm X)
      → (v : El V)
      → ⊔ₚ-Frm-rec inlₚ* inrₚ* (inrₚ U v) ↦ inrₚ* v
    {-# REWRITE ⊔ₚ-Frm-rec-inr-β #-}

    Σₚ-Frm-rec : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {U : ℙ} {V : El U → ℙ}
      → (ρ : (u : El U) → El (V u) → Frm X)
      → El (Σₚ U V) → Frm X 

    Σₚ-Frm-rec-β : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U : ℙ) (V : El U → ℙ)
      → (ρ : (u : El U) → El (V u) → Frm X)
      → (u : El U) (v : El (V u))
      → Σₚ-Frm-rec ρ ⟦ U , V ∣ u , v ⟧ₚ ↦ ρ u v
    {-# REWRITE Σₚ-Frm-rec-β #-}

    --
    --  Laws for frame recursors
    --
    
    ⊔ₚ-Frm-rec-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (U : ℙ)
      → (inlₚ* : El U → Frm X)
      → (inrₚ* : El ⊥ₚ → Frm X)
      → ⊔ₚ-Frm-rec inlₚ* inrₚ* ↦ inlₚ*
    {-# REWRITE ⊔ₚ-Frm-rec-unit-r #-}

    ⊔ₚ-Frm-rec-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (V : ℙ)
      → (inlₚ* : El ⊥ₚ → Frm X)
      → (inrₚ* : El V → Frm X)
      → ⊔ₚ-Frm-rec inlₚ* inrₚ* ↦ inrₚ*
    {-# REWRITE ⊔ₚ-Frm-rec-unit-l #-}

    ⊔ₚ-Frm-rec-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U V W : ℙ)
      → (inlₚ* : El (U ⊔ₚ V) → Frm X)
      → (inrₚ* : El W → Frm X) 
      → ⊔ₚ-Frm-rec {U = U ⊔ₚ V} {V = W} inlₚ* inrₚ* ↦
          ⊔ₚ-Frm-rec {U = U} {V = V ⊔ₚ W}
            (λ u → inlₚ* (inlₚ V u))
            (⊔ₚ-Frm-rec {U = V} {V = W} (λ v → inlₚ* (inrₚ U v)) inrₚ*) 
    {-# REWRITE ⊔ₚ-Frm-rec-assoc #-} 

    Σₚ-Frm-rec-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (U : ℙ)
      → (ρ : (u : El U) (t : El ⊤ₚ) → Frm X)
      → Σₚ-Frm-rec ρ ↦ (λ u → ρ u ttₚ)
    {-# REWRITE Σₚ-Frm-rec-unit-r #-}

    Σₚ-Frm-rec-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (V : El ⊤ₚ → ℙ)
      → (ρ : (u : El ⊤ₚ) (v : El (V u)) → Frm X)
      → Σₚ-Frm-rec ρ ↦ ρ ttₚ
    {-# REWRITE Σₚ-Frm-rec-unit-l #-}

    Σₚ-Frm-rec-zero-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (U : ℙ)
      → (ρ : (u : El U) (v : El ⊥ₚ) → Frm X)
      → Σₚ-Frm-rec ρ ↦ ⊥ₚ-Frm-rec
    {-# REWRITE Σₚ-Frm-rec-zero-r #-}

    Σₚ-Frm-rec-zero-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (V : El ⊥ₚ → ℙ)
      → (ρ : (u : El ⊥ₚ) (v : El (V u)) → Frm X)
      → Σₚ-Frm-rec ρ ↦ ⊥ₚ-Frm-rec 
    {-# REWRITE Σₚ-Frm-rec-zero-l #-}

    Σₚ-Frm-rec-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (U : ℙ) (V : El U → ℙ) (W : El (Σₚ U V) → ℙ)
      → (ρ : (u : El (Σₚ U V)) → El (W u) → Frm X)
      → Σₚ-Frm-rec {U = Σₚ U V} {V = W} ρ ↦
        Σₚ-Frm-rec {U = U} {V = λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)}
          (λ u → Σₚ-Frm-rec {U = V u} {V = (λ v → W ⟦ U , V ∣ u , v ⟧ₚ)}
          (λ v w → ρ ⟦ U , V ∣ u , v ⟧ₚ w) )
    {-# REWRITE Σₚ-Frm-rec-assoc #-}

    ⊔ₚ-Σₚ-Frm-rec-distrib-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (U V : ℙ)
      → (W : El (U ⊔ₚ V) → ℙ)
      → (ρ : (p : El (U ⊔ₚ V)) (q : El (W p)) → Frm X) 
      → Σₚ-Frm-rec ρ ↦ ⊔ₚ-Frm-rec {U = Σₚ U (λ u → W (inlₚ V u))}
                                  {V = Σₚ V (λ v → W (inrₚ U v))}
      (Σₚ-Frm-rec {U = U} {V = (λ u → W (inlₚ V u))} (λ u w → ρ (inlₚ V u) w))
      (Σₚ-Frm-rec {U = V} {V = (λ v → W (inrₚ U v))} (λ v w → ρ (inrₚ U v) w))
    {-# REWRITE ⊔ₚ-Σₚ-Frm-rec-distrib-r #-}

    ⊔ₚ-Σₚ-Frm-rec-distrib-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) (U : ℙ)
      → (V : El U → ℙ) (W : El U → ℙ)
      → (ρ : (u : El U) (vw : El (V u ⊔ₚ W u)) → Frm X)
      → Σₚ-Frm-rec ρ ↦ ⊔ₚ-Frm-rec {U = Σₚ U V} {V = Σₚ U W}
          (Σₚ-Frm-rec {V = V} (λ u v → ρ u (inlₚ (W u) v)))
          (Σₚ-Frm-rec {V = W} (λ u w → ρ u (inrₚ (V u) w)))
    {-# REWRITE ⊔ₚ-Σₚ-Frm-rec-distrib-l #-}

  --
  --  Higher Frames
  --

  record Frmₛ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} (Xₛₙ : Frm Xₙ → Set ℓ) (f : Frm Xₙ) (x : Xₛₙ f) : Set ℓ where
    eta-equality
    inductive
    constructor ⟪_,_⟫f
    field
      opr : Opr Xₙ f
      dec : (p : El (pos opr)) → Xₛₙ (typ opr p)

  open Frmₛ public
      
  --
  --  Opetopic Types and Frames
  --
  
  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ X → (f : Frm X) → Set ℓ)

  Frm {n = O} X = Arity X -- probably don't want to do this now ...
  Frm {n = S n} (Xₙ , Xₛₙ) = Σ (Frm Xₙ) (λ f → Σ (Xₛₙ f) (λ x → Frmₛ Xₛₙ f x))

  --
  --  Monadic Structure
  --
  
  η-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
    → Cns X f ⊤ₚ (⊤ₚ-Frm-rec f) 

  η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X) → Opr X f
  η f = ⟪ _ , _ , η-cns f ⟫ₒₚ

  η-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → (f : Frm Xₙ) (x : Xₛₙ f)
    → Frmₛ Xₛₙ f x 
  η-frm {Xₛₙ = Xₛₙ} f x = ⟪ η f , ⊤ₚ-elim (λ p → Xₛₙ (typ (η f) p)) x ⟫f 

  μ-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (pos c)) → Opr X (typ c p))
    → Cns X f (Σₚ (pos c) (λ p → pos (δ p)))
              (Σₚ-Frm-rec (λ p q → typ (δ p) q))

  μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    → {f : Frm X} (c : Opr X f)
    → (δ : (p : El (pos c)) → Opr X (typ c p))
    → Opr X f
  μ c δ = ⟪ _ , _ , μ-cns c δ ⟫ₒₚ

  μ-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    → (ϕ : (p : El (pos (opr fₛ))) → Frmₛ Xₛₙ (typ (opr fₛ) p) (dec fₛ p))
    → Frmₛ Xₛₙ f x
  μ-frm fₛ ϕ = ⟪ μ (opr fₛ) (λ p → opr (ϕ p)) ,
                Σₚ-elim _ _ _ (λ p q → dec (ϕ p) q) ⟫f
    
  --
  --  Monadic Laws
  --

  postulate

    μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → μ-cns c (λ p → η (typ c p)) ↦ cns c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (f : Frm X) (δ : (p : El (pos (η f))) → Opr X (typ (η f) p))
      → μ-cns (η f) δ ↦ cns (δ ttₚ)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Opr X f)
      → (δ : (p : El (pos c)) → Opr X (typ c p))
      → (ε : (p : El (pos (μ c δ))) → Opr X (typ (μ c δ) p))
      → μ-cns (μ c δ) ε ↦ μ-cns c (λ p → μ (δ p)
          (λ q → ε ⟦ pos c , (λ p → pos (δ p)) ∣ p , q ⟧ₚ))  
    {-# REWRITE μ-assoc #-}

  --
  --  The slice construction
  --

  data Tree {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ) :
    (f : Frm (Xₙ , Xₛₙ)) (P : ℙ) (t : El P → Frm (Xₙ , Xₛₙ)) → Set ℓ where 

    lf : (f : Frm Xₙ) (x : Xₛₙ f)
      → Tree Xₙ Xₛₙ (f , x , η-frm f x)
          ⊥ₚ ⊥ₚ-Frm-rec 

    nd : {fₙ : Frm Xₙ} (x : Xₛₙ fₙ) (fₛₙ : Frmₛ Xₛₙ fₙ x)
      → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (typ (opr fₛₙ) p) (dec fₛₙ p))
      → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (typ (opr fₛₙ) p , dec fₛₙ p , δ p))
      → Tree Xₙ Xₛₙ (fₙ , x , μ-frm fₛₙ δ) 
          (⊤ₚ ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p)))
          (⊔ₚ-Frm-rec (⊤ₚ-Frm-rec (fₙ , x , fₛₙ))
                      (Σₚ-Frm-rec (λ p q → typ (ε p) q))) 


  Cns {n = O} X _ _ _ = ⊤
  Cns {n = S n} (Xₙ , Xₛₙ) = Tree Xₙ Xₛₙ

  --
  --  Grafting of trees
  --
  
  γ-cns : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {fₙ : Frm Xₙ} {x : Xₛₙ fₙ} {fₛₙ : Frmₛ Xₛₙ fₙ x}
    → (c : Opr (Xₙ , Xₛₙ) (fₙ , x , fₛₙ))
    → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (typ (opr fₛₙ) p) (dec fₛₙ p))
    → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (typ (opr fₛₙ) p , dec fₛₙ p , δ p))
    → Cns (Xₙ , Xₛₙ) (fₙ , x , μ-frm fₛₙ δ)
        (pos c ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p)))
        (⊔ₚ-Frm-rec (typ c) (Σₚ-Frm-rec (λ p q → typ (ε p) q)))

  -- Missing still: right unit (left is definitional), associativity
  -- and distributivity of γ ....

  --
  --  Monadic implementations
  --

  η-cns {n = O} f = tt
  η-cns {n = S n} (fₙ , x , fₛₙ) = 
    nd x fₛₙ (λ p → η-frm (typ (opr fₛₙ) p) (dec fₛₙ p))
            (λ p → ⟪ _ , _ , lf (typ (opr fₛₙ) p) (dec fₛₙ p) ⟫ₒₚ)

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
        δ' p = μ-frm (δ p) (ϕ' p)
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
