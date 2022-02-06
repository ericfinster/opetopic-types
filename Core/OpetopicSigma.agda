--
--  OpetopicSigma.agda - Dependent Sum of Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.Prelude
open import Core.Opetopes
open import Core.OpetopicType
open import Core.OpetopicFamily
open import Core.Element

module Core.OpetopicSigma where

  Σₒ : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (P : 𝕆Fam X ℓ₁)
    → 𝕆Type n (ℓ-max ℓ₀ ℓ₁) 

  -- Action on Frames
  fst-frm : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} → Frm (Σₒ X P) 𝑜 → Frm X 𝑜

  snd-frm : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} (f : Frm (Σₒ X P) 𝑜) → Frm↓ P (fst-frm f)

  pair-frm : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜) (f↓ : Frm↓ P f)
    → Frm (Σₒ X P) 𝑜 

  -- Action on Constructors
  {-# TERMINATING #-} -- usual fix 
  fst-cns : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm (Σₒ X P) 𝑜}
    → Cns (Σₒ X P) f 𝑝 → Cns X (fst-frm f) 𝑝

  snd-cns : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm (Σₒ X P) 𝑜}
    → (c : Cns (Σₒ X P) f 𝑝) → Cns↓ P (snd-frm f) (fst-cns c)
    
  pair-cns : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
    → (c : Cns X f 𝑝) (c↓ : Cns↓ P f↓ c)
    → Cns (Σₒ X P) (pair-frm f f↓) 𝑝

  -- Axioms
  postulate

    -- Computation rules
    fst-pair-frm-β : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜) (f↓ : Frm↓ P f)
      → fst-frm (pair-frm f f↓) ↦ f
    {-# REWRITE fst-pair-frm-β #-}
    
    snd-pair-frm-β : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜) (f↓ : Frm↓ P f)
      → snd-frm (pair-frm f f↓) ↦ f↓
    {-# REWRITE snd-pair-frm-β #-}

    pair-frm-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm (Σₒ X P) 𝑜)
      → pair-frm (fst-frm f) (snd-frm f) ↦ f
    {-# REWRITE pair-frm-η #-}

    fst-pair-cns-β : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → (c : Cns X f 𝑝) (c↓ : Cns↓ P f↓ c)
      → fst-cns (pair-cns c c↓) ↦ c 
    {-# REWRITE fst-pair-cns-β #-}
    
    snd-pair-cns-β : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → (c : Cns X f 𝑝) (c↓ : Cns↓ P f↓ c)
      → snd-cns (pair-cns c c↓) ↦ c↓
    {-# REWRITE snd-pair-cns-β #-}

    pair-cns-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm (Σₒ X P) 𝑜}
      → (c : Cns (Σₒ X P) f 𝑝)
      → pair-cns (fst-cns c) (snd-cns c) ↦ c
    {-# REWRITE pair-cns-η #-}

    -- Calculation of shapes 
    pair-shp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (f : Frm (Σₒ X P) 𝑜)
      → (c : Cns (Σₒ X P) f 𝑝) (p : Pos 𝑝)
      → Shp (Σₒ X P) c p ↦
          pair-frm (Shp X (fst-cns c) p) (Shp↓ P (snd-cns c) p)
    {-# REWRITE pair-shp #-} 

    -- Compatibility with η 
    fst-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm (Σₒ X P) 𝑜)
      → fst-cns (η (Σₒ X P) f) ↦ η X (fst-frm f)
    {-# REWRITE fst-η #-}
    
    snd-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm (Σₒ X P) 𝑜)
      → snd-cns (η (Σₒ X P) f) ↦ η↓ P (snd-frm f)
    {-# REWRITE snd-η #-}

    pair-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜) (f↓ : Frm↓ P f)
      → pair-cns (η X f) (η↓ P f↓) ↦ η (Σₒ X P) (pair-frm f f↓)
    {-# REWRITE pair-η #-}

    -- Compaitbility with μ 
    fst-μ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {f : Frm (Σₒ X P) 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns (Σₒ X P) f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns (Σₒ X P) (Shp (Σₒ X P) c p) (𝑞 p))
      → fst-cns (μ (Σₒ X P) c d) ↦ μ X (fst-cns c) (λ p → fst-cns (d p))
    {-# REWRITE fst-μ #-}

    snd-μ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {f : Frm (Σₒ X P) 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns (Σₒ X P) f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns (Σₒ X P) (Shp (Σₒ X P) c p) (𝑞 p))
      → snd-cns (μ (Σₒ X P) c d) ↦ μ↓ P (snd-cns c) (λ p → snd-cns (d p))
    {-# REWRITE snd-μ #-}

    pair-μ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ P (Shp↓ P c↓ p) (d p))
      → pair-cns (μ X c d) (μ↓ P c↓ d↓) ↦
          μ (Σₒ X P) (pair-cns c c↓) (λ p → pair-cns (d p) (d↓ p))
    {-# REWRITE pair-μ #-}

  -- Implementations
  Σₒ {zero} X P = tt*
  Σₒ {suc n} (Xₙ , Xₛₙ) (Pₙ , Pₛₙ)  =
    Σₒ Xₙ Pₙ , λ f → Σ[ x ∈ Xₛₙ (fst-frm f) ] Pₛₙ (snd-frm f) x
  
  fst-frm {zero} f = tt*
  fst-frm {suc n} (f , x , c , y) =
    fst-frm f , fst x , fst-cns c , λ p → fst (y p)
  
  snd-frm {zero} f = tt*
  snd-frm {suc n} (f , x , c , y) =
    snd-frm f , snd x , snd-cns c , λ p → snd (y p)
  
  pair-frm {zero} f f↓ = tt*
  pair-frm {suc n} (f , x , c , y) (f↓ , x↓ , c↓ , y↓) =
    pair-frm f f↓ , (x , x↓) , pair-cns c c↓ , λ p → (y p , y↓ p)

  fst-cns {zero} c = tt*
  fst-cns {suc n} (lf (x , _)) = lf x
  fst-cns {suc n} {X = X} {P = P} (nd (x , x↓) c y d z ψ) =
    nd x (fst-cns c) (λ p → fst (y p))
         (λ p → fst-cns (d p)) (λ p q → fst (z p q))
         (λ p → fst-cns {suc n} {X = X} {P = P} (ψ p))
  
  snd-cns {zero} c = tt*
  snd-cns {suc n} (lf (_ , x↓)) = idp
  snd-cns {suc n} {X = X} {P = P} (nd (_ , x↓) c y d z ψ) =
    snd-cns c , (λ p → snd (y p)) ,
      (λ p → snd-cns (d p)) , (λ p q → snd (z p q)) ,
      (λ p → snd-cns {suc n} {X = X} {P = P} (ψ p)) , idp

  pair-cns {zero} c c↓ = tt*
  pair-cns {suc n} {f = f , x , ._ , ._} {f↓ = f↓ , x↓ , ._ , ._}
    (lf .x) idp = lf {f = pair-frm f f↓} (x , x↓)
  pair-cns {suc n} {X = X} {P} {f = f , x , ._ , ._} {f↓ = f↓ , x↓ , ._ , ._}
    (nd .x c y d z ψ) (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) = 
    nd {f = pair-frm f f↓} (x , x↓) (pair-cns c c↓) (λ p → (y p , y↓ p))
      (λ p → pair-cns (d p) (d↓ p)) (λ p q → (z p q , z↓ p q))
      (λ p → pair-cns {suc n} {X = X} {P} (ψ p) (ψ↓ p))
