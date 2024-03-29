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

  -- Action on Constructors
  fst-cns : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm (Σₒ X P) 𝑜}
    → Cns (Σₒ X P) f 𝑝 → Cns X (fst-frm f) 𝑝

  snd-cns : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm (Σₒ X P) 𝑜}
    → (c : Cns (Σₒ X P) f 𝑝) → Cns↓ P (snd-frm f) (fst-cns c)

  record Σ-cell {n ℓ₀ ℓ₁} {Xₙ  : 𝕆Type n ℓ₀} {Pₙ  : 𝕆Fam Xₙ ℓ₁}
    (Xₛₙ : {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ₀)
    (Pₛₙ : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} → Frm↓ Pₙ f → Xₛₙ f → Type ℓ₁)
    {𝑜 : 𝒪 n} (f : Frm (Σₒ Xₙ Pₙ) 𝑜) : Type (ℓ-max ℓ₀ ℓ₁) where
    constructor _,_ 
    field
    
      fstₒ : Xₛₙ (fst-frm f)
      sndₒ : Pₛₙ (snd-frm f) fstₒ 

  open Σ-cell public
  
  postulate
  
    -- Calculation of shapes
    fst-shp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (f : Frm (Σₒ X P) 𝑜)
      → (c : Cns (Σₒ X P) f 𝑝) (p : Pos 𝑝)
      → Shp X (fst-cns c) p ↦ fst-frm (Shp (Σₒ X P) c p) 
    {-# REWRITE fst-shp #-}
    
    snd-shp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (f : Frm (Σₒ X P) 𝑜)
      → (c : Cns (Σₒ X P) f 𝑝) (p : Pos 𝑝)
      → Shp↓ P (snd-cns c) p ↦ snd-frm (Shp (Σₒ X P) c p) 
    {-# REWRITE snd-shp #-} 

    -- Compatibility with η 
    fst-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm (Σₒ X P) 𝑜)
      → fst-cns (η (Σₒ X P) f) ↦ η X (fst-frm f)
    {-# REWRITE fst-η #-}
    
    snd-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm (Σₒ X P) 𝑜)
      → snd-cns (η (Σₒ X P) f) ↦ η↓ P (snd-frm f)
    {-# REWRITE snd-η #-}

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

  -- Implementations
  Σₒ {zero} X P = tt*
  Σₒ {suc n} (Xₙ , Xₛₙ) (Pₙ , Pₛₙ)  =
    Σₒ Xₙ Pₙ , Σ-cell Xₛₙ Pₛₙ

  fst-frm {𝑜 = ●} f = tt*
  fst-frm {𝑜 = 𝑜 ∣ 𝑝} (f , x , c , y) = 
    fst-frm f , fstₒ x , fst-cns c , λ p → fstₒ (y p)

  snd-frm {𝑜 = ●} f = tt*
  snd-frm {𝑜 = 𝑜 ∣ 𝑝} (f , x , c , y) = 
    snd-frm f , sndₒ x , snd-cns c , λ p → sndₒ (y p)

  fst-cns {𝑜 = ●} c = tt*
  fst-cns {𝑜 = 𝑜 ∣ ._} {𝑝 = lfₒ} (lf x) = lf (fstₒ x)
  fst-cns {𝑜 = 𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd x c y d z ψ) = 
    nd (fstₒ x) (fst-cns c) (λ p → fstₒ (y p))
         (λ p → fst-cns (d p)) (λ p q → fstₒ (z p q))
         (λ p → fst-cns (ψ p))

  snd-cns {𝑜 = ●} c = tt*
  snd-cns {𝑜 = 𝑜 ∣ ._} {𝑝 = lfₒ} (lf x) = lf↓ (sndₒ x)
  snd-cns {𝑜 = 𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd x c y d z ψ) = 
    nd↓ (sndₒ x) (snd-cns c) (λ p → sndₒ (y p))
        (λ p → snd-cns (d p)) (λ p q → sndₒ (z p q))
        (λ p → snd-cns (ψ p)) 

  --
  --  Pairing 
  --

  pair-frm : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜) (f↓ : Frm↓ P f)
    → Frm (Σₒ X P) 𝑜 

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

    -- Compatibility with Shape

    pair-shp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → (c : Cns X f 𝑝) (c↓ : Cns↓ P f↓ c) (p : Pos 𝑝)
      → Shp (Σₒ X P) (pair-cns c c↓) p ↦ pair-frm (Shp X c p) (Shp↓ P c↓ p) 
    {-# REWRITE pair-shp #-}

    -- pair-shp-exp : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
    --   → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (f : Frm (Σₒ X P) 𝑜)
    --   → (c : Cns (Σₒ X P) f 𝑝) (p : Pos 𝑝)
    --   → Shp (Σₒ X P) c p  ↦ pair-frm (Shp X (fst-cns c) p) (Shp↓ P (snd-cns c) p)
    -- {-# REWRITE pair-shp-exp #-} 

    -- Compatibility with monad operations
    pair-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜) (f↓ : Frm↓ P f)
      → pair-cns (η X f) (η↓ P f↓) ↦ η (Σₒ X P) (pair-frm f f↓)
    {-# REWRITE pair-η #-}

    pair-μ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {P : 𝕆Fam X ℓ₁}
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ P (Shp↓ P c↓ p) (d p))
      → pair-cns (μ X c d) (μ↓ P c↓ d↓) ↦
          μ (Σₒ X P) (pair-cns c c↓) (λ p → pair-cns (d p) (d↓ p))
    {-# REWRITE pair-μ #-}

  pair-frm {𝑜 = ●} f f↓ = tt*
  pair-frm {𝑜 = 𝑜 ∣ 𝑝} (f , x , c , y) (f↓ , x↓ , c↓ , y↓) = 
    pair-frm f f↓ , (x , x↓) , pair-cns c c↓ , λ p → (y p , y↓ p)

  pair-cns {𝑜 = ●} c c↓ = tt*
  pair-cns {𝑜 = 𝑜 ∣ ._} {𝑝 = lfₒ} (lf x) (lf↓ x↓) = lf (x , x↓)
  pair-cns {𝑜 = 𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd x c y d z ψ) (nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓) = 
    nd (x , x↓) (pair-cns c c↓) (λ p → (y p , y↓ p))
      (λ p → pair-cns (d p) (d↓ p)) (λ p q → (z p q , z↓ p q))
      (λ p → pair-cns (ψ p) (ψ↓ p))

  --
  --  Testing ...
  --
  


