--
--  OpetopicStructures.agda - Definitions of various structures
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat

open import Core.Everything

module Lib.Structures where

  is-fibrant : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  is-fibrant {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → isContr (Σ[ x ∈ Xₛₙ f ] Xₛₛₙ {𝑜 ∣ 𝑝} (f , x , c , y))

  record is-fibrant-ext {n ℓ} {Γ : 𝕆Type n ℓ} (Γ∞ : 𝕆Type∞ Γ) : Type ℓ where
    coinductive
    field
      fill-fib : is-fibrant ((Γ , Fill Γ∞) , Fill (Hom Γ∞))
      hom-fib : is-fibrant-ext (Hom Γ∞)

  ∞-Groupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞-Groupoid ℓ = Σ[ X ∈ 𝕆Type∞ (𝕋 0) ] is-fibrant-ext X

  ∞-Category : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞-Category ℓ = Σ[ X ∈ 𝕆Type∞ (𝕋 0) ] is-fibrant-ext (Hom X)

  A∞-space : (ℓ : Level) → Type (ℓ-suc ℓ)
  A∞-space ℓ = Σ[ X ∈ 𝕆Type∞ (𝕋 1) ] is-fibrant-ext X

  ∞-Planar-Operad : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞-Planar-Operad ℓ = Σ[ X ∈ 𝕆Type∞ (𝕋 2) ] is-fibrant-ext X

  --  Composition Structures
  composition-structure : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  composition-structure {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → Σ[ x ∈ Xₛₙ f ] Xₛₛₙ {𝑜 ∣ 𝑝} (f , x , c , y)

  -- Uniquely composable, aka fibrant, types
  uniqueness-structure : ∀ {n ℓ} {X : 𝕆Type (suc (suc n)) ℓ}
    → composition-structure X → Type ℓ 
  uniqueness-structure {n} {X = (Xₙ , Xₛₙ) , Xₛₛₙ} ϕ =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    (cmp : Xₛₙ f) (fill : Xₛₛₙ (f , cmp , c , y))
    → (cmp , fill) ≡ ϕ c y
