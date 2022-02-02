--
--  OpetopicMap.agda - Maps of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicSub

module OpetopicStructures where

  is-fibrant-ctx : ∀ {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) → Type ℓ
  is-fibrant-ctx {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    (f : Frm Xₙ 𝑜) (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → isContr (Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y))

  record is-fibrant-ext {n ℓ} {Γ : 𝕆Ctx n ℓ} (Γ∞ : 𝕆Ctx∞ ℓ Γ) : Type ℓ where
    coinductive
    field
      fill-fib : is-fibrant-ctx ((Γ , Fill Γ∞) , Fill (Hom Γ∞))
      hom-fib : is-fibrant-ext (Hom Γ∞)

  ∞-Groupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞-Groupoid ℓ = Σ[ X ∈ 𝕆Ctx∞ ℓ (𝕋 0) ] is-fibrant-ext X

  ∞-Category : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞-Category ℓ = Σ[ X ∈ 𝕆Ctx∞ ℓ (𝕋 0) ] is-fibrant-ext (Hom X)

  A∞-space : (ℓ : Level) → Type (ℓ-suc ℓ)
  A∞-space ℓ = Σ[ X ∈ 𝕆Ctx∞ ℓ (𝕋 1) ] is-fibrant-ext X

  ∞-Planar-Operad : (ℓ : Level) → Type (ℓ-suc ℓ)
  ∞-Planar-Operad ℓ = Σ[ X ∈ 𝕆Ctx∞ ℓ (𝕋 2) ] is-fibrant-ext X

  --
  --  The free ∞-category construction
  --

  postulate

    FreeInfCat : ∀ {ℓ} → 𝕆Ctx∞ ℓ tt* → 𝕆Ctx∞ ℓ tt*
    
    freeIn : ∀ {ℓ} (X : 𝕆Ctx∞ ℓ tt*) → [ X ⇒ FreeInfCat X ↓ tt* ]
    
    freeIsCat : ∀ {ℓ} (X : 𝕆Ctx∞ ℓ tt*)
      → is-fibrant-ext (Hom (FreeInfCat X))
  
    -- And now we need the elimination principle ... for this we need to say
    -- what a dependent ∞-category is, and moreover define the action of
    -- substitutions on terms.


