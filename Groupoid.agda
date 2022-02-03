--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType
open import OpetopicTerm
open import OpetopicSub

module Groupoid where

  Grp : ∀ {n ℓ} (X : Type ℓ) → 𝕆Type (𝕋 n {ℓ}) ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕆Term {n} (Grp X)

  -- The extra units make this sloppy, but okay ...
  data 𝕆Id {n ℓ} (X : Type ℓ) : {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜}
    → Frm↓ (Grp X) f → Lift Unit → Type ℓ where
    op-refl : (x : X) {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜} (γ : Lift Unit)
      → 𝕆Id X (Frm-Tm (Pt x) f) γ

  Grp {zero} X = lift tt
  Grp {suc n} X =
    Grp {n} X , 𝕆Id X

  Pt {zero} x = lift tt
  Pt {suc n} x = Pt {n} x , op-refl x

  --
  --  The free multiplicative extension associated to an opetopic type
  --

  data MultFill {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) 
    : {𝑜 : 𝒪 n} (f : Frm (fst (fst X)) 𝑜) → Type ℓ 


  data MultHom {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ)
    : {𝑜 : 𝒪 (suc n)} (f : Frm (fst (fst X) , MultFill X) 𝑜) → Type ℓ 


  data MultFill {n ℓ} X where

    in-fill : {𝑜 : 𝒪 n} {f : Frm (fst (fst X)) 𝑜}
      → (x : (snd (fst X)) f)
      → MultFill X f 

    mult-comp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → MultFill X (Shp (fst (fst X)) c p))
      → MultFill X f


  data MultHom {n ℓ} X where

    in-hom : {𝑜 : 𝒪 (suc n)} {φ : Frm (fst X) 𝑜}
      → (filler : snd X φ)
      → MultHom X (fst φ , in-fill (fst (snd φ)) ,
                    fst (snd (snd φ)) , λ p → in-fill (snd (snd (snd φ)) p))

    mult-fill : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → MultFill X (Shp (fst (fst X)) c p))
      → MultHom X (f , mult-comp c y , c , y)


  FreeMult : ∀ {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ) → 𝕆Ctx∞ ℓ Xₙ
  Fill (FreeMult Xₙ X∞) = MultFill ((Xₙ , Fill X∞) , Fill (Hom X∞)) 
  Fill (Hom (FreeMult Xₙ X∞)) = MultHom ((Xₙ , Fill X∞) , Fill (Hom X∞)) 
  Hom (Hom (FreeMult {n} Xₙ X∞)) = 
    FreeMult ((Xₙ , MultFill ((Xₙ , Fill X∞) , Fill (Hom X∞))) ,
                    MultHom ((Xₙ , Fill X∞) , Fill (Hom X∞)))
            ((Pf∞ ((id-sub Xₙ , in-fill) , in-hom) (Hom (Hom X∞)))) 


  --
  --  The free uniquely multiplicative context associated to
  --  a multiplicative one
  --

  is-mult-ctx : ∀ {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) → Type ℓ
  is-mult-ctx {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    (f : Frm Xₙ 𝑜) (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y)


  data UniqueFill {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) (ϕ : is-mult-ctx X)
    : {𝑜 : 𝒪 n} (f : Frm (fst (fst X)) 𝑜) → Type ℓ 


  data UniqueHom {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) (ϕ : is-mult-ctx X)
    : {𝑜 : 𝒪 (suc n)} (f : Frm (fst (fst X) , UniqueFill X ϕ) 𝑜) → Type ℓ 


  data UniqueFill {n ℓ} X ϕ where

    in-unique-fill : {𝑜 : 𝒪 n} {f : Frm (fst (fst X)) 𝑜}
      → (x : (snd (fst X)) f)
      → UniqueFill X ϕ f 

    comp-unique : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → (snd (fst X)) (Shp (fst (fst X)) c p))
      → (x : UniqueFill X ϕ f) (α : UniqueHom X ϕ (f , x , c , λ p → in-unique-fill (y p)))
      → in-unique-fill (fst (ϕ f c y)) ≡ x

  data UniqueHom {n ℓ} X ϕ where
  
    in-hom : {𝑜 : 𝒪 (suc n)} {φ : Frm (fst X) 𝑜}
      → (filler : snd X φ)
      → UniqueHom X ϕ (fst φ , in-unique-fill (fst (snd φ)) ,
          fst (snd (snd φ)) , λ p → in-unique-fill (snd (snd (snd φ)) p))

    fill-unique : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → (snd (fst X)) (Shp (fst (fst X)) c p))
      → (x : UniqueFill X ϕ f) (α : UniqueHom X ϕ (f , x , c , λ p → in-unique-fill (y p)))
      → (λ i → UniqueHom X ϕ (f , comp-unique c y x α i , c , λ p → in-unique-fill (y p)))
          [ in-hom (snd (ϕ f c y)) ≡ α ] 

  -- FreeUnique : ∀ {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ) → 𝕆Ctx∞ ℓ Xₙ
  -- Fill (FreeUnique Xₙ X∞) = UniqueFill ((Xₙ , Fill X∞) , Fill (Hom X∞)) 
  -- Fill (Hom (FreeUnique Xₙ X∞)) = UniqueHom ((Xₙ , Fill X∞) , Fill (Hom X∞)) 
  -- Hom (Hom (FreeUnique {n} Xₙ X∞)) = 
  --   FreeUnique ((Xₙ , UniqueFill ((Xₙ , Fill X∞) , Fill (Hom X∞))) ,
  --                   UniqueHom ((Xₙ , Fill X∞) , Fill (Hom X∞)))
  --           ((Pf∞ ((id-sub Xₙ , in-fill) , in-hom) (Hom (Hom X∞)))) 
