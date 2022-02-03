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
  --  The free ∞-groupoid associated to an opetopic type
  --

  data FreeCell {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) 
    : {𝑜 : 𝒪 n} (f : Frm (fst (fst X)) 𝑜) → Type ℓ 


  data FreeFill {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ)
    : {𝑜 : 𝒪 (suc n)} (f : Frm (fst (fst X) , FreeCell X) 𝑜) → Type ℓ 


  data FreeCell {n ℓ} X where

    free-cell-in : {𝑜 : 𝒪 n} {f : Frm (fst (fst X)) 𝑜}
      → (x : (snd (fst X)) f)
      → FreeCell X f 

    comp-in : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (fst (fst X)) c p))
      → FreeCell X f

    comp-unique : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (fst (fst X)) c p))
      → (x : FreeCell X f) (α : FreeFill X (f , x , c , y))
      → comp-in c y ≡ x 

  data FreeFill {n ℓ} X where

    free-fill-in : {𝑜 : 𝒪 (suc n)} (φ : Frm (fst X) 𝑜)
      → FreeFill X (fst φ , free-cell-in (fst (snd φ)) ,
                    fst (snd (snd φ)) , λ p → free-cell-in (snd (snd (snd φ)) p))

    fill-in : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (fst (fst X)) c p))
      → FreeFill X (f , comp-in c y , c , y)

    fill-unique : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (fst (fst X)) c p))
      → (x : FreeCell X f) (α : FreeFill X (f , x , c , y))
      → (λ i → FreeFill X (f , comp-unique c y x α i , c , y)) [ fill-in c y ≡ α ] 

  -- is-fibrant-ctx : ∀ {n ℓ} (X : 𝕆Ctx (suc (suc n)) ℓ) → Type ℓ
  -- is-fibrant-ctx {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
  --   {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
  --   (f : Frm Xₙ 𝑜) (c : Cns Xₙ f 𝑝)
  --   (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
  --   → isContr (Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y))
  
  -- FreeGrp : ∀ {ℓ} (X : 𝕆Ctx∞ ℓ tt*)
  --   → (n : ℕ) → 𝕆Ctx n ℓ 

  -- inc⇒ : ∀ {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ)
  --   → [ X∞ ⇒ FreeGrp Xₙ X∞ ↓ {!!} ] -- id sub 
    

  -- FreeGrp X n = {!!} 

  -- Or maybe the frames and fillers need to be two separate definitions.
  -- Or maybe it gets unfolded somehow ....

  -- What if 

  -- FreeGrp : ∀ {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ) → 𝕆Ctx∞ ℓ Xₙ

  -- data FreeCell {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ)
  --   : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ where

  -- data FreeFill {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ)
  --   : {𝑜 : 𝒪 (suc n)} (f : Frm (Xₙ , FreeCell Xₙ X∞) 𝑜) → Type ℓ where

  -- -- Maybe if you destruct one more time, you can use the other Frm∞ constructor? 
  -- Fill (FreeGrp Xₙ X∞) = FreeCell Xₙ {!FreeGrp (Xₙ , Fill X∞) (Hom X∞)!}
  -- Hom (FreeGrp Xₙ X∞) = {!FreeGrp (Xₙ , Fill X∞) (Hom X∞)!}

  -- --
  -- --  Opetope and Context extensions Frame 
  -- --

  -- data 𝒪Ext : {n : ℕ} (𝑜 : 𝒪 n) → ℕ → Type where
  --   here : {n : ℕ} (𝑜 : 𝒪 n) → 𝒪Ext 𝑜 zero
  --   there : {n : ℕ} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  --     → {k : ℕ} (e : 𝒪Ext (𝑜 , 𝑝) k)
  --     → 𝒪Ext 𝑜 (suc k) 
  
  -- Frm∞ : ∀ {n ℓ} (Xₙ : 𝕆Ctx n ℓ) (X∞ : 𝕆Ctx∞ ℓ Xₙ)
  --   → {𝑜 : 𝒪 n} 
  --   → {k : ℕ} (e : 𝒪Ext 𝑜 k) → Type ℓ 
  -- Frm∞ {n} Xₙ X∞ (here 𝑜) = Frm Xₙ 𝑜
  -- Frm∞ {n} Xₙ X∞ (there 𝑜 𝑝 e) = Frm∞ (Xₙ , Fill X∞) (Hom X∞) e


  -- Skeleton : ∀ {ℓ} (X : 𝕆Ctx∞ ℓ tt*)
  --   → (n : ℕ) → 𝕆Ctx n ℓ
  -- Skeleton X zero = lift tt
  -- Skeleton X (suc n) = Skeleton X n , {!!}
