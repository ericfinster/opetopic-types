--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicType
open import OpetopicFam 
open import OpetopicTerm
open import OpetopicSub

module Groupoid where

  Grp : ∀ {n ℓ} (X : Type ℓ) → 𝕆Fam (𝕋 n {ℓ}) ℓ
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

  data MultFill {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) 
    : {𝑜 : 𝒪 n} (f : Frm (fst (fst X)) 𝑜) → Type ℓ 


  data MultHom {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ)
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


  FreeMult : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (X∞ : 𝕆Type∞ ℓ Xₙ) → 𝕆Type∞ ℓ Xₙ
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

  is-mult-ctx : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  is-mult-ctx {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    (f : Frm Xₙ 𝑜) (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y)

  record is-mult-ext {n ℓ} {Xₙ : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ ℓ Xₙ) : Type ℓ where
    coinductive
    field
      fill-mult : is-mult-ctx ((Xₙ , Fill X∞) , Fill (Hom X∞))
      hom-mult : is-mult-ext (Hom X∞)

  open is-mult-ext

  -- Yikes.  This is slightly more complicated than expected.  You have
  -- to reconstruct the frame in X to multipy.  In principle seems like
  -- it could be done using y.  But we'll see...
  pf-is-mult : ∀ {n ℓ} {X : 𝕆Type n ℓ} {Y : 𝕆Type n ℓ}
    → (σ : X ⇒ Y) (X∞ : 𝕆Type∞ ℓ X)
    → is-mult-ext X∞ → is-mult-ext (Pf∞ σ X∞)
  fill-mult (pf-is-mult σ X∞ ϕ) f c y = (({!!} , {!!}) , {!!}) , {!!}
  hom-mult (pf-is-mult σ X∞ ϕ) =
    pf-is-mult (σ , (λ {𝑜} {f} x → (f , (λ _ → Frm⇒ σ f)) , x))
      (Hom X∞) (hom-mult ϕ)

  data UniqueFill {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) (ϕ : is-mult-ctx X)
    : {𝑜 : 𝒪 n} (f : Frm (fst (fst X)) 𝑜) → Type ℓ 

  data UniqueHom {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) (ϕ : is-mult-ctx X)
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
  
    in-unique-hom : {𝑜 : 𝒪 (suc n)} {φ : Frm (fst X) 𝑜}
      → (filler : snd X φ)
      → UniqueHom X ϕ (fst φ , in-unique-fill (fst (snd φ)) ,
          fst (snd (snd φ)) , λ p → in-unique-fill (snd (snd (snd φ)) p))

    fill-unique : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (fst (fst X)) 𝑜} (c : Cns (fst (fst X)) f 𝑝)
      → (y : (p : Pos 𝑝) → (snd (fst X)) (Shp (fst (fst X)) c p))
      → (x : UniqueFill X ϕ f) (α : UniqueHom X ϕ (f , x , c , λ p → in-unique-fill (y p)))
      → (λ i → UniqueHom X ϕ (f , comp-unique c y x α i , c , λ p → in-unique-fill (y p)))
          [ in-unique-hom (snd (ϕ f c y)) ≡ α ] 

  FreeUnique : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (X∞ : 𝕆Type∞ ℓ Xₙ) (ϕ : is-mult-ext X∞) → 𝕆Type∞ ℓ Xₙ
  Fill (FreeUnique Xₙ X∞ ϕ) = UniqueFill ((Xₙ , Fill X∞) , Fill (Hom X∞))  (fill-mult ϕ) 
  Fill (Hom (FreeUnique Xₙ X∞ ϕ)) = UniqueHom ((Xₙ , Fill X∞) , Fill (Hom X∞))  (fill-mult ϕ) 
  Hom (Hom (FreeUnique {n} Xₙ X∞ ϕ)) = 
    FreeUnique ((Xₙ , UniqueFill ((Xₙ , Fill X∞) , Fill (Hom X∞)) (fill-mult ϕ)) ,
                    UniqueHom ((Xₙ , Fill X∞) , Fill (Hom X∞)) (fill-mult ϕ))
            ((Pf∞ ((id-sub Xₙ , in-unique-fill) , in-unique-hom) (Hom (Hom X∞))))
            (pf-is-mult ((id-sub Xₙ , in-unique-fill) , in-unique-hom) (Hom (Hom X∞)) (hom-mult (hom-mult ϕ)))

  --
  --  Fuck yeah!  A whole day but I got it!
  --

  Skeleton : ∀ {ℓ} (X : 𝕆Type∞ ℓ tt*)
    → (n : ℕ) → 𝕆Type n ℓ

  SkeletonExt : ∀ {ℓ} (X : 𝕆Type∞ ℓ tt*)
    → (n : ℕ) → 𝕆Type∞ ℓ (Skeleton X n) 

  Skeleton X zero = lift tt
  Skeleton X (suc n) = Skeleton X n , Fill (SkeletonExt X n)

  SkeletonExt X zero = X
  SkeletonExt X (suc n) = Hom (SkeletonExt X n)

  FreeGrp : ∀ {ℓ} (X : 𝕆Type∞ ℓ tt*)
    → (n : ℕ) → 𝕆Type n ℓ 

  FreeInc : ∀ {ℓ} (X : 𝕆Type∞ ℓ tt*)
    → (n : ℕ) → Skeleton X n ⇒ FreeGrp X n 

  data FreeCell {ℓ} (X : 𝕆Type∞ ℓ tt*) : {n : ℕ} {𝑜 : 𝒪 n} (f : Frm (FreeGrp X n) 𝑜) → Type ℓ 

  FreeGrp X zero = lift tt
  FreeGrp X (suc n) = FreeGrp X n , FreeCell X

  data FreeCell {ℓ} X where

    free-in : {n : ℕ} {𝑜 : 𝒪 n} {f : Frm (Skeleton X n) 𝑜}
      → (x : Fill (SkeletonExt X n) f)
      → FreeCell X (Frm⇒ (FreeInc X n) f)

    free-comp : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (FreeGrp X n) 𝑜} (c : Cns (FreeGrp X n) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (FreeGrp X n) c p))
      → FreeCell X f 

    free-fill : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (FreeGrp X n) 𝑜} (c : Cns (FreeGrp X n) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (FreeGrp X n) c p))
      → FreeCell X {suc n} {𝑜 , 𝑝} (f , free-comp c y , c , y)

    free-comp-unique : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (FreeGrp X n) 𝑜} (c : Cns (FreeGrp X n) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (FreeGrp X n) c p))
      → (x : FreeCell X f) (α : FreeCell X (f , x , c , y))
      → free-comp c y ≡ x

    free-fill-unique : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (FreeGrp X n) 𝑜} (c : Cns (FreeGrp X n) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (FreeGrp X n) c p))
      → (x : FreeCell X f) (α : FreeCell X (f , x , c , y))
      → (λ i → FreeCell X (f , free-comp-unique c y x α i , c , y))
          [ free-fill c y ≡ α ] 

  FreeInc X zero = tt*
  FreeInc X (suc n) = FreeInc X n , free-in
