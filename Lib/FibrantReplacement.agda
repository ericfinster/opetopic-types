--
--  FibrantReplacement.agda - Consructing the Fibrant Replacement of an Opetopic Type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.Everything

module Lib.FibrantReplacement where

  --
  --  Fuck yeah!  A whole day but I got it!
  --

  Skeleton : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type n ℓ

  SkeletonExt : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type∞ {ℓ = ℓ} (Skeleton X n) 

  Skeleton X zero = lift tt
  Skeleton X (suc n) = Skeleton X n , Fill (SkeletonExt X n)

  SkeletonExt X zero = X
  SkeletonExt X (suc n) = Hom (SkeletonExt X n)

  FreeGrp : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type n ℓ 

  FreeInc : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → Skeleton X n ⇒ FreeGrp X n 

  data FreeCell {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*) : {n : ℕ} {𝑜 : 𝒪 n} (f : Frm (FreeGrp X n) 𝑜) → Type ℓ 

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
      → FreeCell X {suc n} {𝑜 ∣ 𝑝} (f , free-comp c y , c , y)

    free-comp-unique : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (FreeGrp X n) 𝑜} (c : Cns (FreeGrp X n) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (FreeGrp X n) c p))
      → (x : FreeCell X f) (α : FreeCell X {𝑜 = 𝑜 ∣ 𝑝} (f , x , c , y))
      → free-comp c y ≡ x

    free-fill-unique : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm (FreeGrp X n) 𝑜} (c : Cns (FreeGrp X n) f 𝑝)
      → (y : (p : Pos 𝑝) → FreeCell X (Shp (FreeGrp X n) c p))
      → (x : FreeCell X f) (α : FreeCell X {𝑜 = 𝑜 ∣ 𝑝} (f , x , c , y))
      → (λ i → FreeCell X {𝑜 = 𝑜 ∣ 𝑝} (f , free-comp-unique c y x α i , c , y))
          [ free-fill c y ≡ α ] 

  FreeInc X zero = tt*
  FreeInc X (suc n) = FreeInc X n , free-in
