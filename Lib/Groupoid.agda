--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.Everything
open import Lib.Structures

module Lib.Groupoid where

  Grp : ∀ {ℓ} (X : Type ℓ) → (n : ℕ) → 𝕆Type n ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → El (Grp X n)

  data GrpCell {n ℓ} (X : Type ℓ) : {𝑜 : 𝒪 n}  → Frm (Grp X n) 𝑜 → Type ℓ where
    reflₒ : (x : X) (𝑜 : 𝒪 n) → GrpCell X (Frm-El (Pt x) 𝑜)

  Grp X zero = tt*
  Grp X (suc n) = Grp X n , GrpCell X

  Pt {zero} x = tt*
  Pt {suc n} x = Pt {n} x , reflₒ x

  --
  --  Fibrancy? 
  --

  thm : ∀ {n ℓ} (X : Type ℓ) → is-fibrant (Grp X (suc (suc n)))
  thm {zero} X {𝑜} {𝑝} {f} c y with y tt
  thm {zero} X {tt} {tt} {tt*} tt* y | reflₒ x .tt =
    -- Well, anyway, fundamental theorem....
    (reflₒ x tt , {!reflₒ x (tt , tt)!}) , {!!}
  thm {suc n} X (lf (reflₒ x 𝑜)) ν =
    (reflₒ x (𝑜 , ηₒ 𝑜) , {!reflₒ x ((𝑜 , ηₒ 𝑜) , lfₒ)!}) , {!!}
  thm {suc n} X (nd x c y d z ψ) ν = {!!}

  -- is-fibrant : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  -- is-fibrant {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
  --   {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
  --   {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
  --   (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
  --   → isContr (Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y))

