--
--  Representables.agda - a fresh take on representables
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Terminal
open import Experimental.Local.Opetopes

module Experimental.Local.Representables where

  Stem : ∀ {n} (𝑜 : 𝒪 n) → 𝒫 𝑜 → 𝕆Type n ℓ-zero
  
  Horn : ∀ {n} → 𝒪 n → 𝕆Type n ℓ-zero
  Bdry : ∀ {n} → 𝒪 n → 𝕆Type n ℓ-zero

  incl : ∀ {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) (p : Posₒ 𝑜 𝑝) → Bdry (Typₒ 𝑝 p) ⇒ Stem 𝑜 𝑝

  data StemCell {n} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) (𝑞 : 𝒫 (𝑜 , 𝑝 , tt*)) : Frm (Stem 𝑜 𝑝) → Type where

    ext : (p : Posₒ 𝑜 𝑝) → StemCell 𝑜 𝑝 𝑞 (Frm⇒ (incl 𝑜 𝑝 p) {!!})
    int : (p : Posₒ (𝑜 , 𝑝 , tt*) 𝑞) → StemCell 𝑜 𝑝 𝑞 {!fst (incl (𝑜 , 𝑝 , tt*) 𝑞 p)!}

  Stem {zero} 𝑜 𝑝 = tt*
  Stem {suc n} (𝑜 , 𝑝 , tt*) 𝑞 = Stem 𝑜 𝑝 , StemCell 𝑜 𝑝 𝑞

  Horn {zero} 𝑜 = tt*
  Horn {suc n} (𝑜 , 𝑝 , tt*) = Stem 𝑜 𝑝 , {!!} 

  Bdry {zero} 𝑜 = tt*
  Bdry {suc n} (𝑜 , 𝑝 , tt*) = Stem 𝑜 𝑝 , {!!} 

  incl = {!!} 




  -- Repr : ∀ {n} → 𝒪 n → 𝕆Type (suc n) ℓ-zero
  -- Repr {zero} tt* = tt* , const Unit
  -- Repr {suc zero} (tt* , tt* , tt*) = {!!}
  -- Repr {suc (suc n)} ((𝑜 , 𝑝 , tt*) , 𝑞 , tt*) = {!!}
