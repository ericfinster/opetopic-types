open import Cubical.Foundations.Everything

open import Core.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Core.OpetopicType
open import Lib.Terminal

module Lib.Opetopes where

  --
  --  Some opetopes 
  --
  
  𝒪 : ℕ → Type
  𝒪 n = Frm (𝕋 n) 

  𝒫 : ∀ {n} → 𝒪 n → Type
  𝒫 o = Src (const Unit*) o 

  Posₒ : ∀ {n} → (𝑜 : 𝒪 n) → 𝒫 𝑜 → Type
  Posₒ 𝑜 𝑝 = Pos (const Unit*) {f = 𝑜} 𝑝
  
  Typₒ : ∀ {n} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) → Posₒ 𝑜 𝑝 → 𝒪 n
  Typₒ {𝑜 = 𝑜} 𝑝 p = Typ (const Unit*) {f = 𝑜} 𝑝 p 

  obj : 𝒪 0
  obj = tt*

  arr : 𝒪 1
  arr = tt* , tt* , tt*

  drop : 𝒪 2
  drop = arr , lf tt* , tt*

  2-globe : 𝒪 2
  2-globe = arr , lf tt* , tt* 

