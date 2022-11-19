{-# OPTIONS --cubical --no-import-sorts --rewriting --guardedness #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Core.OpetopicType
open import Core.OpetopicMap
open import Core.Opetopes
open import Lib.Structures
open is-fibrant-ext

module Experimental.infcat {ℓ : Level} (C : ∞-Category ℓ) where
  Carrier : Type ℓ
  Carrier = fst C .Fill tt*

  hom : Carrier → Carrier → Type ℓ
  hom x y = fst C .Hom .Fill {o = arrow} (tt* , x , tt* , λ _ → y)

  Id : (x : Carrier) → hom x x
  Id x = snd C .fill-fib {𝑜 = arrow} {𝑝 = lfₒ} {f = (tt* , x , tt* , λ _ → x)}
    (lf x) (λ ()) .fst .fst

  Comp : {x y z : Carrier} → hom y z → hom x y → hom x z
  Comp {x} {y} {z} g f = snd C .fill-fib {𝑜 = arrow} {𝑝 = n-path 2} {f = (tt* , x , tt* , λ _ → z)}
    {!!} -- (nd x tt* (λ _ → y) (λ _ → tt*) (λ _ _ → z) (λ _ → nd y tt* (λ _ → z) (λ _ → tt*) (λ _ _ → z) (λ _ → lf z)))
    {!!}
    .fst .fst
    
