--
--  NaturalTransform.agda - Natural Transformations of ∞-Functors
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum
open import Cubical.Data.Bool

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures
open import Experimental.NoDecs.CartesianProduct

module Experimental.NoDecs.NaturalTransform where

𝕀∞ : 𝕆Type∞ (𝕋 {ℓ-zero} 0)
Fill 𝕀∞ = λ _ → Bool
Fill (Hom 𝕀∞) (_ , x , y) = x ≤ y
Hom (Hom 𝕀∞) = 𝕋Ext _

≤-trans : {x y z : Bool} → x ≤ y → y ≤ z → x ≤ z
≤-trans {false} {y} {z} _ _ = tt
≤-trans {true} {true} {true} _ _ = tt

≤-src : {x y : Bool} (s : Src (Fill (Hom 𝕀∞)) (_ , x , y)) → x ≤ y
≤-src (lf false) = tt
≤-src (lf true) = tt
≤-src (nd tgt brs flr) = ≤-trans (≤-src (br brs)) flr

is∞cat𝕀 : is-fibrant-ext (Hom 𝕀∞)
fill-fib is∞cat𝕀 _ s = isContrΣ (≤-src s , isProp≤ _ _ _) (λ _ → tt* , λ _ → refl)
hom-fib is∞cat𝕀 = is-fib-ext-𝕋Ext

NatTrans : (X Y : 𝕆Type∞ (𝕋 {ℓ-zero} 0)) → Type
NatTrans X Y = Map tt* (prod∞ X 𝕀∞) Y
