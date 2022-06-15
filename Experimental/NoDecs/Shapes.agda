--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty 
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType 

module Experimental.NoDecs.Shapes where

  module _ {ℓ} (X₀ : 𝕆Type 1 ℓ) where

    Obj : Type ℓ
    Obj = snd X₀ tt* 

    module _ (X₁ : Frm X₀ → Type ℓ) where

      Hom : Obj → Obj → Type ℓ
      Hom x y = X₁ (tt* , x , y)

      module _ (X₂ : Frm (X₀ , X₁) → Type ℓ) where

        Null : (x : Obj) (f : Hom x x) → Type ℓ
        Null x f = X₂ ((tt* , x , x) , lf x , f)

        2Glob : {x y : Obj} (f g : Hom x y) → Type ℓ
        2Glob {x} {y} f g = X₂ ((tt* , x , y) , nd y [ x , x , lf x ] f , g)

        Simplex : {x y z : Obj} (f : Hom x y) (g : Hom y z) (h : Hom x z) → Type ℓ
        Simplex {x} {y} {z} f g h = X₂ ((tt* , x , z) , nd z [ y , x , nd y [ x , x , lf x ] f ] g , h) 
        
