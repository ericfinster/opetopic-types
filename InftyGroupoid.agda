{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Algebras

module InftyGroupoid where

  ∞Groupoid : Set₁
  ∞Groupoid = Σ (OpetopicType IdMnd) (is-fibrant)

  underlying : ∞Groupoid → Set  
  underlying (X , is-fib) = Ob X ttᵢ 


  -- module _ (A : Set) where

  --   open import IdentityMonadOver A

  --   XA : OpetopicType IdMnd
  --   XA = ↓-to-OpType IdMnd IdMnd↓

  --   unary-pd : (x y z : A) → Pd (Pb IdMnd (Idx↓ IdMnd↓)) (((ttᵢ , z) , (ttᵢ , cst x)))
  --   unary-pd x y z =
  --     nd (ttᵢ , cst y)
  --        (cst (ttᵢ , cst x))
  --        (cst (η (Slice (Pb IdMnd (Idx↓ IdMnd↓))) ((ttᵢ , y) , ttᵢ , cst x)))

  --   -- This should be the type of fillers of the 2-simplex
  --   2-simplex : {x y z : A} (p : x == y) (q : y == z) (r : x == z) → Set
  --   2-simplex {x} {y} {z} p q r =
  --     Ob (Hom (Hom XA))
  --       ((((ttᵢ , z) , (ttᵢ , cst x)) , (x , r) , ttᵢ , cst idp) ,
  --        unary-pd x y z ,
  --        λ { (inl tt)  → (y , q) , ttᵢ , cst idp ;
  --            (inr (ttᵢ , inl tt)) → (x , p) , ttᵢ , cst idp ;
  --            (inr (ttᵢ , inr ())) })

  module _ (A : Set) where

    open import IdentityMonadOver A

    postulate
    
      id-is-algebraic : is-algebraic IdMnd IdMnd↓
      -- id-is-algebraic ttᵢ ttᵢ ν = has-level-in (ctr , unique)

      --   where ctr : alg-comp IdMnd IdMnd↓ ttᵢ ttᵢ ν
      --         ctr = ⟦ ν ttᵢ ∣ ttᵢ ∣ λ= (λ { ttᵢ → idp }) ⟧ 

      --         unique : (α : alg-comp IdMnd IdMnd↓ ttᵢ ttᵢ ν) → ctr == α
      --         unique ⟦ a ∣ ttᵢ ∣ idp ⟧ = alg-comp-= IdMnd IdMnd↓ ttᵢ ttᵢ ν idp idp
      --           (λ { ttᵢ → {!!} })

    XA : OpetopicType IdMnd
    XA = ↓-to-OpType IdMnd IdMnd↓ 

    XA-is-fibrant : is-fibrant XA
    XA-is-fibrant = alg-is-fibrant IdMnd IdMnd↓
      id-is-algebraic

  to-∞Groupoid : Set → ∞Groupoid
  to-∞Groupoid A = XA A , XA-is-fibrant A


  
