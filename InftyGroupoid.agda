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

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    Plbk : 𝕄
    Plbk = Pb M (Idx↓ M↓)

    Plbk↓ : 𝕄↓ Plbk
    Plbk↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)
    
    Slc : 𝕄
    Slc = Slice Plbk

    Slc↓ : 𝕄↓ Slc
    Slc↓ = Slice↓ Plbk↓

    postulate

      slc-algebraic : is-algebraic Slc Slc↓
    
    alg-to-idx↓ : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → alg-comp M M↓ i c ν ≃ Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν)))
    alg-to-idx↓ i c ν = equiv to from to-from from-to

      where to : alg-comp M M↓ i c ν → Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν)))
            to ⟦ j ∣ d ∣ τ ⟧ = j , (j , idp) , d , app= τ

            from : Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν))) → alg-comp M M↓ i c ν
            from (j , (.j , idp) , d , τ) = ⟦ j ∣ d ∣ λ= τ ⟧

            to-from : (x : Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν))))
              → to (from x) == x
            to-from (j , (.j , idp) , d , τ) =
              ap (λ x → j , (j , idp) , d , x) (λ= (λ p → app=-β τ p))

            from-to : (x : alg-comp M M↓ i c ν)
              → from (to x) == x
            from-to ⟦ j ∣ d ∣ τ ⟧ = ap (λ x → ⟦ j ∣ d ∣ x ⟧) (! (λ=-η τ)) 
            
    alg-mnd-has-unique-action : is-algebraic M M↓
      → unique-action M (Idx↓ M↓) (Idx↓ Slc↓) 
    alg-mnd-has-unique-action is-alg i c ν =
      equiv-preserves-level (alg-to-idx↓ i c ν) ⦃ is-alg i c ν ⦄ 

  alg-is-fibrant : (M : 𝕄) (M↓ : 𝕄↓ M)
    → is-algebraic M M↓
    → is-fibrant (↓-to-OpType M M↓)
  base-fibrant (alg-is-fibrant M M↓ is-alg) =
    alg-mnd-has-unique-action M M↓ is-alg
  hom-fibrant (alg-is-fibrant M M↓ is-alg) =
    alg-is-fibrant (Slc M M↓) (Slc↓ M M↓) (slc-algebraic M M↓)


  module _ (A : Set) where

    open import IdentityMonadOver A

    XA : OpetopicType IdMnd
    XA = ↓-to-OpType IdMnd IdMnd↓

    unary-pd : (x y z : A) → Pd (Pb IdMnd (Idx↓ IdMnd↓)) (((ttᵢ , z) , (ttᵢ , cst x)))
    unary-pd x y z =
      nd (ttᵢ , cst y)
         (cst (ttᵢ , cst x))
         (cst (η (Slice (Pb IdMnd (Idx↓ IdMnd↓))) ((ttᵢ , y) , ttᵢ , cst x)))

    -- This should be the type of fillers of the 2-simplex
    2-simplex : {x y z : A} (p : x == y) (q : y == z) (r : x == z) → Set
    2-simplex {x} {y} {z} p q r =
      Ob (Hom (Hom XA))
        ((((ttᵢ , z) , (ttᵢ , cst x)) , (x , r) , ttᵢ , cst idp) ,
         unary-pd x y z ,
         λ { (inl tt)  → (y , q) , ttᵢ , cst idp ;
             (inr (ttᵢ , inl tt)) → (x , p) , ttᵢ , cst idp ;
             (inr (ttᵢ , inr ())) })
             
    2-simplex-lem→ : {x y z : A} (p : x == y) (q : y == z) (r : x == z) → 2-simplex p q r → r == p ∙ q
    2-simplex-lem→ {x} {y} {.t} p q r ((((t , idp) , ttᵢ , u) , v) , pd , rel) = {!pd!}
    

  -- module _ (A : Set) where

  --   open import IdentityMonadOver A

  --   id-is-algebraic : is-algebraic IdMnd IdMnd↓
  --   id-is-algebraic ttᵢ ttᵢ ν = has-level-in (ctr , unique)

  --     where ctr : alg-comp IdMnd IdMnd↓ ttᵢ ttᵢ ν
  --           ctr = ⟦ ν ttᵢ ∣ ttᵢ ∣ λ= (λ { ttᵢ → idp }) ⟧

  --           unique : (α : alg-comp IdMnd IdMnd↓ ttᵢ ttᵢ ν) → ctr == α
  --           unique ⟦ a ∣ ttᵢ ∣ idp ⟧ =
  --             ap (λ x → ⟦ a ∣ ttᵢ ∣ x ⟧) {!!}

  --   XA : OpetopicType IdMnd
  --   XA = ↓-to-OpType IdMnd IdMnd↓ 

  --   XA-is-fibrant : is-fibrant XA
  --   XA-is-fibrant = alg-is-fibrant IdMnd IdMnd↓
  --     id-is-algebraic

  -- to-∞Groupoid : Set → ∞Groupoid
  -- to-∞Groupoid A = XA A , XA-is-fibrant A

