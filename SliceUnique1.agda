{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import FundamentalThm

module SliceUnique1 (M : 𝕄) (M↓ : 𝕄↓ M) where

  open import SliceUnfold M M↓
  open import SliceAlg M M↓
  open import SliceUnique M M↓

  -- The hypothesis we need splits by induction into two cases: one
  -- for leaves and one for nodes.  So let's isolate what we need
  -- for each.

  module RHypSplit (R : Rel₂) where

    -- This is the case for leaves
    R-hyp-lf : Set
    R-hyp-lf = (i : Idx M) (j : Idx↓ M↓ i) 
      → (ϕ : (p : Pos Slc₁ (lf (i , j))) → Idx↓ Slc↓₁ (Typ Slc₁ (lf (i , j)) p))
      → R ((((i , j) , η M i , cst j) , (j , idp) , η↓ M↓ j , cst idp) , lf (i , j) , ϕ)

    -- This is the case for nodes
    R-hyp-nd : Set
    R-hyp-nd = (i : Idx M) (j : Idx↓ M↓ i)
      → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → (δ : (p : Pos Plbk₁ {i = i , j} (c , ν)) → Cns Plbk₁ (Typ Plbk₁ {i = i , j} (c , ν) p))
      → (ε : (p : Pos Plbk₁ {i = i , j} (c , ν)) → Cns Slc₁ (Typ Plbk₁ {i = i , j} (c , ν) p , δ p))
      → (ϕ : (p : Pos Slc₁ (nd {i = i , j} (c , ν) δ ε)) → Idx↓ Slc↓₁ (Typ Slc₁ (nd {i = i , j} (c , ν) δ ε) p))
      → let open IdxIh i j c ν δ ε ϕ in 
        R ((((i , j) , (μ M c (fst ∘ δ) , (λ p → snd (δ (μfst p)) (μsnd p)))) , (j' , j'=j) , (μ↓ M↓ d δ↓' , typ-μ↓=ν')) , nd (c , ν) δ ε , ϕ) 

    R-hyp-split : (R-lf : R-hyp-lf) (R-nd : R-hyp-nd)
      → R-hypothesis R
    R-hyp-split R-lf R-nd ._ (lf (i , j)) ϕ = R-lf i j ϕ
    R-hyp-split R-lf R-nd ._ (nd {i , j} (c , ν) δ ε) ϕ = R-nd i j c ν δ ε ϕ
  
  --  So, from the analysis in SliceUnique.agda, we need to prove these
  --  two clauses using only three facts: the monad extension is algebraic,
  --  R is fibrant, and R admits a fibrant extension T.

  --  Let's look at the leaf case first.

  module RHypLeaf (is-alg : is-algebraic M M↓)
      (R : Rel₂) (is-fib-R : unique-action Slc₁ (Idx↓ Slc↓₁) R)
      (T : Rel₃) (is-fib-T : unique-action Slc₂ (Idx↓ Slc↓₂) T) where

    -- We need to show we have an element of R-hyp-lf.  Let's
    -- see what we actually get from fibrancy.

    module _ (i : Idx M) (j : Idx↓ M↓ i) 
             (ϕ : (p : Pos Slc₁ (lf (i , j))) → Idx↓ Slc↓₁ (Typ Slc₁ (lf (i , j)) p)) where

      -- We can extract the center of contraction given by fibrancy ...
      
      fib-ctr : Σ (Idx↓ Slc↓₁ ((i , j) , (η M i , cst j))) (λ a → R ((((i , j) , η M i , cst j) , a) , lf (i , j) , ϕ))
      fib-ctr = contr-center (is-fib-R ((i , j) , (η M i , cst j)) (lf (i , j)) ϕ)

      -- ... and project out its elements.
      
      idx-el : Idx↓ Slc↓₁ ((i , j) , (η M i , cst j))
      idx-el = fst fib-ctr

      R-el : R ((((i , j) , η M i , cst j) , idx-el) , lf (i , j) , ϕ)
      R-el = snd fib-ctr

    -- So comparing the elemnent of R that we *get*, and the element
    -- that we *need*, we will be done if we can show the following:

    lf-case-done-if : Set
    lf-case-done-if = (i : Idx M) (j : Idx↓ M↓ i) 
      → (ϕ : (p : Pos Slc₁ (lf (i , j))) → Idx↓ Slc↓₁ (Typ Slc₁ (lf (i , j)) p))
      → idx-el i j ϕ == (j , idp) , (η↓ M↓ j , cst idp)

    -- Because then we can just transport:
    
    open RHypSplit R

    lf-case-done-implies-hyp-lf : (l : lf-case-done-if) → R-hyp-lf 
    lf-case-done-implies-hyp-lf l i j ϕ =
      transport (λ x → R ((((i , j) , η M i , cst j) , x) , lf (i , j) , ϕ))
      (l i j ϕ) (R-el i j ϕ) 

    --  So why must these two elements be equal?

    module _ (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
             (j : Idx↓ M↓ i) (c↓ : Cns↓ M↓ j (η M i))
           where

      -- I see.  You don't explicitly give the tree over.  Rather, you give it
      -- as a decoration in the slice.  That's why you thought you should be
      -- working in the algebra, but it looks here like you are working in the
      -- base.  I see.

      comp-tr : Idx Slc₂
      comp-tr = (((i , j) , {!!}) , (j , idp) , (μ↓ M↓ c↓ {!!} , {!!})) , nd (η M i , cst j) {!!} {!!} , {!!}

    -- module _ (i : Idx M) (j : Idx↓ M↓ i) 
    --          (ϕ : (p : Pos Slc₁ (lf (i , j))) → Idx↓ Slc↓₁ (Typ Slc₁ (lf (i , j)) p)) where

    -- Uh-oh.  So I now realize that you had been identifying two
    -- different compositions in you head: there is the one given
    -- by composition in the monad over, and the one given by R.

    -- What you can show is the idempotency with respect to the *R*
    -- composition.  But then you need the two to agree, don't you?

    -- Hmmm.  Yeah, so it almost feels like a kind of Eckmann-Hilton
    -- type deal: you've got two multiplications.  And you basically
    -- need to show that they agree.

    -- Okay, well in any case, that's a nice way to put it.  And I
    -- guess you had already thought that maybe the leaf and node
    -- cases should not be so different from each other.

    -- So it looks like we'll need some kind of "exchange" principle,
    -- or some way of connecting these two multiplications.  I guess
    -- clearly this will we proved by the kind of elimination
    -- principle we have on the constructors over because of the
    -- algebricity.

    -- Right, so maybe instead of idempotency, you can show that this
    -- element must be a right/left unit for composition.  Or
    -- something along these lines.

    -- Again, be careful. It's surely a unit for *R*-composition.  But
    -- you need it to be a unit for *M↓*-composition.  So somehow a
    -- first step is to show that we have a relation between R and
    -- *some* form of composition.


