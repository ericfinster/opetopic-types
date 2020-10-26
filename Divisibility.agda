{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import SliceLemmas

module Divisibility where

  --
  --  Disvisibility of an extension
  --

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    record divisor (i : Idx M) (c : Cns M i)
           (δ : (p : Pos M c) → Cns M (Typ M c p))
           (j : Idx↓ M↓ i) (α : Cns↓ M↓ j (μ M c δ))
           (∂ : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
           (β : (p : Pos M c) → Cns↓ M↓ (∂ p) (δ p))
           (coh : (p : Pos M c) (q : Pos M (δ p))
             → Typ↓ M↓ α (μ-pos M c δ p q) == Typ↓ M↓ (β p) q) : Set where
      field

        div : Cns↓ M↓ j c
        typ-coh : (p : Pos M c) → Typ↓ M↓ div p == ∂ p 
        μ-coh : μ↓ M↓ {δ = δ} div (λ p → transport (λ x → Cns↓ M↓ x (δ p)) (! (typ-coh p)) (β p)) == α
        coh-coh : (p : Pos M c) (q : Pos M (δ p))
          → coh p q == ! (ap (λ x → Typ↓ M↓ x (μ-pos M c δ p q)) μ-coh) ∙
            typ-trans-inv M M↓ (! (typ-coh p)) (β p) q

    open divisor public
    
    is-divisible-ext : Set
    is-divisible-ext = (i : Idx M) (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (j : Idx↓ M↓ i) (α : Cns↓ M↓ j (μ M c δ))
      → (∂ : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → (β : (p : Pos M c) → Cns↓ M↓ (∂ p) (δ p))
      → (coh : (p : Pos M c) (q : Pos M (δ p))
           → Typ↓ M↓ α (μ-pos M c δ p q) == Typ↓ M↓ (β p) q)
      → is-contr (divisor i c δ j α ∂ β coh) 

  --
  --  Divisibility of a relation on the slice
  --
  
  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-div : is-divisible-ext M M↓) where

    SlcM : 𝕄
    SlcM = Slice (Pb M (Idx↓ M↓)) 

    SlcM↓ : 𝕄↓ SlcM
    SlcM↓ = Slice↓ (Pb↓ M↓ (Idx↓ M↓ ) (λ i j k → j == k))

    DblSlcM : 𝕄
    DblSlcM = Slice (Pb SlcM (Idx↓ SlcM↓))

    DblSlcM↓ : 𝕄↓ DblSlcM
    DblSlcM↓ = Slice↓ (Pb↓ SlcM↓ (Idx↓ SlcM↓) (λ i j k → j == k)) 

    SlcRel : Set₁
    SlcRel = Idx DblSlcM → Set

    CanonRel : SlcRel
    CanonRel = Idx↓ DblSlcM↓ 

    is-unital : (R : SlcRel)
      → (i : Idx M) (j : Idx↓ M↓ i)
      → (d : Cns↓ M↓ j (η M i))
      → (typ-d : (p : Pos M (η M i)) → Typ↓ M↓ d p == j)
      → Set
    is-unital R i j d typ-d = R ((((i , j) , (η M i , cst j)) , (j , idp) , (d , typ-d)) , lf (i , j) , λ { () })
    
    is-div-rel : (R : SlcRel)
      → (i : Idx M) (j : Idx↓ M↓ i)
      → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → (δ : (p : Pos M c) → Cnsₚ M (Idx↓ M↓) (Typ M c p , ν p))
      → (ε : (p : Pos M c) → Cnsₛ (Pb M (Idx↓ M↓)) ((Typ M c p , ν p) , δ p))
      → (θ : (p : Posₛ (Pb M (Idx↓ M↓)) (nd {i = (i , j)} (c , ν) δ ε)) → Idx↓ SlcM↓ (Typₛ (Pb M (Idx↓ M↓)) (nd (c , ν) δ ε) p))
      → (d : Cns↓ M↓ j (μ M c (λ p → fst (δ p))))
      → (typ-d : (p : Pos M (μ M c (λ p₁ → fst (δ p₁)))) → Typ↓ M↓ d p ==
                      snd (δ (μ-pos-fst M c (λ p₁ → fst (δ p₁)) p))
                        (μ-pos-snd M c (λ p₁ → fst (δ p₁)) p))
      → Set
    is-div-rel R i j c ν δ ε θ d typ-d =
      R ((((i , j) , _ , _) , (j , idp) , d , typ-d) , nd (c , ν) δ ε , θ) ≃
        (θ (inl unit) == (j , idp) , (div dv , typ-coh dv))

      where dv : divisor M M↓ i c (fst ∘ δ) j d ν (λ p → {!!}) (λ p q → {!!})
            dv = {!!} 

    -- I cannot complete this yet for a kind of dumb reason: we are
    -- being asked here to divide with respect to a decoration by
    -- *trees*, whereas the defintion of divisibility above is in
    -- terms of just a decoration by constructors (i.e., a 2-level tree
    -- as opposed to an aribitrary one).  In principle, this does
    -- not matter (since you can just compose) but it takes some work
    -- to connect the two, and it might just be better to rewrite the
    -- definition above to work with trees instead.

    -- Now I claim:
    --
    --  1. The space of unital/divisible relations is visibly a proposition.
    --     Indeed, the defintions essentially say it is forced to be equal
    --     to some given space of equalities which does not mention R itself.
    --     Hence, given R and R', since they are both equivalent to θ = ..blah..,
    --     they are equivalent to each other.
    --
    --  2. The canonical relation (defined above) is unital and
    --     divisible.  And since I have already argued that the space of
    --     such relations is a proposition, this means it is an *inhabited*
    --     proposition and hence contractible.
    --
    --  In other words: given a divisible monad extension, the space
    --  of divisible relations on the slice of that monad is
    --  contractible.
    --
    --  So what's left to show, roughly, is that if we have a fibrant
    --  opetopic type over the identity monad, then all of its monads,
    --  and all of its "relations" are unital and divisible in the
    --  sense just described.  It should then follow by coinduction
    --  that they are all equivalent to the *canonical relations*, i.e
    --  those which are given by the "↓-to-OpType" construction which
    --  is exactly what CanonRel above is.
    --
    --  I believe this last step is where one needs some kind of
    --  completeness hypothesis.  This corresponds to Antoine's proof
    --  that a fibrant type is divisible in the presence of
    --  completeness.
    --
    --  That should be it.  We "just" have to put together all the
    --  pieces.  Which is going to be a serious pain in the ass.
    --
