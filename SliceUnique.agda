{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import FundamentalThm
open import MonadEqv 
open import SliceUnfold
open import SliceAlgebraic

-- Can you fix this?
open import lib.NType2

module SliceUnique where

  -- Here, I believe is the proper coinductive statement
  -- of the theorem:

  alg↓-unique : (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓)
    → (X : OpetopicType M) (is-fib : is-fibrant X)
    → (ob≃ : (i : Idx M) → Idx↓ M↓ i ≃ Ob X i)
    → (witness : (i : Idx M) (c : Cns M i)
               → (ν : (p : Pos M c) → Ob X (Typ M c p))
               → Ob (Hom X) ((i , –> (ob≃ i) (idx (contr-center (is-alg i c (λ p → <– (ob≃ (Typ M c p)) (ν p)))))) , c , ν))
    → ↓-to-OpType M M↓ ≃ₒ X 
  Ob≃ (alg↓-unique M M↓ is-alg X is-fib ob≃ witness) = ob≃
  Hom≃ (alg↓-unique M M↓ is-alg X is-fib ob≃ witness) =
    let open ExtUnfold M M↓ in
    alg↓-unique ExtSlc₁ ExtSlc↓₁ (slc-algebraic M M↓)
      (op-transp (Slice≃ (Pb≃' ob≃)) (Hom X))
      (op-transp-fib (Slice≃ (Pb≃' ob≃)) (Hom X) (hom-fibrant is-fib))
      {!!}
      {!!}

  -- We are left with two proof obligations, which, after eliminating
  -- away the equivalence by univalence, become the following:

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓)
           -- (X₀ : Rel₀ M) (e : (i : Idx M) → Idx↓ M↓ i ≃ X₀ i)
           (X₁ : Rel₁ M (Idx↓ M↓)) (is-fib-X₁ : is-fib₁ M X₁)
           (X₂ : Rel₂ M X₁) (is-fib-X₂ : is-fib₂ M X₂)
           (witness : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
                    → X₁ ((i , idx (contr-center (is-alg i c ν))) , (c , ν)))
           where

    open ExtUnfold M M↓
    open import SliceAlg M M↓

    -- The next equivalence is given generically by the
    -- fundamental theorem, which says both the spaces may
    -- be expressed as identity types.
    
    next-ob≃ : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X₁ i
    next-ob≃ ((i , j) , c , ν) = equiv to from to-from from-to

      -- Idx↓ ExtSlc↓₁ ((i , j) , c , ν)         ≃⟨ {!!} ⟩  -- by the fundamental theorem
      -- j == idx (contr-center (is-alg i c ν))  ≃⟨ {!!} ⟩  -- again, by the fundamental theorem, using "witness"
      -- X₁ ((i , j) , c , ν) ≃∎

      where to : Idx↓ ExtSlc↓₁ ((i , j) , c , ν) → X₁ ((i , j) , c , ν)
            to ((j' , j'=j) , d , typ-d=ν) = transport (λ x → X₁ ((i , x) , c , ν)) (ap idx alg=α ∙' j'=j) (witness i c ν) 

              where α : alg-comp M M↓ i c ν
                    α = ⟦ j' ∣ d ∣ λ= typ-d=ν ⟧ 

                    alg=α : contr-center (is-alg i c ν) == α
                    alg=α = contr-path (is-alg i c ν) α 

            from : X₁ ((i , j) , c , ν) → Idx↓ ExtSlc↓₁ ((i , j) , c , ν)
            from x₁ = (idx alg , fst= wit=x₁) , (cns alg , λ p → app= (typ alg) p) 

              where alg : alg-comp M M↓ i c ν
                    alg = contr-center (is-alg i c ν)
                    
                    wit=x₁ : (idx (contr-center (is-alg i c ν)) , witness i c ν) == (j , x₁) 
                    wit=x₁ = contr-has-all-paths ⦃ is-fib-X₁ i c ν ⦄ (idx (contr-center (is-alg i c ν)) , witness i c ν) (j , x₁) 

            -- So this is clear, but annoying because of the funext....
            to-from : (x₁ : X₁ ((i , j) , c , ν)) → to (from x₁) == x₁
            to-from x₁ = to (from x₁) =⟨ idp ⟩                                                             -- defn
                         transport P (ap idx alg=α ∙' fst= wit=x₁) (witness i c ν) =⟨ {!idp!} ⟩            -- split
                         transport P (fst= wit=x₁) (transport P (ap idx alg=α) (witness i c ν)) =⟨ {!!} ⟩  -- because the first transport "is" the identity
                         transport P (fst= wit=x₁) (witness i c ν) =⟨ to-transp (snd= wit=x₁) ⟩                               -- by wit=x₁ below
                         x₁ =∎ 
  
                where P : Idx↓ M↓ i → Set
                      P x = X₁ ((i , x) , c , ν)
                      
                      alg : alg-comp M M↓ i c ν
                      alg = contr-center (is-alg i c ν)
                      
                      α : alg-comp M M↓ i c ν
                      α = ⟦ idx alg ∣ cns alg ∣ λ= (λ p → app= (typ alg) p) ⟧ 

                      alg=α : contr-center (is-alg i c ν) == α
                      alg=α = contr-path (is-alg i c ν) α 

                      wit=x₁ : (idx (contr-center (is-alg i c ν)) , witness i c ν) == (j , x₁) 
                      wit=x₁ = contr-has-all-paths ⦃ is-fib-X₁ i c ν ⦄ (idx (contr-center (is-alg i c ν)) , witness i c ν) (j , x₁) 

            from-to : (i₁ : Idx↓ ExtSlc↓₁ ((i , j) , c , ν)) → from (to i₁) == i₁
            from-to ((j' , j'=j) , d , typ-d=ν) = (idx alg , fst= wit=x₁) , (cns alg , λ p → app= (typ alg) p) =⟨ {!!} ⟩ -- because wit=x₁ == with=x₁'
                                                  (idx alg , ap idx alg=α ∙' j'=j) , (cns alg , λ p → app= (typ alg) p) =⟨ {!!} ⟩ -- should now be just from alg=α ...
                                                  ((j' , j'=j) , d , typ-d=ν) =∎

                -- Yeah, so already here we see that this is kind of non-trivial and you're
                -- going to have to think about it a bit to make it work.  But, I mean, the
                -- existence of this equivalence is not really in doubt.  So you just have
                -- to work a bit more to unfold it and everything.

                where P : Idx↓ M↓ i → Set
                      P x = X₁ ((i , x) , c , ν)
                      
                      alg : alg-comp M M↓ i c ν
                      alg = contr-center (is-alg i c ν)

                      α : alg-comp M M↓ i c ν
                      α = ⟦ j' ∣ d ∣ λ= typ-d=ν ⟧ 

                      alg=α : contr-center (is-alg i c ν) == α
                      alg=α = contr-path (is-alg i c ν) α 

                      x₁ : X₁ ((i , j) , c , ν)
                      x₁ = transport P (ap idx alg=α ∙' j'=j) (witness i c ν) 

                      -- Okay, so this is an interesting idea.  Is it what you were looking for?
                      
                      wit=x₁ : (idx (contr-center (is-alg i c ν)) , witness i c ν) == (j , x₁) 
                      wit=x₁ = contr-has-all-paths ⦃ is-fib-X₁ i c ν ⦄ (idx (contr-center (is-alg i c ν)) , witness i c ν) (j , x₁) 

                      wit=x₁' : (idx (contr-center (is-alg i c ν)) , witness i c ν) == (j , x₁)
                      wit=x₁' = pair= (ap idx alg=α ∙' j'=j) (from-transp P (ap idx alg=α ∙' j'=j) idp) 



    is-fib-X₁' : is-fib₁ M X₁
    is-fib-X₁' i c ν = has-level-in (ctr , pth) 

      where lcl≃ : (j : Idx↓ M↓ i) → Idx↓ ExtSlc↓₁ ((i , j) , c , ν) ≃ X₁ ((i , j) , c , ν)
            lcl≃ j = next-ob≃ ((i , j) , c , ν)

            the-eqv : alg-comp M M↓ i c ν ≃ Σ (Idx↓ M↓ i) (λ a → X₁ ((i , a) , c , ν))
            the-eqv = Σ-emap-r lcl≃ ∘e (alg-to-idx↓ M M↓ i c ν) 

            ctr : Σ (Idx↓ M↓ i) (λ j → X₁ ((i , j) , (c , ν)))
            ctr = –> (the-eqv) (contr-center (is-alg i c ν))

            pth : (y : Σ (Idx↓ M↓ i) (λ j → X₁ ((i , j) , (c , ν)))) → ctr == y
            pth y = ap (–> (the-eqv)) (contr-path (is-alg i c ν) (<– (the-eqv) y)) ∙
                    <–-inv-r (the-eqv) y  

    -- And here's what you wanted....
    two-fibs-agree : is-fib-X₁' == is-fib-X₁
    two-fibs-agree = prop-has-all-paths
      ⦃ Π-level (λ i → Π-level (λ c → Π-level (λ ν → is-contr-is-prop))) ⦄
        is-fib-X₁' is-fib-X₁

    -- Now.  This should give a relation between the two, right?  It should
    -- be possible to work out exactly what that relation is.  And I think
    -- you'll need that....

    -- Hmmm.  But the paths will be equal over the proof that the
    -- centers are equal. Aha!  But that's the key!  There will be
    -- such a proof by applying the function on either side.  Doesn't
    -- this already have to give a relation between the two?

    -- It may be useful, however, to prove the above equivalence
    -- directly so that we have better control over the image of
    -- various elements....

    -- In any case, we have now reduced ourselves to the following:
    -- we have to find a witness in X₂ showing that it coincides
    -- with the proof that the slice is algebraic.  This should be
    -- carried out via induction, now with the extra hypothesis that
    -- X₁ witnesses multiplication in the algebra.

    next-witness : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
      → (θ : (p : Pos ExtSlc₁ σ) → X₁ (Typ ExtSlc₁ σ p))
      → X₂ ((i , –> (next-ob≃ i) (slc-idx i σ (λ p → <– (next-ob≃ (Typ ExtSlc₁ σ p)) (θ p)))) , (σ , θ))
    next-witness ((i , j) , ._ , ._) (lf .(i , j)) θ = transport (λ x → X₂ ((((i , j) , η M i , (λ _ → j)) , x) , lf (i , j) , θ)) hence-need X₂-el

      where X₁-el : X₁ ((i , j) , η M i , (λ _ → j))
            X₁-el = fst (contr-center (is-fib-X₂ ((i , j) , _ , _) (lf (i , j)) θ))

            X₂-el : X₂ ((((i , j) , η M i , (λ _ → j)) , X₁-el) , lf (i , j) , θ)
            X₂-el = snd (contr-center (is-fib-X₂ ((i , j) , _ , _) (lf (i , j)) θ))

            j' : Idx↓ M↓ i
            j' = idx (contr-center (is-alg i (η M i) (λ _ → j)))

            X₁-wit : X₁ ((i , j') , η M i , (λ _ → j))
            X₁-wit = witness i (η M i) (cst j)

            stronger-claim : contr-center (is-alg i (η M i) (λ _ → j)) == ⟦ j ∣ η↓ M↓ j ∣ λ= (cst idp) ⟧
            stronger-claim = contr-path (is-alg i (η M i) (λ _ → j)) ⟦ j ∣ η↓ M↓ j ∣ λ= (cst idp) ⟧ 

            can-get : j , X₁-el == j' , X₁-wit
            can-get = contr-has-all-paths ⦃ is-fib-X₁ i (η M i) (cst j) ⦄ (j , X₁-el) (j' , X₁-wit)

            hence-need : X₁-el == –> (next-ob≃ ((i , j) , η M i , (λ _ → j))) ((j , idp) , η↓ M↓ j , (λ _ → idp))
            hence-need = X₁-el =⟨ to-transp! (snd= can-get) ⟩
                         transport! P (fst= can-get) X₁-wit
                           =⟨ {!!} ⟩ -- Well, then clearly we need these two to be inverse to each other ...
                         transport P (ap idx stronger-claim) X₁-wit
                           =⟨ idp ⟩ 
                         –> (next-ob≃ ((i , j) , η M i , (λ _ → j))) ((j , idp) , η↓ M↓ j , (λ _ → idp)) =∎

                where P : Idx↓ M↓ i → Set
                      P x = X₁ ((i , x) , η M i , cst j)

            -- Well, maybe there is something simler.... from "can-get" we have
            -- that X₁-el == transport .... X₁-wit.  So if the equivalence is
            -- given as a transport in this way, wouldn't we be done?
            
            -- Interesting.  So it is a transport.  But using a
            -- different path.  There's the one given by X₁ being
            -- fibrant, and the one given by the the fact that we are
            -- in an algebraic extension.

            -- Ohhh!  But I think that's it!  Because now I get *two*
            -- proofs that X₁ is fibrant.  there's the one I have
            -- assumed, and there's the one given by pulling back the
            -- proof that the extension is algebraic along the
            -- equivalence.  What I need is that these two coincide.  But
            -- now I will get that because being fibrant is a property!
            -- And now I have that X₁ is a transport via can-get and that
            -- it is a transport along a path which must be equivalent.

            -- Bam!!!


            -- Okay, so now we need to do something clever.  And here
            -- is where I think we need something like your argument
            -- from idempotence: any idempotent element must be
            -- equivalent to the canonical one.  But this time we have
            -- the extra information that the image of the idempotent
            -- element by the equivalence is the one claimed.

            -- Yes, something like this.  But there is likely to be
            -- another way to phrase this somehow.

            -- Okay, but we can define a "loop" to be an element like
            -- X₁-el.  And these will compose.  And so if my
            -- equivalence is a homomorphism (which I think it should
            -- be), I should be able to show that the thing on the
            -- right is idempotent.  But so is the thing on the left
            -- by fibrancy.  And therefore they should be equal and we
            -- get what we want.  That's the idea.

            -- Hmm.  But don't we still need to know that the
            -- multiplication defined by X₂ and the one given by
            -- composition agree for this to work?


    next-witness ((i , j) , ._ , ._) (nd c δ ε) θ = {!!}

