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

  -- Hmm.  Can you maybe this the *whole* hypothesis in the base?
  -- Because now the whole thing is only a statement about is-alg.
  -- And after an iteration, this will become the proof that the
  -- slice is algebraic, which will compute.  And since there is
  -- no extra hypothesized data, we can *apply* this function
  -- whenever we like.

  -- Nice.  So it's a little like you're idea of a "continuation".
  -- Maybe this is the right way to axiomatize that idea?
  
  alg↓-unique' : (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓)
    → (X : OpetopicType (Slice (Pb M (Idx↓ M↓)))) (is-fib : is-fibrant X)
    -- We'll need to add that X is fibrant at the base level so that
    -- we actually *have* elements of x to apply the function to.
    → (κ : (i : Idx M) (c : Cns M i)
         → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
         → (j : Idx↓ M↓ i) (x : Ob X (((i , j) , c , ν)))
         → idx (contr-center (is-alg i c ν)) == j)
    → ↓-to-OpType M M↓ ≃ₒ record { Ob = Idx↓ M↓ ; Hom = X }
  alg↓-unique' = {!!} 

  -- This makes a lot of sense.  Now we are not hypothesizing any
  -- extra data besides that which is given by the fibrant opetopic
  -- type.  Rather, we are saying that if you *already know* a way
  -- to transform the base of your opetopic type to be the correct,
  -- then we can *find* a compatible way to transform the rest.

  -- Moreover, in defining κ' (i.e. the next iteration), we will be
  -- allowed to suppose that we are indeed looking at the composite.
  -- Not sure exactly what this will give, but okay .....

  -- No, I think it's the other way around: the goal does not depend
  -- on the x.  So what you can do is match on *j*, and in this case,
  -- you'll actually be able to pattern match in the slice.  Moreover,
  -- it somehow looks like it's going to come out completely trivially.
  
  -- This feels really, really good now.

  -- Yeah.  This seems to be exactly the idea of "looking back into the
  -- past".  I.e., everything always reduces down to the base case.

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
    
    next-ob≃ : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X₁ i
    next-ob≃ ((i , j) , c , ν) = equiv to from to-from from-to

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


    --
    --  Relation between is-alg and is-fib-X₁
    --

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

    module _ (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) where

      lcl≃ : (j : Idx↓ M↓ i) → Idx↓ ExtSlc↓₁ ((i , j) , c , ν) ≃ X₁ ((i , j) , c , ν)
      lcl≃ j = next-ob≃ ((i , j) , c , ν)
      
      ctr= : –> (Σ-emap-r lcl≃ ∘e (alg-to-idx↓ M M↓ i c ν)) (contr-center (is-alg i c ν)) ==
             contr-center (is-fib-X₁ i c ν) 
      ctr= = ap (λ x → contr-center (x i c ν)) two-fibs-agree 

      wit=x₁ : (j : Idx↓ M↓ i) (x₁ : X₁ ((i , j) , c , ν))
        → (idx (contr-center (is-alg i c ν)) , witness i c ν) == (j , x₁) 
      wit=x₁ j x₁ = contr-has-all-paths ⦃ is-fib-X₁ i c ν ⦄ (idx (contr-center (is-alg i c ν)) , witness i c ν) (j , x₁) 

      -- Equivalence between algebraic compositions and indices
      -- alg-to-idx↓ : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      --   → alg-comp M M↓ i c ν ≃ Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν)))
      -- alg-to-idx↓ i c ν = equiv to from to-from from-to

      --   where to : alg-comp M M↓ i c ν → Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν)))
      --         to ⟦ j ∣ d ∣ τ ⟧ = j , (j , idp) , d , app= τ

      --         from : Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν))) → alg-comp M M↓ i c ν
      --         from (j , (.j , idp) , d , τ) = ⟦ j ∣ d ∣ λ= τ ⟧

      --         to-from : (x : Σ (Idx↓ M↓ i) (λ j → Idx↓ Slc↓ ((i , j) , (c , ν))))
      --           → to (from x) == x
      --         to-from (j , (.j , idp) , d , τ) =
      --           ap (λ x → j , (j , idp) , d , x) (λ= (λ p → app=-β τ p))

      --         from-to : (x : alg-comp M M↓ i c ν)
      --           → from (to x) == x
      --         from-to ⟦ j ∣ d ∣ τ ⟧ = ap (λ x → ⟦ j ∣ d ∣ x ⟧) (! (λ=-η τ)) 


    --
    --  Hmmm.  Now I'm starting to doubt that this approach will work.
    --  Because it looks like one of the paths dependes on X₁-el,
    --  while the other doesn't.  So how are you going to get a
    --  congruence to relate them?
    --

    --  Shit.  Then what could be the backup plan? 


    next-witness : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
      → (θ : (p : Pos ExtSlc₁ σ) → X₁ (Typ ExtSlc₁ σ p))
      → X₂ ((i , –> (next-ob≃ i) (slc-idx i σ (λ p → <– (next-ob≃ (Typ ExtSlc₁ σ p)) (θ p)))) , (σ , θ))
    next-witness ((i , j) , ._ , ._) (lf .(i , j)) θ = transport (λ x → X₂ ((((i , j) , η M i , (λ _ → j)) , x) , lf (i , j) , θ)) hence-need X₂-el

      where X₁-el : X₁ ((i , j) , η M i , (cst j))
            X₁-el = fst (contr-center (is-fib-X₂ ((i , j) , _ , _) (lf (i , j)) θ))

            X₂-el : X₂ ((((i , j) , η M i , (cst j)) , X₁-el) , lf (i , j) , θ)
            X₂-el = snd (contr-center (is-fib-X₂ ((i , j) , _ , _) (lf (i , j)) θ))

            j' : Idx↓ M↓ i
            j' = idx (contr-center (is-alg i (η M i) (cst j)))

            X₁-wit : X₁ ((i , j') , η M i , (cst j))
            X₁-wit = witness i (η M i) (cst j)

            fib-pth : (j' , X₁-wit) == (j , X₁-el)
            fib-pth = contr-has-all-paths ⦃ is-fib-X₁ i (η M i) (cst j) ⦄
              (idx (contr-center (is-alg i (η M i) (cst j))) , witness i (η M i) (cst j))
              (j , X₁-el)

            alg-pth : contr-center (is-alg i (η M i) (λ _ → j)) == ⟦ j ∣ η↓ M↓ j ∣ λ= (cst idp) ⟧
            alg-pth = contr-path (is-alg i (η M i) (λ _ → j)) ⟦ j ∣ η↓ M↓ j ∣ λ= (cst idp) ⟧ 

            -- alg-pth' : contr-center (is-alg i (η M i) (λ _ → j)) == ⟦ j ∣ η↓ M↓ j ∣ λ= (cst idp) ⟧
            -- alg-pth' = contr-has-all-paths ⦃ is-alg i (η M i) (cst j) ⦄ (contr-center (is-alg i (η M i) (cst j))) ⟦ j ∣ η↓ M↓ j ∣ λ= (cst idp) ⟧  

            P : Idx↓ M↓ i → Set
            P x = X₁ ((i , x) , η M i , cst j)

            hence-need : X₁-el == transport P (ap idx alg-pth) X₁-wit
            hence-need = X₁-el =⟨ ! (to-transp (snd= fib-pth)) ⟩
                         transport P (fst= fib-pth) X₁-wit
                           =⟨ {!!} ⟩ 
                         transport P (ap idx alg-pth) X₁-wit =∎


    next-witness ((i , j) , ._ , ._) (nd c δ ε) θ = {!!}


