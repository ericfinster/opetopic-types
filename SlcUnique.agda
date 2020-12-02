{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
-- open import IdentityMonad
-- open import IdentityMonadOver
-- open import InftyGroupoid
-- open import FundamentalThm
-- open import MonadEqv 
open import SliceUnfold

module SlcUnique where

  --
  --  Investigating the consequences of fibrancy ... 
  --
  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    open Slices M M↓ 

    module _ (R : Idx Slc₂ → Set) where

      SlcR : 𝕄
      SlcR = Slice (Pb Slc₂ R)

      module _ (T : Idx SlcR → Set) (is-fib-T : unique-action Slc₂ R T) where

        -- So, what does the fibrancy of T get us in this case?
        dbl-slice-unit : (i : Idx M) (j : Idx↓ M↓ i) → Idx Slc₂
        dbl-slice-unit i j = (((i , j) , (_ , _)) , ((j , idp) , (η↓ M↓ j , cst idp))) , lf (i , j) , λ { () }

        -- Ahh!  What's the unit?
        T-lf : (i : Idx (Pb Slc₁ (Idx↓ Slc↓₁))) → Cns Slc₂ (i , η (Pb Slc₁ (Idx↓ Slc↓₁)) i)
        T-lf i = lf i 

        R-unital : (i : Idx (Pb Slc₁ (Idx↓ Slc↓₁))) → R (i , η (Pb Slc₁ (Idx↓ Slc↓₁)) i) 
        R-unital i = fst (contr-center (is-fib-T (i , η (Pb Slc₁ (Idx↓ Slc↓₁)) i) (lf i) (λ { () })))

        gen-case : Idx (Pb Slc₁ (Idx↓ Slc↓₁)) → Type₀
        gen-case (((i , j) , (c , ν)) , ((j' , j'=j) , d , typ-d=ν)) = {!η (Pb Slc₁ (Idx↓ Slc↓₁)) (((i , j) , (c , ν)) , ((j' , j'=j) , d , typ-d=ν))!} 

        -- nd (c , ν) (λ p → η M (Typ M c p) , (λ _ → ν p)) (λ p → lf (Typ M c p , ν p)), (λ _ → (j' , j'=j) , d , typ-d=ν)

        idx-pb : (i : Idx M) (j : Idx↓ M↓ i) → Idx (Pb Slc₁ (Idx↓ Slc↓₁))
        idx-pb i j = (((i , j) , (_ , _)) , ((j , idp) , (η↓ M↓ j , cst idp)))

        eta-pb : (i : Idx M) (j : Idx↓ M↓ i) → Cns (Pb Slc₁ (Idx↓ Slc↓₁)) (idx-pb i j)
        eta-pb i j = nd (η M i , (λ _ → j)) (λ _ → η M i , (λ _ → j)) (λ _ → lf (i , j)) , λ { true → (j , idp) , (η↓ M↓ j , cst idp) } 

        -- Hmmm.  This doesn't typecheck when we actually normalize.  Is that kind
        -- of thing a problem?
        
        special-case : (i : Idx M) (j : Idx↓ M↓ i) → R (idx-pb i j , {!eta-pb i j!})
        special-case i j = R-unital (((i , j) , (_ , _)) , ((j , idp) , (η↓ M↓ j , cst idp))) 

        -- Okay.  So. This indeed shows that these are *not* the
        -- hypotheses that we see below.  Yes, exactly!  Under the
        -- identification of R with the canonical relation, we should
        -- see that in the next step, this kind of "unit construction"
        -- *becomes* the unit over, and that's why we have an
        -- inhabitant of relating it to a leaf.

        -- So I think I agree that your prediction is right: we do
        -- indeed need these extra hypotheses on R, and under the the
        -- identification of R with the canonical relation, T should
        -- be transformed to a relation which satisfies exactly these
        -- same principles.
        
  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) where

    open Slices M M↓
    
    module _ (R : Idx Slc₂ → Set) (is-fib-R : unique-action Slc₁ (Idx↓ Slc↓₁) R) where

      -- Wait, can I *prove* the statement below using the fibrancy of R? 

      module _ (i : Idx M) (j : Idx↓ M↓ i) where

        ctr : Σ (Idx↓ Slc↓₁ ((i , j) , (η M i , cst j))) (λ z → R ((((i , j) , (η M i , cst j)) , z) , lf (i , j) , ⊥-elim))
        ctr = contr-center (is-fib-R ((i , j) , (η M i , cst j)) (lf (i , j)) ⊥-elim)

        R-fib-lf : R ((((i , j) , (η M i , cst j)) , fst ctr) , lf (i , j) , ⊥-elim)
        R-fib-lf = snd ctr 

        -- So I think the point is that the contraction center gives you these *four* pieces of data.
        -- That's why the fibration needs the extra agrument here.  But that's should be okay, you can
        -- still transport along the contractible piece.
        Alg-Fib : (α : alg-comp M M↓ i (η M i) (cst j)) (p : idx α == j)  → Set
        Alg-Fib ⟦ idx ∣ cns ∣ typ ⟧ p = R ((((i , j) , (η M i , cst j)) , (idx , p) , (cns , app= typ)) , lf (i , j) , ⊥-elim)

        -- Is this going to be enough to map to and from the canonical
        -- relation?  I see.  So the question is going to be if, there
        -- is actually a path from this guy to the canonical guy *in
        -- the space of four tuples*.  You get the first three from
        -- the algebricity of the extension.  The path over will be a
        -- commutative triangle, right?  But you will be using the
        -- *identity* path, so I think it will work out!

        canon-alg : alg-comp M M↓ i (η M i) (cst j)
        canon-alg = ⟦ j ∣ η↓ M↓ j ∣ idp ⟧ 
      
        r-alg : alg-comp M M↓ i (η M i) (cst j)
        r-alg = ⟦ fst (fst (fst ctr)) ∣ fst (snd (fst ctr)) ∣ λ= (snd (snd (fst ctr))) ⟧ 

        by-alg : r-alg == canon-alg
        by-alg = contr-has-all-paths ⦃ is-alg i (η M i) (cst j) ⦄ r-alg canon-alg

        triangle : snd (fst (fst ctr)) == idp [ (λ α → idx α == j) ↓ by-alg ]
        triangle = ↓-app=cst-in {!snd (fst (fst ctr))!}

        do-we-have : (j , idp) == (fst (fst ctr)) 
        do-we-have = {!!}

      module _ (i : Idx M) 
          (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          (δ : (p : Pos M c) → Cnsₚ M (λ z → Idx↓ M↓ z) (Typ M c p , ν p))
          (ε : (p : Pos M c) → Pd (Pb M (Idx↓ M↓)) ((Typ M c p , ν p) , δ p)) where

        α : alg-comp M M↓ i c ν
        α = contr-center (is-alg i c ν)
        
        j : Idx↓ M↓ i
        j = idx α 

      postulate
      
        R-lf-η↓ : (i : Idx M) (j : Idx↓ M↓ i)
          → R ((((i , j) , _ , _) , (j , idp) , η↓ M↓  j , cst idp) , lf (i , j) , ⊥-elim) 

        -- R-nd-μ↓ : (i : Idx M) (j : Idx↓ M↓ i)
        --   → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
        --   → (δ : (p : Pos M c) → Cnsₚ M (λ z → Idx↓ M↓ z) (Typ M c p , ν p))
        --   → (ε : (p : Pos M c) → Pd (Pb M (Idx↓ M↓)) ((Typ M c p , ν p) , δ p))
        --   → R ((((i , j) , _ , _) , (j , idp) , μ↓ M↓ {!!} {!!} , {!!}) , nd (c , ν) δ ε , {!!}) 

        R-nd-μ↓ : (i : Idx M) 
          → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          → (δ : (p : Pos M c) → Cnsₚ M (λ z → Idx↓ M↓ z) (Typ M c p , ν p))
          → (ε : (p : Pos M c) → Pd (Pb M (Idx↓ M↓)) ((Typ M c p , ν p) , δ p))
          → let α = contr-center (is-alg i c ν)
                j = idx α
                d = cns α
                τ = typ α
            in R ((((i , j) , _ , _) , (j , idp) , μ↓ M↓ d {!!} , {!!}) , nd (c , ν) δ ε , λ { p → {!p!} }) 

      -- Rats.  We have that reduction problem: because it's a
      -- position in a *particular* monad, it doesn't compute
      -- correctly.  Annoying.

      -- OH!!! But because M↓ is algebraic, we can actually *complete*
      -- the given information to a series of constructors: just use
      -- the decoration ν and the fact that M↓ is an algebraic
      -- extension.  (This means replacing j with the resulting
      -- output).  Nice.  So there's no more hypotheses needed.  The
      -- rest is determined.

      -- Yep.  And so it's clear what to do: assume the constructor
      -- over and a continutation of θ for all places.  Use this to do
      -- the multiplication over, and then reassemble the θ argument
      -- from the local data and the assumed continuation.

      need-to-show : (i : Idx Slc₂) → R i → CanonRel₂ i
      need-to-show ((((i , j) , ._ , ._) , (.j , idp) , d , typ-d=ν) , lf .(i , j) , θ) r =
        (((j , idp) , η↓ M↓ j , cst idp) , {!!}) , lf↓ (j , idp) , λ { () }

        -- Okay, and so this is clear from the fact that we have r in
        -- the context: by the fundamental theorem, this element of r
        -- is equivalent to the required equality.
        
      need-to-show ((((i , j) , ._ , ._) , (.j , idp) , d , typ-d=ν) , nd (c , ν) δ ε , θ) r = 
        (((j , idp) , {!!} , {!!}) , {!!}) , {!nd↓ (d , typ-d=ν) ? ?!} , {!!}


      -- It occurs to me that this direction may be more informative ...
      other-way : (i : Idx Slc₂) → CanonRel₂ i → R i
      -- other-way ((((i , j) , c , ν) , (.j , idp) , (d , typ-d=ν)) , ω , θ) ((_ , idp) , (A , B)) = {!ω!}
      other-way ((((i , j) , ._ , ._) , (.j , idp) , d , typ-d=ν) , lf .(i , j) , θ) ((_ , idp) , A , B) = {!!}

        -- I see. So the point now is to use this elimination
        -- principle which reduces us to this case: we'll transform
        -- the canonical element using the fact that the extension is
        -- algebraic to obtain the element of R.
        where my-alg : alg-comp M M↓ i (η M i) (cst j)
              my-alg = ⟦ j ∣ η↓ M↓ j ∣ idp ⟧ 

              competitor : alg-comp M M↓ i (η M i) (cst j)
              competitor = ⟦ j ∣ d ∣ (λ= typ-d=ν) ⟧
              
              pth : my-alg == competitor
              pth = contr-has-all-paths ⦃ is-alg i (η M i) (cst j) ⦄ my-alg competitor 

              -- Right, so funext is going to make this annoying like it was before.
              -- Probably this is an indication that you should modify the definition
              -- of algebraic....

              -- I see.  But you do in fact match on this data in the proof of the
              -- algebricity theorem.  So it's clearly a tradeoff......

      other-way ((((i , j) , ._ , ._) , (.j , idp) , d , typ-d=ν) , nd (c , ν) δ ε , θ) ((_ , idp) , A , B) = {!A!}

        -- Okay, I don't see what this one is, but it should be the
        -- second blank that you let agda fill in for you above.  So I
        -- think it's clearly there.  And you're just going to have
        -- the same strategy: reduce to this case by contractibility,
        -- and that's going to be the hypothesis from above.

        -- Right, so it looks like you'll have to actually modify
        -- delta and whatnot which complicates things a bit.  But
        -- I think I'm starting to see the idea.
        
        where the-alg : alg-comp M M↓ i (μ M c (fst ∘ δ)) (λ p → snd (δ (μ-pos-fst M c (fst ∘ δ) p)) (μ-pos-snd M c (fst ∘ δ) p))
              the-alg = ⟦ fst (fst (θ (inl tt))) ∣ μ↓ M↓ (fst (snd (θ true))) {!!}  ∣ {!!} ⟧ 

      --
      -- CanonRel ((((i , j) , (c , ν)) , ((j , idp) , (d , typ-d=ν))) , (ω , θ)) reduces to:
      -- 
      -- Σ
      -- (Σ
      --  (Σ (Σ (Idx↓ M↓ i) (λ j₁ → j₁ == j))
      --   (λ i↓ →
      --      Σ (Cns↓ M↓ (fst i↓) c)
      --      (λ d₁ → (p : Pos M c) → Typ↓ M↓ d₁ p == ν p)))
      --  (λ j₁ → j₁ == (j , idp) , d , typ-d=ν))
      -- (λ i↓ →
      --    Σ
      --    (Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) (fst (fst i↓) , snd (fst i↓))
      --     ω)
      --    (λ d₁ →
      --       (p : Posₛ (Pb M (Idx↓ M↓)) ω) →
      --       Typ↓ₛ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) d₁ p == θ p))

      
