{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType

module Experiments where

  -- Okay, we need the identity monads....
  
  𝕆Mnd : (n : ℕ) → 𝕄
  𝕆Mnd O = IdMnd ⊤
  𝕆Mnd (S n) = Slice (Pb (𝕆Mnd n) (cst ⊤))

  𝕆 : (n : ℕ) → Set
  𝕆 n = Idx (𝕆Mnd n) 

  -- Great.  Now.  I'd like to axiomatize what I mean when I say that
  -- a monoid is some kind of higher path space in A.  The problem is
  -- whether to axiomatize the *pullback* step or the *slice* step.

  record GroupoidalMonad (A : Set) : Set₁ where
    field
    
      n : ℕ
      M : 𝕄↓ (𝕆Mnd n)

      E : (o : 𝕆 n) → Idx↓ M o ≃ A 
      F : (o : 𝕆 n) (σ : Cns (𝕆Mnd n) o) (i : Idx↓ M o)
        → is-contr (Cns↓ M i σ) 
      
  -- The first one says that we have a product fibration of A and the
  -- n-opetopes.  The second says that the square is a pullback.  Now,
  -- I'm not 100% sure this is correct, but it's certainly the
  -- simplest thing you can imagine.

  -- The idea is something like this: from this stage, we should be
  -- able to slice the monad M.  Then we would like to chose a set of
  -- fillers and continue.  The point is to say that this choice is
  -- unique somehow.

  -- Okay, but then what is the answer?

  module _ (A : Set) (GM : GroupoidalMonad A) where

    open GroupoidalMonad GM

    R : (i : Idx (𝕆Mnd n)) → Idx↓ M i → ⊤ → Set
    R i a unit = ⊤

    M' : 𝕄↓ (𝕆Mnd (S n))
    M' = Slice↓ (Pb↓ M (cst ⊤) R)

    E' : (o : 𝕆 (S n)) → Idx↓ M' o ≃ A
    E' ((o , unit) , (p , ν)) = equiv to {!!} {!!} {!!}

      where to : Idx↓ₛ (Pb↓ M (λ _ → ⊤) R) ((o , tt) , p , ν) → A
            to ((a , r) , (s , ϕ)) = {!!} -- –> (E o) a

      -- F : (o : 𝕆 n) (σ : Cns (𝕆Mnd n) o) (i : Idx↓ M o)
      --   → is-contr (Cns↓ M i σ) 

    -- Okay.  So things are coming out fairly trivial.  Which is
    -- either good or bad depending on how you think of it ....

    -- Right.  So maybe indeed the idea is, for the moment, to work
    -- not with opetopic types themselves, but rather opetopic types
    -- over the terminal one.  Then you *do* have an opetopic type for
    -- every type, which I think should be unique.  Indeed, it should
    -- always be equivalent to the terminal guy over the monad over
    -- determined by the type A.

    -- Indeed.  And that's the thing, we would *should* have the
    -- absolute statement, but we're blocked from doing it by this
    -- annoying thing about a monad over not determining an opetopic
    -- type.  But if we *define* oo-groupoid to be an opetopic type
    -- *over* the terminal one which is appropriately fibrant, then
    -- I think perhaps we *can* get things to work out.


    -- Idx↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
    --   → (X : Idx M → Set)
    --   → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
    --   → (i : Idx M) (x : X i)
    --   → Idx↓ (Pb↓ M↓ X Y) (i , x) ↦ Σ (Idx↓ M↓ i) (λ j → Y i j x)
    -- {-# REWRITE Idx↓-Pb↓ #-}

    -- Cns↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
    --   → (X : Idx M → Set)
    --   → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
    --   → (i : Idx M) (x : X i)
    --   → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
    --   → (ϕ : Idx↓ (Pb↓ M↓ X Y) (i , x))
    --   → Cns↓ (Pb↓ M↓ X Y) ϕ (c , ν) ↦ Σ (Cns↓ M↓ (fst ϕ) c) (λ d → (p : Pos M c) → Y (Typ M c p) (Typ↓ M↓ d p) (ν p))
    -- {-# REWRITE Cns↓-Pb↓ #-}

  -- A previous version ...
  -- OverToOpetopicType : (M : 𝕄) (M↓ : 𝕄↓ M) → OpetopicType M
  -- Ob (OverToOpetopicType M M↓) = Idx↓ M↓ 
  -- Hom (OverToOpetopicType M M↓) =
  --   OverToOpetopicType (Slice (Pb M (Idx↓ M↓)))
  --     (Ext (Slice (Pb M (Idx↓ M↓))) (λ { ((i , j) , (c , ν)) → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν) }))

  OverToOpetopicType : (M : 𝕄) (M↓ : 𝕄↓ M) → OpetopicType M
  Ob (OverToOpetopicType M M↓) = Idx↓ M↓ 
  Hom (OverToOpetopicType M M↓) =
    OverToOpetopicType (Slice (Pb M (Idx↓ M↓)))
                       (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)))

  -- Okay.  This second construction is starting to grow on me.  By
  -- pulling back using the diagonal in this way, I think we get the
  -- same essentialy idea as before: a constructor is a constructor
  -- over with the specified typing function.  *But* in this new
  -- construction, the constructors are actually a tree which
  -- multiplies down to the specified constructor over.  And this was
  -- exactly what was missing before.  Okay, very nice.

  -- Yes, right.  This guys actually uses the multiplication of the
  -- monad over.

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where


    A : Idx M → Set
    A = Idx↓ M↓

    Slc : 𝕄
    Slc = Slice (Pb M A)

    W : Idx (Slice (Pb M A)) → Set
    W ((i , j) , (c , ν)) = Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν) 

    Y : Idx (Slice (Pb Slc W)) → Set
    Y ((i , j) , (c , ν)) = Σ (Cns↓ (Ext Slc W) j c) (λ d → Typ↓ (Ext Slc W) {f↓ = j} d == ν) 

    ob-fib : unique-action M A W
    ob-fib i c ν = claim 

      where claim : is-contr (Σ (A i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν)))
            claim = {!!} 

    hom-fib : unique-action Slc W Y
    hom-fib ((i , j) , ._ , ._) (lf .(i , j)) ϕ = has-level-in (ctr , unique)

      where ctr : (Σ (W ((i , j) , η M i , (λ _ → j))) (λ w → Y ((((i , j) , η M i , (λ _ → j)) , w) , lf (i , j) , ϕ)))
            ctr = (η↓ M↓ j , idp) , ϕ , idp

            unique : (y : Σ (W ((i , j) , η M i , (λ _ → j))) (λ w → Y ((((i , j) , η M i , (λ _ → j)) , w) , lf (i , j) , ϕ))) → ctr == y
            unique ((c , is-cst) , .ϕ , idp) = pair= (pair= {!!} {!!}) {!!}

            -- So, the claim is that

    hom-fib ((i , j) , ._ , ._) (nd σ δ ε) ϕ = {!!}


    -- hom-fib : unique-action Slc W Y
    -- hom-fib ((i , j) , (c , ν)) σ ϕ  = has-level-in (ctr , {!!})

    --   where ctr : Σ (W ((i , j) , c , ν)) (λ w → Y ((((i , j) , c , ν) , w) , σ , ϕ))
    --         ctr = ({!!} , {!!}) , (ϕ , idp) 

    -- Hmmm.  But on the other hand, if we are in the algebraic case,
    -- σ + ϕ should be witnessing that j is the multiplication of the
    -- tree, and hence the resulting W should be the composite of this
    -- guy, which should somehow be unique. 

    -- So, the pair σ ϕ determine a tree in M↓ whose multiplication
    -- should lie over c.  And whose decoration should agree.  But I
    -- don't see why this guy is unique as claimed ...

    -- So the second factor looks okay.  But for the first, we seem to
    -- need some kind of hypothesis: and it looks to be exactly that
    -- the monad over is "algebraic", i.e. comes from an algebra.

    -- Hmmm.  But actually, it looks even stronger, no?   Because the
    -- output (j) is also fixed.  Yeah, something appears to be wrong.
    -- Because it seems the hom will only be fibrant exactly when M↓
    -- really is the extension monad.

    -- Okay, interesting.  This doesn't quite look true in general.
    -- However, it will be true in the case of an oo-groupoid arising
    -- from a type.  And I think more generally when the monad over
    -- is arising from an algebra.

    -- On the other hand, I think it is true after a single slice.

    -- So it seems the idea for uniqueness might go something like this:
    -- If I have an opetopic type, when is it equivalent to the above
    -- construction applied to Ext M Ob?  Because this then starts to
    -- look like what you were doing above.  The condition is something
    -- like that it becomes terminal after a single slice.

    -- I feel like you're very close ....

  is-algebraic : (M : 𝕄) (M↓ : 𝕄↓ M) → Set
  is-algebraic M M↓ = (i : Idx M) (c : Cns M i)
    → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
    → is-contr (Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν)))  

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    slc-algebraic : is-algebraic M M↓ → is-algebraic (Slice (Pb M (Idx↓ M↓))) (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → ⊤)))
    slc-algebraic is-alg ((i , j) , ._ , ._) (lf .(i , j)) ϕ = has-level-in ((((j , tt) , η↓ M↓ j , {!!}) , {!!} , {!!}) , {!!})
    slc-algebraic is-alg ((i , j) , ._ , ._) (nd σ δ ε) ϕ = {!!}

    SM : 𝕄
    SM = Slice (Pb M (Idx↓ M↓))

    F : Idx SM → Set
    F ((i , j) , (c , ν)) = Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν)

    ext-algebraic : is-algebraic M M↓ → is-algebraic SM (Ext SM F)
    ext-algebraic is-alg ((i , j) , (c , ν)) σ ϕ = {!!}

      where hyp : is-contr (Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))
            hyp = {!!} 


    -- Mmmm.  So the problem is like that it's not the extension monad
    -- we should have next.  We need the data of a tree in M↓ which
    -- has d as it's type since this is exactly serving the purpose of
    -- linking the constructor over with the multiplication and what
    -- not.  But then I don't think this is just a extension monad.
    
    -- Fuck a duck.

    -- Yeah, so like it's totally clear when this happens: exactly
    -- when M↓ is the extension monad.  Something is wrong.

    -- Ahhh!  What am I missing? The fibration doesn't remember σ
    -- at all.  Doesn't even know about it.  But it should be
    -- using some extra witness to make things unique.

    -- What if we go the other way?  Hmmm.  I don't really see how
    -- that would help.

    -- slc-algebraic is-alg ((i , j) , ._ , ._) (lf .(i , j)) ϕ =
    --   has-level-in (((η↓ M↓ j , idp) , ϕ , idp) , {!!})
    -- slc-algebraic is-alg ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ =
    --   has-level-in ((({!μ↓ M↓ (fst (ϕ (inl unit))) ?!} , {!!}) , ϕ , idp) , {!!})

    -- So.

  -- AlgToOpType : (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) → OpetopicType M
  -- Ob (AlgToOpType M M↓ is-alg) = Idx↓ M↓
  -- Hom (AlgToOpType M M↓ is-alg) =
  --   AlgToOpType (Slice (Pb M (Idx↓ M↓)))
  --               (Ext (SM M M↓) (Fillers M M↓ is-alg)) {!!}

  -- -- unique-action : (M : 𝕄) (A : Idx M → Set)
  --   → (W : Idx (Slice (Pb M A)) → Set)
  --   → Set
  -- unique-action M A W = (f : Idx M) (σ : Cns M f)
  --   → (ν : (p : Pos M σ) → A (Typ M σ p))
  --   → is-contr (Σ (A f) (λ a → W ((f , a) , σ , ν)))
    
  -- record is-fibrant {M : 𝕄} (X : OpetopicType M) : Set where
  --   coinductive
  --   field

  --     base-fibrant : unique-action M (Ob X) (Ob (Hom X))
  --     hom-fibrant : is-fibrant (Hom X)

  -- open is-fibrant public
