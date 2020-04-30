{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import OpetopicType
-- open import FundamentalThm

module InfinityGroupoid where

  ∞-Rel : (A : Set) → Set₁
  ∞-Rel A = OpetopicType (IdMnd A) 

  -- An "n-loop" monad is one equipped with an augmentation to the
  -- n-th slice of the identity.  I guess the first thing would be
  -- to show that an opetopic type really admits such a thing.

  -- Of course, as you've set it up, you need to insert a bunch of
  -- trivial pullbacks in order to really make this true.  Or
  -- transport along the equivalence showing that these are isomorphic
  -- the the original monad.  Annoying.
  
  𝕃Mnd : ℕ → Set
  𝕃Mnd n = 𝕄↓ (𝕆Mnd n)
  
  is-trivial-for' : (A : Set) {n : ℕ} (L : 𝕃Mnd n) → Set
  is-trivial-for' A {n} L = (f : Frm (𝕆Mnd n)) → Frm↓ L f ≃ A

  is-trivial-for : (A : Set) {n : ℕ} (L : 𝕃Mnd n) → Set
  is-trivial-for A {n} L = (f : Frm (𝕆Mnd n)) (σ : Tree (𝕆Mnd n) f)
    → (Σ (Frm↓ L f) (λ f↓ → Tree↓ L f↓ σ)) ≃ A

  -- Okay, so, what you wanted to say is that the square of constructors
  -- over was a pullback square.  And I think that translates to the
  -- following: 
  trees-over-are-pullback : (A : Set) {n : ℕ} (L : 𝕃Mnd n) → Set
  trees-over-are-pullback A {n} L = (f : Frm (𝕆Mnd n)) →
    (σ : Tree (𝕆Mnd n) f) (f↓ : Frm↓ L f) → is-contr (Tree↓ L f↓ σ)

  -- Right.  This should say that fiberwise over Frm, we see a product.
  -- In particular, given a frame↓ and a choice of tree, there is a
  -- *unique* decoration lifting it.  Great, now we're making some
  -- progress.

  -- And it seems as though you could in fact axiomatize this with
  -- respect to a choice of filling fibration over the slice: given a
  -- choice of fillers, the constructors over will be pairs of a
  -- constuctor and a decoration.  So we can assert that this space of
  -- decorations is contractible, and that will have the same effect.

  -- In the case of opetopes, this will force the constructors over
  -- fibration to have discrete fibers, as there is just a set of
  -- opetopes over a given one.

  -- Given this, how does one define the filling relation? Here you
  -- could use the inductive presentation.  Or just a proof that
  -- the decoration is the canonical one? 
  
  -- I feel like there's a bit more here: these two equivalences
  -- should be compatible in a sense which I cannot yet make
  -- completely precise....

  -- But now that I've thought more about these higher degenerate
  -- relations, I guess that is a reasonable picture of what this
  -- equivalence is giving us: for each point a : A, we should think
  -- of the associated frame over as the "completely degenerate opetope
  -- at a:A".

  -- But then, in analogy with what you were doing this morning, the
  -- space of fillers for the slice should just be the relation saying
  -- that, for each (a:A), the completely degenerate opetope at (a:A)
  -- admits a relation to the completely degenerate tree for any
  -- element of the fiber over this choice.

  -- Okay, yes, here is what I think happens: when you pick the set of
  -- fillers and perform the pullback construction, the resulting
  -- monad should indeed have *both* the frames and constructor
  -- fibrations as constant at A.  The *slice* of this monad now has
  -- frames which look like spheres in A and constructors which look
  -- like "webs" in A. When we now chose fillers, we do it in such a
  -- way as to chose a null-homotopy of the sphere in A.  And then the
  -- constructors of the pullback will look like webs with each "hole"
  -- filled with a nullhomotopy, which is why they *again* become
  -- contractible and the fibration becomes trivial.

  canonical-extension : (A : Set) {n : ℕ} (L : 𝕃Mnd n)
    → (is-triv : is-trivial-for A L)
    → (f : Frm (𝕆Mnd n)) (σ : Tree (𝕆Mnd n) f)
    → (f↓ : Frm↓ L f) → Set
  canonical-extension = {!!}


  -- Now.  We must use this information to construct the next space
  -- of fillers.  But I wonder if we don't need one more statement:
  -- that the equivalence above is somehow compatible with the monad
  -- structure.  And then this is what lets us define the new space
  -- of fillers as equality in some derived multiplication?

  -- Okay, is this the correct statement? Yeah, it looks about right:
  -- after fixing the shape, the total space is supposed to be maps
  -- from the opetope to A itself, and since opetopes are contractible
  -- this should be A.
  
  -- Indeed.  Now the idea is to show something like the following:
  --
  --  1) Given this hypothesis, the space of filling fibrations
  --     the slice/pb of which *also* satisfies this condition is
  --     contractible.
  --
  --  2) If an opetopic type is fibrant, then all of its slices
  --     satisfy this condition.
  --

  -- Mmmm.  Okay.  But there is some annoying shifting going on
  -- because of the insertion of the pullback construction.  Yeah,
  -- this makes we want to go back to the version where these two
  -- things were kind of simultaneous.

  -- I see.  Yeah, so the "generic" if you will data for a slice is a
  -- polynomial extension: both an extension of the frames and the
  -- constructors, but also equipped with the data of a typing
  -- function for the constructor extension.  I think this is what you
  -- were missing last time.

  -- In any case, it's kind of funny because you actually have the
  -- choice, when set up this way, to extend the fillers *twice*.  And
  -- it's this ambiguity which is really bothering me at the point
  -- because it introduces a bunch of non-canonical equivalences that
  -- I guess you will have to transport over.



  -- The combination of these two statements should then show that the
  -- space of oo-groupoid structures on a type A is contractible.

  -- So, the question is, given such a setup, what *is* the formula
  -- for the extension that you claim exists.



  -- So, then, is there a way to define what is an opetopic type
  -- which removes this ambiguity? Hmmm.  I feel like it will end
  -- up being very close to what you had before.

  -- Right, and so it's tempting to rewrite the definition of the
  -- pullback as giving a monad over and then taking Σ.


  -- module _ {A : Set} (R : ∞-Rel A) (is-fib : is-fibrant R) where

  --   rel : A → A → Set
  --   rel a₀ a₁ = Flr R a₀ a₁

  --   refl : (a : A) → rel a a
  --   refl a = fst (fst (has-level-apply (base-fibrant (hom-fibrant is-fib) (unit , a , a) (lf a)))) 

  --   rel-is-id : (a₀ : A) (a₁ : A) → rel a₀ a₁ ≃ (a₀ == a₁)
  --   rel-is-id a₀ a₁ = fundamental-thm A (λ a → rel a₀ a) a₀ (refl a₀)
  --     (base-fibrant is-fib unit a₀) a₁

  -- -- A lemma about path spaces needed below
  -- module _ {i} {A : Type i} where
    
  --   lemma-to : {a₀ a₁ : A}
  --     → (p : a₀ == a₁) (aut : a₁ == a₁)
  --     → (q : a₀ == a₁)
  --     → p == q → p ∙ aut == q
  --   lemma-to p aut q α = {!!}


  -- module _ {M : 𝕄} (F : Filler M) where

  --   postulate

  --     F-unique : has-unique-comps M F 

  --     G₀ : Filler (Slice M F)
  --     G₁ : Filler (Slice M F)

  --     G₀-unique : has-unique-comps (Slice M F) G₀
  --     G₁-unique : has-unique-comps (Slice M F) G₁

  --   tgt-auto : {f : Frm M} {σ : Tree M f} {τ : Cell M f}
  --     → (θ₀ θ₁ : Cell (Slice M F) (f , σ , τ)) → τ == τ
  --   tgt-auto {f} {σ} {τ} θ₀ θ₁ = fst= (contr-has-all-paths ⦃ F-unique f σ ⦄ (τ , θ₀) (τ , θ₁))

  --   cell-over : {f : Frm M} {σ : Tree M f} {τ : Cell M f}
  --     → (θ₀ θ₁ : Cell (Slice M F) (f , σ , τ))
  --     → θ₀ == θ₁ [ (λ x → Cell (Slice M F) (f , σ , x)) ↓ tgt-auto θ₀ θ₁ ]
  --   cell-over {f} {σ} {τ} θ₀ θ₁ = snd= (contr-has-all-paths ⦃ F-unique f σ ⦄ (τ , θ₀) (τ , θ₁))

  --   claim : {f : Frm (Slice M F)}
  --     → (σ : Tree (Slice M F) f) (τ : Cell (Slice M F) f)
  --     → G₀ σ τ ≃ G₁ σ τ
  --   claim {f = f , σ₀ , τ₀} σ τ = (G₁-nf)⁻¹ ∘e left-with ∘e G₀-nf

  --     where G₀-nf : G₀ σ τ ≃ (comp-fun (Slice M F) G₀ G₀-unique σ == τ)
  --           G₀-nf = fillers-are-pths (Slice M F) G₀ G₀-unique σ τ

  --           G₁-nf : G₁ σ τ ≃ (comp-fun (Slice M F) G₁ G₁-unique σ == τ)
  --           G₁-nf = fillers-are-pths (Slice M F) G₁ G₁-unique σ τ

  --           θ₀ : F σ₀ τ₀
  --           θ₀ = comp-fun (Slice M F) G₀ G₀-unique σ
            
  --           θ₁ : F σ₀ τ₀
  --           θ₁ = comp-fun (Slice M F) G₁ G₁-unique σ

  --           left-with : (θ₀ == τ) ≃ (θ₁ == τ)
  --           left-with = {!!}

  --   -- Hmmm.  We're getting stuck here.  What happens is that the
  --   -- filling spaces are equivalent up to a kind of conjugation.
  --   -- There must be some kind of way to generalize so that this is
  --   -- sufficient for what you want.

  --   -- Okay, here is a possibility: maybe fibrant is not enough, and
  --   -- you want to be looking at some kind of restricted space of
  --   -- extensions.  Then the idea is that the identity types lie in
  --   -- this restricted space.

  --   -- And I think there is a kind of candidate: the idea is that you
  --   -- should look at *natural* extensions.  I'm not sure what I mean
  --   -- by this in the general case, but I'm thinking about what
  --   -- characterizes composition, and I think the point is that it is
  --   -- sufficient to have naturality because then Yoneda kicks in and
  --   -- says that it must be given by composition with a fixed path,
  --   -- namely, the image of the identity.

  --   -- So you should give a quick sketch of the low dimensional yoneda
  --   -- guy, because I think this is the dimension 1 case of saying
  --   -- that the extension is unique.  At least it's not completely far
  --   -- fetched ...
