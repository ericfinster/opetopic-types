{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb

module FreeAlg (M : 𝕄) (X : Idx M → Set) where

  record CnsFreeAlg {i : Idx M} (α : ⟦ M ⟧ X i) (c : Cns M i) : Set where
    constructor ⟦_∥_∥_⟧
    field
      δ-fr : (p : Pos M c) → Cns M (Typ M c p)
      ν-fr : (p : Pos M c) (q : Pos M (δ-fr p)) → X (Typ M (δ-fr p) q)
      -- f-fr : fst α == μ M c δ-fr
      -- o-fr : snd α == (λ p → ν-fr (μ-pos-fst M c δ-fr p) (μ-pos-snd M c δ-fr p)) 
      --        [ (λ x → (p : Pos M x) → X (Typ M x p)) ↓ f-fr ]
      e-fr : α == μ M c δ-fr , λ p → ν-fr (μ-pos-fst M c δ-fr p) (μ-pos-snd M c δ-fr p) 

  open CnsFreeAlg
  
  FreeAlgTyp : {i : Idx M} {α : ⟦ M ⟧ X i} (c : Cns M i)
    → CnsFreeAlg α c
    → (p : Pos M c) → ⟦ M ⟧ X (Typ M c p)
  FreeAlgTyp c cns p = δ-fr cns p , ν-fr cns p 

  -- Free-η↓ : {i : Idx M} (α : ⟦ M ⟧ X i)
  --   → CnsFreeAlg α (η M i)
  -- Free-η↓ (c , ν) = ⟦ η-dec M (Cns M) c ∥ {!!} ∥ {!!} ⟧

  Free-μ↓ : {i : Idx M} {c : Cns M i}
    → {δ : (p : Pos M c) → Cns M (Typ M c p)}
    → {α : ⟦ M ⟧ X i} (c↓ : CnsFreeAlg α c)
    → (δ↓ : (p : Pos M c) → CnsFreeAlg (FreeAlgTyp c c↓ p) (δ p))
    → CnsFreeAlg α (μ M c δ)
  Free-μ↓ {c = c} {δ = δ} ⟦ δ' ∥ ν' ∥ idp ⟧ δ↓ =
    ⟦ (λ p → δ-fr (δ↓ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p)) ∥
      (λ p q → ν-fr (δ↓ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p) q) ∥
      {!!} ⟧

      where claim : δ' == (λ p → μ M (δ p) (λ q → δ-fr (δ↓ p) q))
            claim = λ= (λ p → fst= (e-fr (δ↓ p))) 

  -- Indeed.  So this is essentially the right setup, but naively
  -- strictifying these equations looks dubious.  Well, I guess you
  -- could avoid the funext application by expandng out the actual
  -- equalities necessary here.  Maybe that's a first step....

  -- Gets a bit messy.

  module _ where

    -- Here's another approach specifying it as a kind of
    -- higher inductive fixed point ....
    
    postulate

      Fr : Idx M → Set
      Fr-Rel : Idx (Slice (Pb M Fr)) → Set 

      Fr-η : (i : Idx M)
        → X i → Fr i
        
      Fr-μ : (i : Idx M) (c : Cns M i)
        → (ν : (p : Pos M c) → Fr (Typ M c p))
        → Fr i 

      Fr-rel : (i : Idx M) (c : Cns M i)
        → (ν : (p : Pos M c) → Fr (Typ M c p))
        → Fr-Rel ((i , Fr-μ i c ν) , (c , ν))
      
      Fr-μ-pth : (i : Idx M) (c : Cns M i)
        → (ν : (p : Pos M c) → Fr (Typ M c p))
        → (f : Fr i) (r : Fr-Rel ((i , f) , (c , ν)))
        → Fr-μ i c ν == f 
    
      Fr-rel-tph : (i : Idx M) (c : Cns M i)
        → (ν : (p : Pos M c) → Fr (Typ M c p))
        → (f : Fr i) (r : Fr-Rel ((i , f) , (c , ν)))
        → transport (λ x → Fr-Rel ((i , x) , (c , ν))) (Fr-μ-pth i c ν f r) (Fr-rel i c ν) == r 


    -- Huh! Crazy!  So this is *much* more interesting than the above.
    -- But now, how do I "embed" this is a whole coinductive tower?
    -- Because I'll need to do this simultaneously for *all* the
    -- families.

    -- So suppose at the *current* stage I also add the specified
    -- elements of the relation.  Hmmm.  Then the thing is that

    -- Hmmm.  A curious thing: by adding *elements* to the higher
    -- families, we are adding *relations* to the lower ones via
    -- the fundamental theorem.

    -- So.  But can you do this uniformly in all the families?
    
    -- Okay, I think I have an idea: I think you should *separate*
    -- the definition of the constructors from that of the paths.
    -- Basically, you should recurse down the tower including all
    -- of the generating *elements*.  This should leave you with
    -- a multiplicative opetopic type.  Then, you're going to
    -- enforce the uniqueness afterwards.


    -- And now what? Well, now I want to "insert" a higher dimensional
    -- relation into the next family, namely, the one connecting the
    -- Fr-μ constructor to its output.

    -- But then I have to simultaneously add paths into both the base
    -- family and the family I am using to fill it.

  -- unique-action : (M : 𝕄) (A : Idx M → Set)
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

