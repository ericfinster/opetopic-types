{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FundamentalThm where

  -- The fundamental theorem of HoTT
  
  fundamental-thm : ∀ {i} (A : Type i) (P : A → Type i)
    → (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P))
    → (a₁ : A) → P a₁ ≃ (a₀ == a₁)
  fundamental-thm A P a₀ r is-c a₁ = equiv to from to-from from-to 

    where to :  P a₁ → a₀ == a₁
          to p = fst= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))

          from : a₀ == a₁ → P a₁
          from p = transport P p r

          to-from : (p : a₀ == a₁) → to (from p) == p
          to-from idp = ap fst= claim

            where claim : contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r) == idp
                  claim = contr-has-all-paths ⦃ =-preserves-contr {x = (a₀ , r)} {y = a₀ , r} is-c ⦄
                            (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r)) idp

          from-to : (p : P a₁) → from (to p) == p
          from-to p = to-transp (snd= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p)))


  -- The above can be interpreted as saying the space of unital, one
  -- side contractible relations on a type A is itself contractible.

  -- I would like to have a similar statement in dimension 2.

  -- Ok!  So HoTT already has exactly the type you have in mind: PathSeq!
  -- Great! and the composition 
  
  Filler₂ : (A : Set) → Set₁
  Filler₂ A = {a₀ a₁ : A} (s : a₀ =-= a₁) (t : a₀ == a₁) → Set

  is-fibrant₂ : (A : Set) (F : Filler₂ A) → Set
  is-fibrant₂ A F = {a₀ a₁ : A} (s : a₀ =-= a₁)
    → is-contr (Σ (a₀ == a₁) (F s))
  
  canonical-filler₂ : (A : Set) → Filler₂ A
  canonical-filler₂ A s t = ↯ s == t

  canonical-filler-is-fibrant : (A : Set) → is-fibrant₂ A (canonical-filler₂ A)
  canonical-filler-is-fibrant A s = pathfrom-is-contr (↯ s) 
  
  Pos₂ : {A : Set} {a₀ a₁ : A} → a₀ =-= a₁ → Set
  Pos₂ [] = ⊥
  Pos₂ (p ◃∙ s) = ⊤ ⊔ (Pos₂ s)

  Typ₂ : {A : Set} {a₀ a₁ : A}
    → (s : a₀ =-= a₁) (p : Pos₂ s)
    → A × A
  Typ₂ (_◃∙_ {a₀} {a₁} h s) true = a₀ , a₁
  Typ₂ (h ◃∙ s) (inr p) = Typ₂ s p

  -- Now we can define multiplication:
  μ₂ : {A : Set} {a₀ a₁ : A} 
    → (s : a₀ =-= a₁)
    → (δ : (p : Pos₂ s) → fst (Typ₂ s p) =-= snd (Typ₂ s p))
    → a₀ =-= a₁
  μ₂ [] δ = []
  μ₂ (p ◃∙ s) δ =
    let w = δ (inl unit)
        δ↑ p = δ (inr p)
    in w ∙∙ μ₂ s δ↑


  cmp : {A : Set} {a₀ a₁ : A} (s : a₀ =-= a₁) → a₀ == a₁
  cmp [] = idp
  cmp (idp ◃∙ s) = cmp s

  test : (A : Set) (F : Filler₂ A)
    → {a₀ a₁ : A} (s : a₀ =-= a₁)
    → F s (cmp s)
  test A F [] = {!!}
  test A F (idp ◃∙ s) = {!test A F s!}

  -- So, what's the idea? In the 1d case, the "canonification map" is
  -- given by transporting.  But in the current case, because of the
  -- asymmetry between source and target, there can't really be such
  -- a map.  So what could we use to replace it?

  -- If you define a fibration over the target which has contractible
  -- fibers.  Then it is equal to the path space for *any* choice of
  -- second argument.  In particular, it would be so for the composite.

  -- So does this give an answer? Focus on the target.  Work one shape
  -- at a time.  The relation is that of a pair of a tree and a relation
  -- element to the target.  What you need to know is that there is at
  -- least *one* tree that multiplies to that given target, and that the
  -- total space of a tree together with a relation is contractible.

  -- But what does that then show? It shows that relations between a
  -- given tree and it's composite is the same as relations between
  -- the tree an the target.  And what did we want to show?  That
  -- relations were the same as between the composite and the target.
  -- But now I think this would follow from fibrancy in the *other*
  -- direction, yeah?

  -- Okay, that is starting to sound good.  You should carry it
  -- through to make sure it really works.

  -- I don't think that works.

  -----------------------------------------------------------------------

  -- Okay, let's try something else.

  -- So, one thing that's clear is that, if you are fibrant, then the
  -- *globular type* extracted from the associated opetopic type
  -- conicides with the identity one.  This is clear because, if you
  -- admit an extension, then you fulfill the criterion for
  -- contractibility that gives the right answer on globular forms.

  -- So if you look at it this way, what you need to show is that there
  -- is at most one fibrant opetopic extension to a globular type.

  -- Right.  And I guess the answer is completely clear: given any shape,
  -- there will be a canonical globular one associated to it.  And this
  -- map will, iteratively, be an equivalence.
