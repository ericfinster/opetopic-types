{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Poly 
open import Inspect

module PolyMonads where

  data Mnd : Type₀ where
    𝕌 : Mnd

  record Prof (I : Type₀) : Type₀ where
    constructor prof
    field
      P : Type₀
      τ : P → I

  open Prof public

  ΣProf : {I : Type₀} (p : Prof I) (δ : P p → Prof I) → Prof I
  ΣProf p δ = prof (Σ (P p) (P ∘ δ)) (λ pq → τ (δ (fst pq)) (snd pq))
  
  postulate
  
    Idx : Mnd → Type₀

    γ : (M : Mnd) → Idx M → Prof (Idx M) → Type₀

    η : (M : Mnd) (i : Idx M) → γ M i (prof ⊤ (cst i))

    μ : (M : Mnd) (i : Idx M) (p : Prof (Idx M)) (c : γ M i p)
      → (δ : (q : P p) → Σ (Prof (Idx M)) (γ M (τ p q)))
      → γ M i (ΣProf p (fst ∘ δ))

  -- Okay, but I think I see what is going to happen here:  without strict associativity
  -- of Σ, it seems that the monad laws will not be well typed.  Indeed, they will be
  -- constructors over two different profiles, linked by a sigma unit or associativity.

  module _ (M : Mnd) where

    I-slc : Type₀
    I-slc = Σ (Idx M) (λ i → Σ (Prof (Idx M)) (λ p → γ M i p))

    data SlcCons : I-slc → Prof (I-slc) → Type₀ where
      dot : (i : Idx M) → SlcCons (i , prof ⊤ (cst i) , η M i) (prof ⊥ ⊥-elim)
      box : (i : Idx M) (p : Prof (Idx M)) (c : γ M i p)
        → (δ : (q : P p) → Σ (Prof (Idx M)) (γ M (τ p q)))
        → (ε : (q : P p) → Σ (Prof (I-slc)) (SlcCons (τ p q , δ q)))
        → SlcCons (i , ΣProf p (fst ∘ δ) , μ M i p c δ)
                  (prof (⊤ ⊔ Σ (P p) (λ p → P (fst (ε p))))
                        (λ { (inl unit) → i , p , c ;
                             (inr (a , b)) → τ (fst (ε a)) b }))

    -- Okay.  So this is pretty interesting.  It essentially builds the place calculation
    -- into the indexing of the type.  Is there, like, some kind of hope that this has
    -- better calculational properties?  Dunno.  Probably not.

    -- But it's still pretty interesting.

    -- Uh, yeah, I'm not quite sure what will happen.  I mean, it certainly feels like the lack
    -- of boilerplate rewrites and so on for places should vastly simplify things.
