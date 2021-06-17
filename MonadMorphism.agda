{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module MonadMorphism where

  -- My idea is to have monad morphisms which are not definitionally
  -- cartesian.  Rather cartesianness, as well as being an equivalence
  -- will be properties....
  
  postulate

    _⇒_ : 𝕄 → 𝕄 → Set 

    Idx⇒ : {M N : 𝕄} → M ⇒ N → Idx M → Idx N
    Cns⇒ : {M N : 𝕄} (ϕ : M ⇒ N) {i : Idx M}
      → Cns M i → Cns N (Idx⇒ ϕ i)
    Pos⇒ : {M N : 𝕄} (ϕ : M ⇒ N)
      → {i : Idx M} {c : Cns M i}
      → Pos M c → Pos N (Cns⇒ ϕ c)

    -- Definitional preservation of structure
    Typ⇒ : {M N : 𝕄} (ϕ : M ⇒ N)
      → (i : Idx M) (c : Cns M i) (p : Pos M c)
      → Typ N (Cns⇒ ϕ c) (Pos⇒ ϕ p) ↦
        Idx⇒ ϕ (Typ M c p) 
    {-# REWRITE Typ⇒ #-}

    η⇒ : {M N : 𝕄} (ϕ : M ⇒ N) (i : Idx M)
      → η N (Idx⇒ ϕ i) ↦ Cns⇒ ϕ (η M i)
    {-# REWRITE η⇒ #-}

    μ⇒ : {M N : 𝕄} (ϕ : M ⇒ N)
      → {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → μ N (Cns⇒ ϕ c) (λ p → {!!}) ↦ Cns⇒ ϕ (μ M c δ)

    -- Shit.  There it is.  You need the morphism to be cartesian to
    -- even describe what the induced decoration is.  This is really
    -- frustrating.

    -- Yet another example of the fact that the most natural setup
    -- would be for constructors to be fibered over their arities...
