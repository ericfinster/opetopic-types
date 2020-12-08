{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module UnivalentMonad where

  postulate

    𝕌 : Set
    El : 𝕌 → Set

    ⊤ᵤ : 𝕌
    ttᵤ : El ⊤ᵤ
    
    ⊤ᵤ-elim : (P : El ⊤ᵤ → Set)
      → (ttᵤ* : P ttᵤ)
      → (u : El ⊤ᵤ) → P u

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (P : 𝕌)
      → Idx M → (El P → Idx M) → Set

    η : (M : 𝕄) (i : Idx M)
      → Cns M ⊤ᵤ i (⊤ᵤ-elim (cst (Idx M)) i) 




  -- Actually, I kind of have an idea: what if monad was *codefined*
  -- with some notion of univalent universe? Then you could posit the
  -- type constructors necessary as well as their
  -- elimination/computation rules.  I wonder how far this can go
  -- .....
