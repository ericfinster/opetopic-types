{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module Frame {I : Type₀} (P : Poly I) where

  record Frame {i : I} (w : W P i) (c : γ P i) : Type₀ where
    constructor frm
    field

      frm-eqv : leaf P w ≃ ρ P i c
      frm-coh : (l : leaf P w) → leaf-type P w l == τ P i c (–> frm-eqv l)

  open Frame public

  -- We show that a frame induces an equivalence of spaces of decorations.
  module _ {i : I} (c : γ P i) (w : W P i) (f : Frame w c) (X : I → Type₀) where
  
    dec-to : (δ : (p : ρ P i c) → X (τ P i c p))
      → (l : leaf P w) → X (leaf-type P w l)
    dec-to δ l = transport X (! (frm-coh f l)) (δ (–> (frm-eqv f) l))

    dec-from : (ε : (l : leaf P w) → X (leaf-type P w l))
      → (p : ρ P i c) → X (τ P i c p)
    dec-from ε p = transport X coh (ε (<– (frm-eqv f) p))

      where coh : leaf-type P w (is-equiv.g (snd (frm-eqv f)) p) == τ P i c p
            coh = frm-coh f (<– (frm-eqv f) p) ∙ ap (τ P i c) (<–-inv-r (frm-eqv f) p)

  -- Oh.  Interesting.  What if there was a notion of *frame-over* where the tree
  -- and constructor could live over an equality in the index.  Because right now,
  -- you can't transport frames along either equivalences of trees or constructors,
  -- you have to do both.  But since the typing of the leaves is by an equality,
  -- why not also the typing of the root?
