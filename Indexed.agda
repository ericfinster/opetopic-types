{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
-- open import Substitution

-- I have turned off positivity so as to be able to adapt old
-- code to this setup quickly for testing.  However, the non-
-- positivity can be avoided by using the three-field variant
-- of polynomials.  But grafting, substitution and so on would
-- need to be rewritten ...

module Indexed {ℓ} {I : Type ℓ} (P : Poly I) where

  -- Hmm. Okay.  But what if you just defined the operations by
  -- *recursion*.  You'll have to keep an equality, but it still
  -- looks like less than before ...

  Sort : ℕ → Type ℓ
  SPoly : (n : ℕ) → Poly (Sort n)

  data Oper : (n : ℕ) → Sort n → Type ℓ
  Params : (n : ℕ) {i : Sort n} (f : Oper n i) → Type ℓ
  Srts : (n : ℕ) {i : Sort n} {f : Oper n i} (p : Params n f) → Sort n

  data Tr (n : ℕ) : Sort n → Type ℓ

  Sort 0 = Ops P
  Sort (S n) = Σ (Sort n) (Oper n)

  Op (SPoly n) = Oper n
  Param (SPoly n) = Params n
  Srt (SPoly n) = Srts n
  
  -- The hypothetical multiplication 
  μ∞ : (n : ℕ) {i : Sort n} → Tr n i → Oper n i

  data Oper where
    frm : {i : I} {f : Op P i} (w : W P i) (α : Frame P w f) → Oper 0 (i , f)
    web : {n : ℕ} {i : Sort n} (w : Tr n i) → Oper (S n) (i , μ∞ n w)

  data Tr (n : ℕ) where
    leaf : {i : Sort n} → Tr n i
    node : {i : Sort n} (f : Oper n i)
      → (ϕ : (p : Params n f) → Tr n (Srts n p))
      → Tr n i
      
  Params = {!!}
  Srts = {!!}

  -- Params O (frm w α) = Node P w 
  -- Params (S n) (web w) = Node (SPoly n) w 

  -- Srts O {f = frm w α} = NodeSrt P w
  -- Srts (S n) {f = web w} = NodeSrt (SPoly n) w 
  
  -- Hmmm. Nope.  Annoyingly it looks like we need to copies of
  -- these functions. But the algorithm is identical.  There must
  -- be a way to abstract the situation ...

  -- subst₀ : {i : I} (w : W P i)
  --   → (κ : (g : Ops P) → Node P w g → W (SPoly 0) g)
  --   → W P i
  -- subst₀ (lf i) κ = lf i
  -- subst₀ (nd (f , ϕ)) κ = {!μ∞ 0 (κ (_ , f) (inl idp))!}

  -- subst : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
  --   → (κ : (g : Sort (S n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
  --   → W (SPoly n) i
  -- subst n w = {!!}

  -- -- Mmmm. So you still want the flattening function to work just
  -- -- on trees.

  -- -- Okay, so that's exactly what you thought ...
  -- μ∞ O (lf (i , f)) = frm (corolla P f) (corolla-lf-eqv P f)
  -- μ∞ O (nd (frm w α , κ)) = frm (subst₀ w κ ) {!!}
  -- μ∞ (S n) (lf (i , f)) = transport (Oper (S n)) (pair= idp {!!}) (web (corolla (SPoly n) f))
  -- μ∞ (S n) (nd (web w , κ)) = transport (Oper (S n)) (pair= idp {!!}) (web (subst n w κ))
  

  μ∞ = {!!}
