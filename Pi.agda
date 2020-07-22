{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import OpetopicType
open import Pb
open import IdentityMonad
open import SigmaMonad

module Pi where

  -- We are going to start with the axiomatization of monadic terms
  postulate

    𝕋 : {M : 𝕄} (M↓ : 𝕄↓ M) → Set 

    idx : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
      → (i : Idx M) → Idx↓ M↓ i
      
    cns : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
      → {i : Idx M} (c : Cns M i)
      → Cns↓ M↓ (idx t i) c

    -- Term compatibility rewrites
    cns-typ : {M : 𝕄} {M↓ : 𝕄↓ M} 
      → (t : 𝕋 M↓) (i : Idx M)
      → (c : Cns M i) (p : Pos M c)
      → Typ↓ M↓ (cns t c) p ↦ idx t (Typ M c p)
    {-# REWRITE cns-typ #-}
    
    cns-η : {M : 𝕄} {M↓ : 𝕄↓ M} 
      → (t : 𝕋 M↓) (i : Idx M)
      → cns t (η M i) ↦ η↓ M↓ (idx t i)
    {-# REWRITE cns-η #-}

    cns-μ : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
      → (i : Idx M) (σ : Cns M i)
      → (δ : (p : Pos M σ) → Cns M (Typ M σ p))
      → cns t (μ M σ δ) ↦ μ↓ M↓ (cns t σ) (λ p → cns t (δ p))
    {-# REWRITE cns-μ #-}

    Slice𝕋 : {M : 𝕄} {M↓ : 𝕄↓ M}
      → 𝕋 M↓ → 𝕋 (Slice↓ M↓) 

  idxₛ : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
    → (f : Idxₛ M) → Idx↓ₛ M↓ f
  idxₛ t (i , c) = idx t i , cns t c

  cnsₛ : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
    → (f : Idxₛ M) (σ : Cnsₛ M f)
    → Cns↓ₛ M↓ (idxₛ t f) σ
  cnsₛ {M} t .(i , η M i) (lf i) = lf↓ (idx t i)
  cnsₛ {M} t .(_ , μ M σ δ) (nd σ δ ε) =
    let δ↓ p = cns t (δ p)
        ε↓ p = cnsₛ t (Typ M σ p , δ p) (ε p)
    in nd↓ (cns t σ) δ↓ ε↓ 

  postulate

    Pb𝕋 : {M : 𝕄} {M↓ : 𝕄↓ M} (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → (t : 𝕋 M↓) (ϕ : (i : Idx M) (x : X i) → Y i (idx t i) x)
      → 𝕋 (Pb↓ M↓ X Y) 

  Π' : (M : 𝕄) (M↓ : 𝕄↓ M)
    → (M↓↓ : 𝕄↓ (ΣM M M↓))
    → (X : OpetopicType (ΣM M M↓))
    → (Y : OpetopicTypeOver M↓↓ X)
    → (t : 𝕋 M↓↓)
    → OpetopicType M  
  Ob (Π' M M↓ M↓↓ X Y t) i = (j : Idx↓ M↓ i) (x : Ob X (i , j)) → Ob↓ Y (i , j) (idx t (i , j)) x
  Hom (Π' M M↓ M↓↓ X Y t) = {!!}

    where C : Idx M → Set
          C i = (j : Idx↓ M↓ i) (x : Ob X (i , j)) → Ob↓ Y (i , j) (idx t (i , j)) x

