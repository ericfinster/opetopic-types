{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module MonadOver where

  postulate

    𝕄↓ : 𝕄 → Set

    Frm↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Frm M → Set
    Cell↓ : {M : 𝕄} (M↓ : 𝕄↓ M) {f : Frm M} (f↓ : Frm↓ M↓ f) → Set
    Tree↓ : {M : 𝕄} (M↓ : 𝕄↓ M) {f : Frm M} (f↓ : Frm↓ M↓ f) → Set

    
