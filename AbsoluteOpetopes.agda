{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import MiniUniverse
open import Decorations

module AbsoluteOpetopes where

  data 𝕆 : ℕ → Set
  data 𝕋 : {n : ℕ} → 𝕆 n → (P : ℙ) → (τ : Decor (𝕆 n) P) → Set

  data 𝕆 where
    ● : 𝕆 O 
    _▸_ : {n : ℕ} (f : 𝕆 n) {P : ℙ} {τ : Decor (𝕆 n) P}
      → 𝕋 f P τ → 𝕆 (S n)

  postulate

    η : {n : ℕ} (o : 𝕆 n)
      → 𝕋 o ⊤ₚ (term o)

    μ : {n : ℕ} {o : 𝕆 n} {P : ℙ} {τ : Decor (𝕆 n) P}
      → (t : 𝕋 o P τ)
      → {Q : El P → ℙ}
      → {ω : (p : El P) → Decor (𝕆 n) (Q p)}
      → (κ : (p : El P) → 𝕋 (app τ p) (Q p) (ω p))
      → 𝕋 o (Σₚ P Q) (times ω)

  data 𝕋 where

    obj : (P : ℙ) (t : Decor (𝕆 O) P)
      → 𝕋 ● P t

    lf : {n : ℕ} (o : 𝕆 n)
      → 𝕋 (o ▸ η o) ⊥ₚ null

    nd : {n : ℕ} {o : 𝕆 n} {P : ℙ} {τ : Decor (𝕆 n) P}
      → (t : 𝕋 o P τ)
      → {Q : El P → ℙ}
      → {ω : (p : El P) → Decor (𝕆 n) (Q p)}
      → (κ : (p : El P) → 𝕋 (app τ p) (Q p) (ω p))
      → {R : (p : El P) → ℙ}
      → {ζ : (p : El P) → Decor (𝕆 (S n)) (R p)}
      → (ε : (p : El P) → 𝕋 (app τ p ▸ κ p) (R p) (ζ p))
      → 𝕋 (o ▸ μ t κ) (⊤ₚ ⊔ₚ Σₚ P R) (plus (term (o ▸ t)) (times ζ)) 

