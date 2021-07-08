{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse
open import Decorations

module AbsoluteOpetopes where

  data 𝕆 : ℕ → Set

  data 𝕆Dec (n : ℕ) : ℙ → Set where
     null : 𝕆Dec n ⊥ₚ
     term : (o : 𝕆 n) → 𝕆Dec n ⊤ₚ
     plus : {U V : ℙ} → 𝕆Dec n U → 𝕆Dec n V
       → 𝕆Dec n (U ⊔ₚ V)
     times : {U : ℙ} {V : El U → ℙ}
       → (ρ : (u : El U) → 𝕆Dec n (V u))
       → 𝕆Dec n (Σₚ U V)

  postulate
  
    appₒ : {n : ℕ} {P : ℙ}
      → 𝕆Dec n P → El P → 𝕆 n

    app₀-term : (n : ℕ) 
      → (o : 𝕆 n) (p : El ⊤ₚ)
      → appₒ (term o) p ↦ o

    appₒ-plus-inl : (n : ℕ) (U V : ℙ)
      → (du : 𝕆Dec n U) (dv : 𝕆Dec n V)
      → (u : El U)
      → appₒ (plus du dv) (inlₚ V u) ↦ appₒ du u 

    appₒ-plus-inr : (n : ℕ) (U V : ℙ)
      → (du : 𝕆Dec n U) (dv : 𝕆Dec n V)
      → (v : El V)
      → appₒ (plus du dv) (inrₚ U v) ↦ appₒ dv v

    appₒ-times : (n : ℕ) (U : ℙ) (V : El U → ℙ)
       → (ρ : (u : El U) → 𝕆Dec n (V u))
       → (u : El U) (v : El (V u))
       → appₒ (times ρ) ⟦ U , V ∣ u , v ⟧ₚ ↦ appₒ (ρ u) v 
    
  data 𝕋 : {n : ℕ} → 𝕆 n → (P : ℙ) → (τ : 𝕆Dec n P) → Set

  data 𝕆 where
    ● : 𝕆 O 
    _▸_ : {n : ℕ} (f : 𝕆 n) {P : ℙ} {τ : 𝕆Dec n P}
      → 𝕋 f P τ → 𝕆 (S n)

  postulate

    η : {n : ℕ} (o : 𝕆 n)
      → 𝕋 o ⊤ₚ (term o)

    μ : {n : ℕ} {o : 𝕆 n} {P : ℙ} {τ : 𝕆Dec n P}
      → (t : 𝕋 o P τ)
      → {Q : El P → ℙ}
      → {ω : (p : El P) → 𝕆Dec n (Q p)}
      → (κ : (p : El P) → 𝕋 (appₒ τ p) (Q p) (ω p))
      → 𝕋 o (Σₚ P Q) (times ω)

  data 𝕋 where

    obj : (P : ℙ) (t : 𝕆Dec O P)
      → 𝕋 ● P t

    lf : {n : ℕ} (o : 𝕆 n)
      → 𝕋 (o ▸ η o) ⊥ₚ null

    nd : {n : ℕ} {o : 𝕆 n} {P : ℙ} {τ : 𝕆Dec n P}
      → (t : 𝕋 o P τ)
      → {Q : El P → ℙ}
      → {ω : (p : El P) → 𝕆Dec n (Q p)}
      → (κ : (p : El P) → 𝕋 (appₒ τ p) (Q p) (ω p))
      → {R : (p : El P) → ℙ}
      → {ζ : (p : El P) → 𝕆Dec (S n) (R p)}
      → (ε : (p : El P) → 𝕋 (appₒ τ p ▸ κ p) (R p) (ζ p))
      → 𝕋 (o ▸ μ t κ) (⊤ₚ ⊔ₚ Σₚ P R) (plus (term (o ▸ t)) (times ζ)) 
