{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module SimpleOpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)

  Frm : ∀ {ℓ n} → 𝕆 ℓ n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → Frm X → Set ℓ
  Pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (t : Frm X) → Set ℓ

  postulate

    η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Cns X f 

    η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Pos X (η X f) f 

    η-pos-elim : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : {g : Frm X} (p : Pos X (η X f) g) → Set ℓ)
      → (p : P (η-pos X f))
      → {g : Frm X} (p : Pos X (η X f) g)
      → P p 

    μ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (κ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → Cns X f

    μ-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (κ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → {g : Frm X} (p : Pos X c g)
      → {h : Frm X} (q : Pos X (κ p) h)
      → Pos X (μ X c κ) h

    μ-pos-elim : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (κ : {g : Frm X} (p : Pos X c g) → Cns X g)
      → (P : {g : Frm X} (p : Pos X (μ X c κ) g) → Set ℓ)
      → (p : {g : Frm X} (p : Pos X c g)
             {h : Frm X} (q : Pos X (κ p) h)
             → P {h} (μ-pos X c κ p q))
      → {g : Frm X} (p : Pos X (μ X c κ) g)
      → P {g} p              

  data Pd {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) :
    (f : Frm Xₙ) (x : Xₛₙ f) (c : Cns Xₙ f)
    (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g)  → Set ℓ where

    lf : {f : Frm Xₙ} (x : Xₛₙ f)
      → Pd Xₙ Xₛₙ f x (η Xₙ f) (η-pos-elim Xₙ f (λ {g} p → Xₛₙ g) x) 

    nd : {f : Frm Xₙ} (c : Cns Xₙ f) (x : Xₛₙ f) 
      → (ν : {g : Frm Xₙ} (p : Pos Xₙ c g) → Xₛₙ g)
      → (δ : {g : Frm Xₙ} (p : Pos Xₙ c g) → Cns Xₙ g)
      → (θ : {g : Frm Xₙ} (p : Pos Xₙ c g)
             {h : Frm Xₙ} (q : Pos Xₙ (δ p) h)
           → Xₛₙ h)
      → (ε : {g : Frm Xₙ} (p : Pos Xₙ c g)
           → Pd Xₙ Xₛₙ g (ν p) (δ p) (θ p))
      → Pd Xₙ Xₛₙ f x (μ Xₙ c δ)
          (μ-pos-elim Xₙ c δ (λ {g} p → Xₛₙ g) θ) 

  𝕆 = {!!}
  Frm = {!!}
  Cns = {!!} 
  Pos = {!!} 
