{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import MiniUniverse
open import AbsoluteOpetopicTypes
open import DependentOpetopicType

module Scratch where

  --
  --  Okay, here are the terminal and identity opetopic types.
  -- 

  Term : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n) → 𝕆∞ X
  Head (Term X) _ = Lift ⊤
  Tail (Term X) = Term (X , cst (Lift ⊤))

  Idₒ : 𝕆∞ {ℓ = lzero} {n = O} ⊤
  Head Idₒ ⟪ f , P , τ ⟫ = is-contr (El P)
  Tail Idₒ = Term (⊤ , λ A → is-contr (El (pos A)))

  record 𝕆↓∞ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X∞ : 𝕆∞ X) (X↓ : 𝕆↓ ℓ↓ X) : Set (lmax ℓ (lsucc ℓ↓)) where
    coinductive
    field
      Head↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) (x : Head X∞ f) → Set ℓ↓
      Tail↓ : 𝕆↓∞ (Tail X∞) (X↓ , Head↓)

  𝕆↓Id : Set → Set₁
  𝕆↓Id A = 𝕆↓∞ Idₒ (cst A) 
  
  ℙType : Set → Set₁
  ℙType X = 𝕆∞ {lzero} X

  -- Oh.  So we can give this as a predicate.
  is-unary : (A : Set) (P : ℙType A) → Set
  is-unary A P = (α : Arity A) (x : Head P α) → is-contr (El (pos α)) 

  --
  --  Kan conditions
  --

  FrmPos : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X) → ℙ
  FrmPos {n = O} A = pos A
  FrmPos {n = S n} (f , x , fₛ) = pos (opr fₛ)

  -- An opetopic type with decidable frame positions
  DecPos : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) → Set ℓ 
  DecPos Xₙ = {f : Frm Xₙ} (p q : El (FrmPos f))
    → Dec (p == q) 

  PFrm↓ : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    → (f : Frm X) (p : El (FrmPos f)) → Set ℓ↓
  PFrm↓ {n = O} X↓ ⟪ x , P , t ⟫ p =
    Σ (X↓ x) (λ x↓ → (p' : El P) (p≠p' : p ≠ p') → X↓ (t p'))
  PFrm↓ {n = S n} (X↓ₙ , X↓ₛₙ) (f , x , fₛ) p =
    Σ (Frm↓ X↓ₙ f) (λ f↓ →
    Σ (X↓ₛₙ f↓ x) (λ x↓ →
    Σ (Opr↓ X↓ₙ f↓ (opr fₛ)) (λ opr↓ →
      (p' : El (pos (opr fₛ))) (p≠p' : p ≠ p')
            → X↓ₛₙ (typ↓ opr↓ p') (dec fₛ p'))))

  FillType : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    → (f : Frm X) (p : El (FrmPos f))
    → (pf : PFrm↓ X↓ f p) → Set ℓ↓
  FillType {n = O} X↓ ⟪ x , P , t ⟫ p _ = X↓ (t p)
  FillType {n = S n} (X↓ₙ , X↓ₛₙ) (f , x , fₛ) p (f↓ , x↓ , opr↓ , pdec) =
    X↓ₛₙ (typ↓ opr↓ p) (dec fₛ p)
    
  plug : ∀ {ℓ ℓ↓} {n : ℕ} {X : 𝕆 ℓ n} (X↓ : 𝕆↓ ℓ↓ X)
    → (D : DecPos X)
    → (f : Frm X) (p : El (FrmPos f))
    → (pf : PFrm↓ X↓ f p) (xp : FillType X↓ f p pf)
    → Frm↓ X↓ f
  plug {n = O} X↓ D f p (x , ϕ) xp = x , pdec

    where pdec : (p' : El (pos f)) → X↓ (typ f p')
          pdec p' with D {f = f} p p'
          pdec .p | inl idp = xp
          pdec p' | inr p≠p' = ϕ p' p≠p'
          
  plug {n = S n} (X↓ₙ , X↓ₛₙ) D (f , x , fₛ) p (f↓ , x↓ , opr↓ , ϕ) xp =
    f↓ , x↓ , ⟪ opr↓ , pdec ⟫f↓

    where pdec : (p' : El (pos (opr fₛ))) → X↓ₛₙ (typ↓ opr↓ p') (dec fₛ p')
          pdec p' with D {f = f , x , fₛ} p p'
          pdec .p | inl idp = xp
          pdec p' | inr p≠p' = ϕ p' p≠p'
          

