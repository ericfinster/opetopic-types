{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ n} (X : 𝕆 ℓ n) → 𝒪 n → Set ℓ
  Cell : ∀ {ℓ n} (X : 𝕆 ℓ n) (o : 𝒪 n) → Frm X o → Set ℓ
  Pd : ∀ {ℓ n} (X : 𝕆 ℓ n) {o : 𝒪 n} (f : Frm X o) → 𝒯r o → Set ℓ 

  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) =
    Σ (𝕆 ℓ n) (λ Xₙ →
      (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ)
  
  Frm X ● = X × X
  Frm X (o ▸ τ) = {!!}
  
  Cell = {!!}
  
  Pd = {!!} 


  postulate

    η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o) (x : Cell X o f) 
      → Pd X f (ηₒ o) 

    μ : ∀ {ℓ n} {X : 𝕆 ℓ n} 
      → {o : 𝒪 n} (f : Frm X o) (τ : 𝒯r o)
      → (ρ : Pd X f τ)
      → {κ : (p : Pos τ) → 𝒯r (Typ τ p)}
      → (δ : (p : Pos τ) → Frm X (Typ τ p))
      → (ε : (p : Pos τ) → Pd X (δ p) (κ p))
      → Pd X f (μₒ τ κ) 

  -- 𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  -- Frm : ∀ {ℓ n} (X : 𝕆 ℓ n) → 𝒪 n → Set ℓ
  -- Pd : ∀ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ) 
  --   → {o : 𝒪 n} (f : Frm Xₙ o) (τ : 𝒯r o) → Set ℓ 

  -- 𝕆 ℓ O = Set ℓ
  -- 𝕆 ℓ (S n) =
  --   Σ (𝕆 ℓ n) (λ Xₙ →
  --     (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ)
  
  -- Frm X ● = X × X 
  -- Frm (Xₙ , Xₛₙ) (o ▸ τ) =
  --   Σ (Frm Xₙ o) (λ f →
  --     Pd Xₙ Xₛₙ f τ × Xₛₙ o f)

  -- postulate

  --   η : ∀ {ℓ n} {Xₙ : 𝕆 ℓ n} {Xₛₙ : (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ} 
  --     → {o : 𝒪 n} {f : Frm Xₙ o} (x : Xₛₙ o f) 
  --     → Pd Xₙ Xₛₙ f (ηₒ o) 

  --   μ : ∀ {ℓ n} {Xₙ : 𝕆 ℓ n} {Xₛₙ : (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ}
  --     → {o : 𝒪 n} (f : Frm Xₙ o) (τ : 𝒯r o)
  --     → (ρ : Pd Xₙ Xₛₙ f τ)
  --     → {κ : (p : Pos τ) → 𝒯r (Typ τ p)}
  --     → (δ : (p : Pos τ) → Frm Xₙ (Typ τ p))
  --     → (ε : (p : Pos τ) → Pd Xₙ Xₛₙ (δ p) (κ p))
  --     → Pd Xₙ Xₛₙ f (μₒ τ κ) 


  -- data Pd' {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ) : 
  --   {o : 𝒪 n} (f : Frm Xₙ o) (τ : 𝒯r o) → Set ℓ where

  --   lf' : {o : 𝒪 n} (f : Frm Xₙ o) (x : Xₛₙ o f)
  --     → Pd' Xₙ Xₛₙ {!!} {!!} 

  -- -- No.  This is certainly wrong ...
  -- -- Okay.  What if we add a "cell" fibration, which trivially computes
  -- -- back to the given one.  Maybe this will let us give these guys
  -- -- simpler types? 

  -- -- data 𝒯r where
  -- --   arr : 𝒯r ●
  -- --   lf : {n : ℕ} (o : 𝒪 n) → 𝒯r (o ▸ ηₒ o)
  -- --   nd : {n : ℕ} (o : 𝒪 n) (τ : 𝒯r o)
  -- --     → (δ : (p : Pos τ) → 𝒯r (Typ τ p))
  -- --     → (ε : (p : Pos τ) → 𝒯r (Typ τ p ▸ δ p))
  -- --     → 𝒯r (o ▸ μₒ τ δ)


  -- Pd Xₙ Xₛₙ {o = ●} f τ = Xₛₙ ● f
  -- Pd Xₙ Xₛₙ {o = o ▸ τ} f υ = {!!}

  -- -- But now we have too many, which is weird!
  -- -- Again, problem is that we don't want to put the whole opetopic type
  -- -- in the index.


