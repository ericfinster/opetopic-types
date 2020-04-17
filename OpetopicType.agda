{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes

module SomeIdeas where

  record OpSig (n : ℕ) : Set₁ where
    field
    
      Frm : (o : 𝕆 n) → Set
      Cell : (o : 𝕆 n) (f : Frm o) → Set
      Tree : (o : 𝕆 n) (f : Frm o) (t : 𝕋 o) → Set

      Typ : (o : 𝕆 n) (t : 𝕋 o)
        → (f : Frm o) (σ : Tree o f t)
        → (p : Pos t)
        → Frm (Typₒ t p)

      -- Inh : (o : 𝕆 n) (t : 𝕋 o)
      --   → (f : Frm o) (σ : Tree o f t)
      --   → (p : Pos t)
      --   → Cell (Typₒ t p) (Typ o t f σ p)

      μ-frm : {o : 𝕆 n} (t : 𝕋 o)
        → (δ : (p : Pos t) → 𝕋 (Typₒ t p))
        → (f : Frm o)
        → (∂ : Tree o f (μₒ t δ))
        → (p : Pos t) → Frm (Typₒ t p)

      μ-tr : {o : 𝕆 n} (t : 𝕋 o)
        → (δ : (p : Pos t) → 𝕋 (Typₒ t p))
        → (f : Frm o)
        → (∂ : Tree o f (μₒ t δ))
        → (p : Pos t) → Tree (Typₒ t p) (μ-frm t δ f ∂ p) (δ p)

      μ-recons : {o : 𝕆 n} (t : 𝕋 o)
        → (δ : (p : Pos t) → 𝕋 (Typₒ t p))
        → (f : Frm o)
        → (∂ : Tree o f (μₒ t δ))
        → (ϕ : (p : Pos t) → Cell (Typₒ t p) (μ-frm t δ f ∂ p))
        → Tree o f t

  open OpSig

  module _ {n : ℕ} (A : OpSig n)
    (N : (o : 𝕆 n) (t : 𝕋 o) (f : Frm A o) (σ : Tree A o f t) (τ : Cell A o f) → Set) where
  
    Frmₛ : 𝕆 (S n) → Set
    Frmₛ (o ∣ t) = Σ (Frm A o) (λ f → Tree A o f t × Cell A o f)

    Cellₛ : (o : 𝕆 (S n)) → Frmₛ o → Set
    Cellₛ (o ∣ t) (f , σ , τ) = N o t f σ τ

    Treeₛ : (o : 𝕆 (S n)) → Frmₛ o → 𝕋 o → Set
    Treeₛ (o ∣ .(ηₒ o)) (f , ∂ , τ) (lfₒ .o) = {!!}
    Treeₛ (o ∣ .(μₒ t δ)) (f , ∂ , τ) (ndₒ .o t δ ε) = 
      Σ ((p : Pos t) → Cell A (Typₒ t p) (μ-frm A t δ f ∂ p)) (λ σ↓ →
         (p : Pos t) → Treeₛ _ (μ-frm A t δ f ∂ p , μ-tr A t δ f ∂ p , σ↓ p) (ε p))

  -- Now we define the slice.
  slice : {n : ℕ} (A : OpSig n)
    → (N : (o : 𝕆 n) (t : 𝕋 o) (f : Frm A o) (σ : Tree A o f t) (τ : Cell A o f) → Set)
    → OpSig (S n)
  Frm (slice A N) = Frmₛ A N
  Cell (slice A N) = Cellₛ A N
  Tree (slice A N) = Treeₛ A N
  Typ (slice A N) = {!!}
  μ-frm (slice A N) = {!!}
  μ-tr (slice A N) = {!!}
  μ-recons (slice A N) = {!!}

  record OpType {n : ℕ} (A : OpSig n) : Set₁ where
    coinductive
    field

      Next : (o : 𝕆 n) (t : 𝕋 o)
        → (f : Frm A o) (σ : Tree A o f t) (τ : Cell A o f)
        → Set

      Higher : OpType (slice A Next)


