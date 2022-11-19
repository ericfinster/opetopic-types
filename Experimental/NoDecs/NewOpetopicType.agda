{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.NoDecs.NewOpetopicType where

  --
  --  Opetopic Types
  --
  
  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)

  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  Web : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → Frm X → Type ℓ

  {-# TERMINATING #-}
  Pos : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {f : Frm X} (w : Web X f)
    → Type ℓ 

  Typ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {f : Frm X} (w : Web X f)
    → (p : Pos X w) → Frm X 

  Dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {f : Frm X} (w : Web X f)
    → (P : Pos X w → Type ℓ)
    → Type ℓ 

  _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {f : Frm X} {w : Web X f}
    → {P : Pos X w → Type ℓ}
    → (δ : Dec w P) (p : Pos X w)
    → P p 

  --
  --  Monadic Structure
  --

  η : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → (f : Frm X) → Web X f

  postulate

    η-dec : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (p : P f)
      → Dec (η X f) (λ q → P (Typ X (η X f) q))

    μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → {f : Frm X} (w : Web X f)
      → (δ : Dec w (λ p → Web X (Typ X w p)))
      → Web X f 

    μ-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (w : Web X f)
      → (δ : Dec w (λ p → Web X (Typ X w p)))
      → (ε : Dec w (λ p → Dec (δ ⊚ p) (λ q → P (Typ X (δ ⊚ p) q))))
      → Dec (μ w δ) (λ q → P (Typ X (μ w δ) q)) 

    ν : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → {f : Frm X} (w : Web X f)
      → (P Q : Pos X w → Type ℓ)
      → (σ : (p : Pos X w) → P p → Q p)
      → Dec w P
      → Dec w Q 

  --
  --  Laws
  --
  
  postulate
  
    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {f : Frm X} (w : Web X f)
      → μ w {!!} ↦ w 

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (f : Frm X) (δ : Dec (η X f) (λ p → Web X (Typ X (η X f) p)))
      → μ (η X f) δ ↦ {!!}

    -- μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    --   → {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
    --   → {f : Frm X 𝑜} (c : Cns X f 𝑝)
    --   → μ X c (λ p → η X (Shp X c p)) ↦ c
    -- {-# REWRITE μ-unit-r #-}

  --
  --  Definitions of opeotpic types and frames
  --

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ w ∈ Web X f ]
    Σ[ dec ∈ Dec w (λ p → P (Typ X w p)) ] 
    P f

  data Pd {n ℓ} {X : 𝕆Type n ℓ} (P : Frm X → Type ℓ) : Frm (X , P) → Type ℓ where

    lf : (f : Frm X) (p : P f)
      → Pd P (f , η X f , η-dec X P f p , p)

    nd : (f : Frm X) (w : Web X f)
      → (α : Dec w (λ p → Web X (Typ X w p)))
      → (β : Dec w (λ p → P (Typ X w p)))
      → (γ : Dec w (λ p → Dec (α ⊚ p) (λ q → P (Typ X (α ⊚ p) q))))
      → (δ : Dec w (λ p → Pd P (Typ X w p , α ⊚ p , γ ⊚ p , β ⊚ p)))
      → (x : P f)
      → Pd P (f , μ w α , μ-dec P w α γ , x)
    
  Web {zero} X f = Unit*
  Web {suc n} (X , P) = Pd P

  Pos {zero} X w = Unit*
  Pos {suc n} X (lf f p) = Lift ⊥
  Pos {suc n} (X , P) (nd f w α β γ δ x) =
    Unit ⊎ (Σ (Pos {n} X w) (λ p → Pos {suc n} (X , P) (δ ⊚ p)))
  
  Typ {zero} X w p = tt*
  Typ {suc n} (X , P) (nd f w α β γ δ x) (inl tt) = f , w , β , x
  Typ {suc n} (X , P)  (nd f w α β γ δ x) (inr (p , q)) =
    Typ {suc n} (X , P) (δ ⊚ p) q

  Dec {zero} w P = P tt*
  Dec {suc n} (lf f p) P = Unit*
  Dec {suc n} (nd f w α β γ δ x) P =
    P (inl tt) × Dec w (λ p → Dec (δ ⊚ p) (λ q → P (inr (p , q))))

  _⊚_ {zero} {w = w} δ p = δ
  _⊚_ {suc n} {w = nd f w α β γ δ x} ϵ (inl tt) = fst ϵ
  _⊚_ {suc n} {w = nd f w α β γ δ x} ϵ (inr (p , q)) = (snd ϵ ⊚ p) ⊚ q
  
  η {zero} X f = tt*
  η {suc n} (X , P) (f , w , y , x)  = {!!}

  -- η X {𝑜 ∣ 𝑝} (f , x , c , y) =

    -- let d p = η (fst X) (Shp (fst X) c p)
    --     z p q = y p 
    --     ψ p = lf (y p)
    -- in nd x c y d z ψ
