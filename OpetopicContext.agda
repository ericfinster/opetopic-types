--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat 
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum 

open import Prelude

module OpetopicContext where


  --
  --  Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Type (ℓ-suc ℓ)

  --
  --  Polynomial Signature
  --

  Frm : ∀ {ℓ n} → 𝕆 ℓ n → Type ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → Frm X → Type ℓ
  Pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f) → Type ℓ
  Typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (p : Pos X c) → Frm X

  --
  --  Monadic Signature
  --

  η : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → (f : Frm X)
    → Cns X f 

  η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → (f : Frm X)
    → Pos X (η X f) 

  η-pos-elim : ∀ {ℓ ℓ' n} (X : 𝕆 ℓ n) (f : Frm X)
    → (P : (p : Pos X (η X f)) → Type ℓ')
    → (η-pos* : P (η-pos X f))
    → (p : Pos X (η X f)) → P p

  {-# TERMINATING #-}
  μ : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (δ : (p : Pos X c) → Cns X (Typ X c p))
    → Cns X f

  μ-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (δ : (p : Pos X c) → Cns X (Typ X c p))
    → (p : Pos X c) (q : Pos X (δ p))
    → Pos X (μ X c δ) 

  μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (δ : (p : Pos X c) → Cns X (Typ X c p))
    → (p : Pos X (μ X c δ))
    → Pos X c

  μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (δ : (p : Pos X c) → Cns X (Typ X c p))
    → (p : Pos X (μ X c δ))
    → Pos X (δ (μ-fst X c δ p))
  
  postulate

    --
    --  Position Typing
    --

    η-pos-typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (p : Pos X (η X f))
      → Typ X (η X f) p ↦ f
    {-# REWRITE η-pos-typ #-}

    μ-pos-typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → Typ X (μ X c δ) p ↦ Typ X (δ (μ-fst X c δ p)) (μ-snd X c δ p)
    {-# REWRITE μ-pos-typ #-}

    --
    --  Position Computation Rules
    --
    
    η-pos-elim-β : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : (p : Pos X (η X f)) → Type ℓ)
      → (η-pos* : P (η-pos X f))
      → η-pos-elim X f P η-pos* (η-pos X f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-fst-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → μ-fst X c δ (μ-pos X c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → μ-snd X c δ (μ-pos X c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → μ-pos X c δ (μ-fst X c δ p) (μ-snd X c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Monad Laws
    --

    μ-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → μ X c (λ p → η X (Typ X c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X (Typ X (η X f) p))
      → μ X (η X f) δ ↦ δ (η-pos X f)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → μ X (μ X c δ) ε ↦ 
        μ X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
    {-# REWRITE μ-assoc #-}

    --
    --  Compatibilities of Intro/Elim with Reductions
    --

    -- Introduction
    μ-pos-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f) (p : Pos X c)
      → μ-pos X c (λ p → η X (Typ X c p)) p (η-pos X (Typ X c p)) ↦ p
    {-# REWRITE μ-pos-unit-r #-}    

    μ-pos-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X f)
      → (p : Pos X (δ (η-pos X f)))
      → μ-pos X (η X f) δ (η-pos X f) p ↦ p
    {-# REWRITE μ-pos-unit-l #-}

    μ-pos-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → (pq : Pos X (μ X c δ)) (r : Pos X (ε pq))
      → let p = μ-fst X c δ pq
            q = μ-snd X c δ pq 
        in μ-pos X (μ X c δ) ε pq r
          ↦ μ-pos X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
              p (μ-pos X (δ p) (λ q → ε (μ-pos X c δ p q)) q r)
    {-# REWRITE μ-pos-assoc #-}
    
    -- First Projection
    μ-fst-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (p : Pos X (μ X c (λ p → η X (Typ X c p))))
      → μ-fst X c (λ p → η X (Typ X c p)) p ↦ p
    {-# REWRITE μ-fst-unit-r #-}

    μ-fst-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X f)
      → (p : Pos X (μ X (η X f) δ))
      → μ-fst X (η X f) δ p ↦ η-pos X f
    {-# REWRITE μ-fst-unit-l #-}

    μ-fst-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → (pqr : Pos X (μ X (μ X c δ) ε))
      → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            q = μ-fst X (δ p) (λ q → ε (μ-pos X c δ p q)) qr
        in μ-fst X (μ X c δ) ε pqr ↦ μ-pos X c δ p q  
    {-# REWRITE μ-fst-assoc #-}

    -- Second Projection
    μ-snd-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (p : Pos X (μ X c (λ p → η X (Typ X c p))))
      → μ-snd X c (λ p → η X (Typ X c p)) p ↦ η-pos X (Typ X c p)
    {-# REWRITE μ-snd-unit-r #-}

    μ-snd-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X (Typ X (η X f) p))
      → (p : Pos X (μ X (η X f) δ))
      → μ-snd X (η X f) δ p ↦ p
    {-# REWRITE μ-snd-unit-l #-}

    μ-snd-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → (pqr : Pos X (μ X (μ X c δ) ε))
      → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
            qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
        in μ-snd X (μ X c δ) ε pqr
          ↦ μ-snd X (δ p) (λ q → ε (μ-pos X c δ p q)) qr 
    {-# REWRITE μ-snd-assoc #-} 

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Type ℓ) where
  
    η-dec : (f : Frm Xₙ) (x : Xₛₙ f)
      → (p : Pos Xₙ (η Xₙ f)) → Xₛₙ (Typ Xₙ (η Xₙ f) p)
    η-dec f = η-pos-elim Xₙ f (λ p → Xₛₙ (Typ Xₙ (η Xₙ f) p)) 

    μ-dec : {f : Frm Xₙ} (c : Cns Xₙ f)
      → (δ : (p : Pos Xₙ c) → Cns Xₙ (Typ Xₙ c p))
      → (θ : (p : Pos Xₙ c) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (p : Pos Xₙ (μ Xₙ c δ)) → Xₛₙ (Typ Xₙ (μ Xₙ c δ) p)
    μ-dec c δ θ p = θ (μ-fst Xₙ c δ p) (μ-snd Xₙ c δ p)

    {-# NO_POSITIVITY_CHECK #-}
    record WebFrm : Type ℓ where
      inductive
      eta-equality
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ
        cns : Cns Xₙ frm
        tgt : Xₛₙ frm
        src : (p : Pos Xₙ cns) → Xₛₙ (Typ Xₙ cns p)

    open WebFrm public
    
    data Web : WebFrm → Type ℓ where

      lf : {f : Frm Xₙ} (x : Xₛₙ f)
        → Web ⟪ f , η Xₙ f , x , η-dec f x ⟫ 

      nd : (φ : WebFrm)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε : (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ ν ⟫ 

    WebPos : {φ : WebFrm} (ω : Web φ) → Type ℓ 
    WebPos (lf x) = Lift ⊥ 
    WebPos (nd φ δ ν ε) = Unit ⊎ Σ (Pos Xₙ (cns φ)) (λ p → WebPos (ε p))

    WebTyp : {φ : WebFrm} (ω : Web φ) (p : WebPos ω) → WebFrm
    WebTyp (nd φ δ ν ε) (inl tt) = φ
    WebTyp (nd φ δ ν ε) (inr (p , q)) = WebTyp (ε p) q

    --
    --  Grafting
    --

    graft : {φ : WebFrm} (ω : Web φ)
      → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
      → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
      → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ ν ⟫
    graft (lf {f} x) δ₁ ν₁ ε₁ = ε₁ (η-pos Xₙ f)
    graft (nd φ δ ν ε) δ₁ ν₁ ε₁ = 
      let δ' p = μ Xₙ (δ p) (δ₁-ih p)
          ν' p q = ν₁ (μ-pos Xₙ (cns φ) δ p (μ-fst Xₙ (δ p) (δ₁-ih p) q)) (μ-snd Xₙ (δ p) (δ₁-ih p) q)
          ε' p = graft (ε p) (δ₁-ih p) (ν₁-ih p) (ε₁-ih p)
      in nd φ δ' ν' ε' 

      where δ₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Cns Xₙ (Typ Xₙ (δ p) q)
            δ₁-ih p q = δ₁ (μ-pos Xₙ (cns φ) δ p q)

            ν₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) (r : Pos Xₙ (δ₁-ih p q)) → Xₛₙ (Typ Xₙ (δ₁-ih p q) r)
            ν₁-ih p q = ν₁ (μ-pos Xₙ (cns φ) δ p q)

            ε₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Web ⟪ Typ Xₙ (δ p) q , δ₁-ih p q , ν p q , ν₁-ih p q ⟫
            ε₁-ih p q = ε₁ (μ-pos Xₙ (cns φ) δ p q)

    graft-pos-inl : {φ : WebFrm} (ω : Web φ)
      → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
      → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
      → WebPos ω → WebPos (graft ω δ ν ε) 
    graft-pos-inl (nd φ δ ν ε) δ₁ ν₁ ε₁ (inl tt) = inl tt
    graft-pos-inl (nd φ δ ν ε) δ₁ ν₁ ε₁ (inr (p , q)) =
      inr (p , (graft-pos-inl (ε p) (δ₁-ih p) (ν₁-ih p) (ε₁-ih p) q))
      
      where δ₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Cns Xₙ (Typ Xₙ (δ p) q)
            δ₁-ih p q = δ₁ (μ-pos Xₙ (cns φ) δ p q)

            ν₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) (r : Pos Xₙ (δ₁-ih p q)) → Xₛₙ (Typ Xₙ (δ₁-ih p q) r)
            ν₁-ih p q = ν₁ (μ-pos Xₙ (cns φ) δ p q)

            ε₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Web ⟪ Typ Xₙ (δ p) q , δ₁-ih p q , ν p q , ν₁-ih p q ⟫
            ε₁-ih p q = ε₁ (μ-pos Xₙ (cns φ) δ p q)

    graft-pos-inr : {φ : WebFrm} (ω : Web φ)
      → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
      → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
      → (p : Pos Xₙ (cns φ)) (q : WebPos (ε p))
      → WebPos (graft ω δ ν ε)
    graft-pos-inr (lf {f} x) δ₁ ν₁ ε₁ =
      η-pos-elim Xₙ f (λ p → WebPos (ε₁ p) → WebPos (ε₁ (η-pos Xₙ f))) (λ p → p)
    graft-pos-inr (nd φ δ ν ε) δ₁ ν₁ ε₁ pq r =
      let p = μ-fst Xₙ (cns φ) δ pq
          q = μ-snd Xₙ (cns φ) δ pq 
      in inr (p , (graft-pos-inr (ε p) (δ₁-ih p) (ν₁-ih p) (ε₁-ih p) q r))

      where δ₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Cns Xₙ (Typ Xₙ (δ p) q)
            δ₁-ih p q = δ₁ (μ-pos Xₙ (cns φ) δ p q)

            ν₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) (r : Pos Xₙ (δ₁-ih p q)) → Xₛₙ (Typ Xₙ (δ₁-ih p q) r)
            ν₁-ih p q = ν₁ (μ-pos Xₙ (cns φ) δ p q)

            ε₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Web ⟪ Typ Xₙ (δ p) q , δ₁-ih p q , ν p q , ν₁-ih p q ⟫
            ε₁-ih p q = ε₁ (μ-pos Xₙ (cns φ) δ p q)

    graft-pos-elim : ∀ {ℓ'} {φ : WebFrm} (ω : Web φ)
      → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
      → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
      → (P : WebPos (graft ω δ ν ε) → Type ℓ')
      → (inl* : (p : WebPos ω) → P (graft-pos-inl ω δ ν ε p))
      → (inr* : (p : Pos Xₙ (cns φ)) (q : WebPos (ε p)) → P (graft-pos-inr ω δ ν ε p q))
      → (p : WebPos (graft ω δ ν ε)) → P p 
    graft-pos-elim (lf {f} x) δ₁ ν₁ ε₁ P inl* inr* p = inr* (η-pos Xₙ f) p
    graft-pos-elim (nd φ δ ν ε) δ₁ ν₁ ε₁ P inl* inr* (inl tt) = inl* (inl tt)
    graft-pos-elim (nd φ δ ν ε) δ₁ ν₁ ε₁ P inl* inr* (inr (p , q)) = 
      graft-pos-elim (ε p) (δ₁-ih p) (ν₁-ih p) (ε₁-ih p)
        (λ q → P (inr (p , q))) (λ q → inl* (inr (p , q)))
        (λ p' q → inr* (μ-pos Xₙ (cns φ) δ p p') q) q

      where δ₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Cns Xₙ (Typ Xₙ (δ p) q)
            δ₁-ih p q = δ₁ (μ-pos Xₙ (cns φ) δ p q)

            ν₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) (r : Pos Xₙ (δ₁-ih p q)) → Xₛₙ (Typ Xₙ (δ₁-ih p q) r)
            ν₁-ih p q = ν₁ (μ-pos Xₙ (cns φ) δ p q)

            ε₁-ih : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Web ⟪ Typ Xₙ (δ p) q , δ₁-ih p q , ν p q , ν₁-ih p q ⟫
            ε₁-ih p q = ε₁ (μ-pos Xₙ (cns φ) δ p q)

    postulate

      graft-pos-elim-inl-β : ∀ {ℓ'} {φ : WebFrm} (ω : Web φ)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → (P : WebPos (graft ω δ ν ε) → Type ℓ')
        → (inl* : (p : WebPos ω) → P (graft-pos-inl ω δ ν ε p))
        → (inr* : (p : Pos Xₙ (cns φ)) (q : WebPos (ε p)) → P (graft-pos-inr ω δ ν ε p q))
        → (p : WebPos ω)
        → graft-pos-elim ω δ ν ε P inl* inr* (graft-pos-inl ω δ ν ε p) ↦ inl* p
      {-# REWRITE graft-pos-elim-inl-β #-}

      graft-pos-elim-inr-β : ∀ {ℓ'} {φ : WebFrm} (ω : Web φ)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → (P : WebPos (graft ω δ ν ε) → Type ℓ')
        → (inl* : (p : WebPos ω) → P (graft-pos-inl ω δ ν ε p))
        → (inr* : (p : Pos Xₙ (cns φ)) (q : WebPos (ε p)) → P (graft-pos-inr ω δ ν ε p q))
        → (p : Pos Xₙ (cns φ)) (q : WebPos (ε p))
        → graft-pos-elim ω δ ν ε P inl* inr* (graft-pos-inr ω δ ν ε p q) ↦ inr* p q
      {-# REWRITE graft-pos-elim-inr-β #-}

  --
  --  Implementations 
  --

  𝕆 ℓ zero = Lift Unit
  𝕆 ℓ (suc n) = Σ (𝕆 ℓ n) (λ Xₙ → (f : Frm Xₙ) → Type ℓ)
  
  Frm {ℓ} {zero} _ = Lift Unit
  Frm {ℓ} {suc n} (Xₙ , Xₛₙ) = WebFrm Xₙ Xₛₙ
  
  Cns {ℓ} {zero} _ _ = Lift Unit
  Cns {ℓ} {suc n} (Xₙ , Xₛₙ) = Web Xₙ Xₛₙ
  
  Pos {ℓ} {zero} _ _ = Lift Unit
  Pos {ℓ} {suc n} (Xₙ , Xₛₙ) = WebPos Xₙ Xₛₙ

  Typ {ℓ} {zero} _ _ _ = lift tt
  Typ {ℓ} {suc n} (Xₙ , Xₛₙ) = WebTyp Xₙ Xₛₙ

  -- η : ∀ {ℓ n} (X : 𝕆 ℓ n)
  --   → (f : Frm X)
  --   → Cns X f 
  η {n = zero} _ _ = lift tt
  η {n = suc n} (Xₙ , Xₛₙ) φ =
    let δ p = η Xₙ (Typ Xₙ (cns φ) p)
        ν p = η-dec Xₙ Xₛₙ (Typ Xₙ (cns φ) p) (src φ p) 
        ε p = lf (src φ p)
    in nd φ δ ν ε 

  -- η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
  --   → (f : Frm X)
  --   → Pos X (η X f) 
  η-pos {n = zero} _ _ = lift tt
  η-pos {n = suc n} (Xₙ , Xₛₙ) φ = inl tt
  
  -- η-pos-elim : ∀ {ℓ ℓ' n} (X : 𝕆 ℓ n) (f : Frm X)
  --   → (P : (p : Pos X (η X f)) → Type ℓ')
  --   → (η-pos* : P (η-pos X f))
  --   → (p : Pos X (η X f)) → P p 
  η-pos-elim {n = zero} X f P η-pos* p = η-pos*
  η-pos-elim {n = suc n} X f P η-pos* (inl tt) = η-pos*

  -- μ : ∀ {ℓ n} (X : 𝕆 ℓ n)
  --   → {f : Frm X} (c : Cns X f)
  --   → (δ : (p : Pos X c) → Cns X (Typ X c p))
  --   → Cns X f
  μ {n = zero} _ _ _ = lift tt
  μ {n = suc n} (Xₙ , Xₛₙ) (lf x) _ = lf x
  μ {n = suc n} (Xₙ , Xₛₙ) (nd φ δ ν ε) κ =
    let ω = κ (inl tt)
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q)))
    in graft Xₙ Xₛₙ ω δ ν ε'

  -- μ-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
  --   → {f : Frm X} (c : Cns X f)
  --   → (δ : (p : Pos X c) → Cns X (Typ X c p))
  --   → (p : Pos X c) (q : Pos X (δ p))
  --   → Pos X (μ X c δ) 
  μ-pos {n = zero} _ _ _ _ _ = lift tt
  μ-pos {n = suc n} (Xₙ , Xₛₙ) (nd φ δ ν ε) κ (inl tt) r = 
    let ω = κ (inl tt)
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q)))
    in graft-pos-inl Xₙ Xₛₙ ω δ ν ε' r 
  μ-pos {n = suc n} (Xₙ , Xₛₙ) (nd φ δ ν ε) κ (inr (p , q)) r = 
    let ω = κ (inl tt)
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q)))
    in graft-pos-inr Xₙ Xₛₙ ω δ ν ε' p
        (μ-pos (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q))) q r)

  -- μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
  --   → {f : Frm X} (c : Cns X f)
  --   → (δ : (p : Pos X c) → Cns X (Typ X c p))
  --   → (p : Pos X (μ X c δ))
  --   → Pos X c
  μ-fst {n = zero} _ _ _ _ = lift tt
  μ-fst {n = suc n} (Xₙ , Xₛₙ) (nd φ δ ν ε) κ = 
    let ω = κ (inl tt)
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q)))
    in graft-pos-elim Xₙ Xₛₙ ω δ ν ε' _
        (λ _ → inl tt)
        (λ p q → inr (p , μ-fst (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q))) q))

  -- μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
  --   → {f : Frm X} (c : Cns X f)
  --   → (δ : (p : Pos X c) → Cns X (Typ X c p))
  --   → (p : Pos X (μ X c δ))
  --   → Pos X (δ (μ-fst X c δ p))
  μ-snd {n = zero} _ _ _ _ = lift tt
  μ-snd {n = suc n} (Xₙ , Xₛₙ) (nd φ δ ν ε) κ = 
    let ω = κ (inl tt)
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q))) 
    in graft-pos-elim Xₙ Xₛₙ ω δ ν ε' _ (λ p → p)
         (λ p q → μ-snd (Xₙ , Xₛₙ) (ε p) (λ q → κ (inr (p , q))) q)

--
--  A note on termination and non-positivity:
--
--    In fact, both can be avoided.
--
--  The non-positivity arises because of the use of the WebFrm record,
--  which may simply be defined as a Σ type in which case the problem
--  disappears.  However, this significantly complicates some of the
--  type signatures, and the development is much more pleasant with
--  the named projections.
--
--  As to the termination, this can also be avoided by defining the
--  rest of the monad signature for the slice locally, and not
--  matching during the definition of η, μ, etc.  The problem with
--  this is that you then need to repeat the rewrites for all the
--  monad laws in this context so that these functions *also* compute,
--  and this leads to an annoying amount of duplication.  Since the
--  definitions of the relevant functions are the same in either case,
--  this already proves that they terminate.  But setting things up
--  the way I have saves a lot of typing.
--
