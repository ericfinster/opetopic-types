{-# OPTIONS --without-K --rewriting --no-positivity #-}

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

open import MiniHoTT

module NewOpetopicType where

  --
  --  Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)

  --
  --  Polynomial Signature
  --

  Frm : ∀ {ℓ n} → 𝕆 ℓ n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → Frm X → Set ℓ
  Pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f) → Set ℓ
  Typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (p : Pos X c) → Frm X

  --
  --  Monadic Signature
  --
  
  postulate

    η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Cns X f 

    η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Pos X (η X f) 

    η-pos-elim : ∀ {ℓ ℓ' n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : (p : Pos X (η X f)) → Set ℓ')
      → (η-pos* : P (η-pos X f))
      → (p : Pos X (η X f)) → P p 

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
      → (P : (p : Pos X (η X f)) → Set ℓ)
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

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : (f : Frm Xₙ) → Set ℓ) where
  
    η-dec : (f : Frm Xₙ) (x : Xₛₙ f)
      → (p : Pos Xₙ (η Xₙ f)) → Xₛₙ (Typ Xₙ (η Xₙ f) p)
    η-dec f = η-pos-elim Xₙ f (λ p → Xₛₙ (Typ Xₙ (η Xₙ f) p)) 

    μ-dec : {f : Frm Xₙ} (c : Cns Xₙ f)
      → (δ : (p : Pos Xₙ c) → Cns Xₙ (Typ Xₙ c p))
      → (θ : (p : Pos Xₙ c) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
      → (p : Pos Xₙ (μ Xₙ c δ)) → Xₛₙ (Typ Xₙ (μ Xₙ c δ) p)
    μ-dec c δ θ p = θ (μ-fst Xₙ c δ p) (μ-snd Xₙ c δ p)

    record WebFrm : Set ℓ where
      inductive 
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ
        cns : Cns Xₙ frm
        tgt : Xₛₙ frm
        src : (p : Pos Xₙ cns) → Xₛₙ (Typ Xₙ cns p)

    open WebFrm
    
    data Web : WebFrm → Set ℓ where

      lf : {f : Frm Xₙ} (x : Xₛₙ f)
        → Web ⟪ f , η Xₙ f , x , η-dec f x ⟫ 

      nd : (φ : WebFrm)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε : (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ ν ⟫ 

    WebPos : {φ : WebFrm} (ω : Web φ) → Set ℓ 
    WebPos (lf x) = ∅
    WebPos (nd φ δ ν ε) = ⊤ {ℓ} ⊔ Σ (Pos Xₙ (cns φ)) (λ p → WebPos (ε p))

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
    graft (nd φ δ₀ ν₀ ε₀) δ₁ ν₁ ε₁ = 
      let δ₁-ih p q = δ₁ (μ-pos Xₙ (cns φ) δ₀ p q)
          ν₁-ih p q = ν₁ (μ-pos Xₙ (cns φ) δ₀ p q)
          ε₁-ih p q = ε₁ (μ-pos Xₙ (cns φ) δ₀ p q)
          δ' p = μ Xₙ (δ₀ p) (δ₁-ih p)
          ν' p q = ν₁ (μ-pos Xₙ (cns φ) δ₀ p (μ-fst Xₙ (δ₀ p) (δ₁-ih p) q)) (μ-snd Xₙ (δ₀ p) (δ₁-ih p) q)
          ε' p = graft (ε₀ p) (δ₁-ih p) (ν₁-ih p) (ε₁-ih p)
      in nd φ δ' ν' ε' 

    postulate
    
      graft-pos-inl : {φ : WebFrm} (ω : Web φ)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → WebPos ω → WebPos (graft ω δ ν ε) 

      graft-pos-inr : {φ : WebFrm} (ω : Web φ)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → (p : Pos Xₙ (cns φ)) (q : WebPos (ε p))
        → WebPos (graft ω δ ν ε)

      graft-pos-elim : ∀ {ℓ'} {φ : WebFrm} (ω : Web φ)
        → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
        → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
        → (ε :  (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
        → (P : WebPos (graft ω δ ν ε) → Set ℓ')
        → (inl* : (p : WebPos ω) → P (graft-pos-inl ω δ ν ε p))
        → (inr* : (p : Pos Xₙ (cns φ)) (q : WebPos (ε p)) → P (graft-pos-inr ω δ ν ε p q))
        → (p : WebPos (graft ω δ ν ε)) → P p 

  𝕆 ℓ O = ⊤
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ Xₙ → (f : Frm Xₙ) → Set ℓ)
  
  Frm {ℓ} {O} _ = ⊤
  Frm {ℓ} {S n} (Xₙ , Xₛₙ) = WebFrm Xₙ Xₛₙ
  
  Cns {ℓ} {O} _ _ = ⊤
  Cns {ℓ} {S n} (Xₙ , Xₛₙ) = Web Xₙ Xₛₙ
  
  Pos {ℓ} {O} _ _ = ⊤
  Pos {ℓ} {S n} (Xₙ , Xₛₙ) = WebPos Xₙ Xₛₙ

  Typ {ℓ} {O} _ _ _ = tt
  Typ {ℓ} {S n} (Xₙ , Xₛₙ) = WebTyp Xₙ Xₛₙ


