{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ n} → 𝕆 ℓ n → 𝒪 n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} (f : Frm X o)
    → 𝒫 o → Set ℓ 
  Shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} {f : Frm X o}
    → {ρ : 𝒫 o} (c : Cns X f ρ)
    → (p : Pos ρ) → Frm X (Typ ρ p) 

  η : ∀ {n ℓ} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} (f : Frm X o)
    → Cns X f (ηₒ o)

  {-# TERMINATING #-} 
  μ : ∀ {n ℓ} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} {f : Frm X o}
    → {ρ : 𝒫 o} (c : Cns X f ρ)
    → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
    → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
    → Cns X f (μₒ ρ ι)

  postulate

    η-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o)
      → (p : Pos (ηₒ o))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → (p : Pos (μₒ ρ ι))
      → Shp X (μ X c κ) p ↦ Shp X (κ (μₒ-pos-fst ρ ι p)) (μₒ-pos-snd ρ ι p)
    {-# REWRITE μ-pos-shp #-} 

    -- Monad Laws
    μ-unit-r : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (ρ : 𝒫 o)
      → {f : Frm X o} (c : Cns X f ρ)
      → μ X c (λ p → η X (Shp X c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o)
      → (ι : (p : Pos (ηₒ o)) → 𝒫 (Typ (ηₒ o) p))
      → (δ : (p : Pos (ηₒ o)) → Cns X f (ι p))
      → μ X (η X f) δ ↦ δ (ηₒ-pos o)
    {-# REWRITE μ-unit-l #-} 

    μ-assoc : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → (δ : (p : Pos (μₒ ρ ι)) → 𝒫 (Typ (μₒ ρ ι) p))
      → (ε : (p : Pos (μₒ ρ ι)) → Cns X (Shp X (κ (μₒ-pos-fst ρ ι p)) (μₒ-pos-snd ρ ι p)) (δ p))
      → μ X (μ X c κ) ε
        ↦ μ X c (λ p → μ X (κ p) (λ q → ε (μₒ-pos ρ ι p q)))
    {-# REWRITE μ-assoc #-} 

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : {o : 𝒪 n} (f : Frm Xₙ o) → Set ℓ) where
  
    η-dec : {o : 𝒪 n} (f : Frm Xₙ o) (x : Xₛₙ f)
      → (p : Pos (ηₒ o)) → Xₛₙ (Shp Xₙ (η Xₙ f) p)
    η-dec {o} f x = ηₒ-pos-elim o (λ p → Xₛₙ (Shp Xₙ (η Xₙ f) p)) x 

    μ-dec : {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm Xₙ o} (c : Cns Xₙ f ρ)
      → (ι : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (δ : (p : Pos ρ) → Cns Xₙ (Shp Xₙ c p) (ι p))
      → (ν : (p : Pos ρ) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
      → (p : Pos (μₒ ρ ι)) → Xₛₙ (Shp Xₙ (μ Xₙ c δ) p)
    μ-dec {ρ = ρ} c ι δ ν p = ν (μₒ-pos-fst ρ ι p) (μₒ-pos-snd ρ ι p)

    {-# NO_POSITIVITY_CHECK #-}
    record WebFrm (o : 𝒪 n) (ρ : 𝒫 o) : Set ℓ where
      inductive
      eta-equality
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ o
        cns : Cns Xₙ frm ρ
        tgt : Xₛₙ frm
        src : (p : Pos ρ) → Xₛₙ (Shp Xₙ cns p)

    open WebFrm public
    
    data Web : {o : 𝒪 n} {ρ : 𝒫 o} → WebFrm o ρ → 𝒯r o ρ → Set ℓ where

      lf : {o : 𝒪 n} {f : Frm Xₙ o} (x : Xₛₙ f)
        → Web ⟪ f , η Xₙ f , x , cst x ⟫ (lfₒ o) 

      nd : {o : 𝒪 n} {ρ : 𝒫 o} (φ : WebFrm o ρ)
        → (ι : (p : Pos ρ) → 𝒫 (Typ ρ p))
        → (κ : (p : Pos ρ) → 𝒯r (Typ ρ p) (ι p))
        → (δ : (p : Pos ρ) → Cns Xₙ (Shp Xₙ (cns φ) p) (ι p))
        → (ν : (p : Pos ρ) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
        → (ε : (p : Pos ρ) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (κ p)) 
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) ι δ ν ⟫ (ndₒ o ρ ι κ) 

    WebPos : {o : 𝒪 n} {ρ : 𝒫 o} {φ : WebFrm o ρ} {τ : 𝒯r o ρ} (ω : Web φ τ) → Set ℓ
    WebPos (lf _) = ∅
    WebPos (nd {ρ = ρ} φ ι κ δ ν ε) = ⊤ {ℓ} ⊔ Σ (Pos ρ) (λ p → WebPos (ε p))

    WebShp : {o : 𝒪 n} {ρ : 𝒫 o} {φ : WebFrm o ρ} {τ : 𝒯r o ρ}
      → (ω : Web φ τ) (p : 𝒯rPos τ)
      → WebFrm (fst (𝒯rTyp τ p)) (snd (𝒯rTyp τ p))
    WebShp (nd φ ι κ δ ν ε) (inl tt) = φ
    WebShp (nd φ ι κ δ ν ε) (inr (p , q)) = WebShp (ε p) q

    graft : {o : 𝒪 n} {ρ : 𝒫 o} {φ : WebFrm o ρ} {τ : 𝒯r o ρ} (ω : Web φ τ)
      → (ι : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (κ : (p : Pos ρ) → 𝒯r (Typ ρ p) (ι p))
      → (δ : (p : Pos ρ) → Cns Xₙ (Shp Xₙ (cns φ) p) (ι p))
      → (ν : (p : Pos ρ) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
      → (ε : (p : Pos ρ) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (κ p)) 
      → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) ι δ ν ⟫ (γₒ τ ι κ)
    graft (lf {o} {f} x) ι₁ κ₁ δ₁ ν₁ ε₁ = ε₁ (ηₒ-pos o)
    graft (nd {ρ = ρ} φ ι κ δ ν ε) ι₁ κ₁ δ₁ ν₁ ε₁ =
      let ι-ih p q = ι₁ (μₒ-pos ρ ι p q)
          κ-ih p q = κ₁ (μₒ-pos ρ ι p q)
          δ-ih p q = δ₁ (μₒ-pos ρ ι p q)
          ν-ih p q = ν₁ (μₒ-pos ρ ι p q)
          ε-ih p q = ε₁ (μₒ-pos ρ ι p q)
          ι' p = μₒ (ι p) (ι-ih p)
          δ' p = μ Xₙ (δ p) (δ-ih p)
          κ' p = γₒ (κ p) (ι-ih p) (κ-ih p)
          ν' p q = ν₁ (μₒ-pos ρ ι p (μₒ-pos-fst (ι p) (ι-ih p) q)) (μₒ-pos-snd (ι p) (ι-ih p) q)
          ε' p = graft (ε p) (ι-ih p) (κ-ih p) (δ-ih p) (ν-ih p) (ε-ih p)
      in nd φ ι' κ' δ' ν' ε'  
  
      -- TODO: Grafting Axioms

  𝕆 ℓ O = ⊤ 
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ Xₙ → {o : 𝒪 n} → Frm Xₙ o → Set ℓ)
  
  Frm {n = O} X tt = ⊤
  Frm {n = S n} (Xₙ , Xₛₙ) (o , ρ) = WebFrm Xₙ Xₛₙ o ρ 

  Cns {n = O} _ _ _ = ⊤ 
  Cns {n = S n} (Xₙ , Xₛₙ) {o , ρ} = Web Xₙ Xₛₙ {o} {ρ} 
  
  Shp {n = O} _ _ _ = tt
  Shp {n = S n} (Xₙ , Xₛₙ) {o , ρ} ω p = WebShp Xₙ Xₛₙ ω p

  -- η : ∀ {n ℓ} (X : 𝕆 ℓ n)
  --   → {o : 𝒪 n} (f : Frm X o)
  --   → Cns X f (ηₒ o)
  η {n = O} _ _ = tt
  η {n = S n} (Xₙ , Xₛₙ) {o , ρ} φ =
    let ι p = ηₒ (Typ ρ p)
        κ p = lfₒ (Typ ρ p)
        δ p = η Xₙ (Shp Xₙ (cns φ) p)
        ν p q = src φ p
        ε p = lf (src φ p)
    in nd φ ι κ δ ν ε
    
  -- μ : ∀ {n ℓ} (X : 𝕆 ℓ n)
  --   → {o : 𝒪 n} {f : Frm X o}
  --   → {ρ : 𝒫 o} (c : Cns X f ρ)
  --   → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
  --   → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
  --   → Cns X f (μₒ ρ ι)
  μ {n = O} _ _ _ = tt
  μ {n = S n} (Xₙ , Xₛₙ) (lf x) θ = lf x
  μ {n = S n} (Xₙ , Xₛₙ) (nd φ ι κ δ ν ε) {ζ} θ =
    let ω = θ (inl tt)
        θ' p q = θ (inr (p , q))
        κ' p = μₒ (κ p) (λ q → ζ (inr (p , q)))
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → θ (inr (p , q)))
    in graft Xₙ Xₛₙ ω ι κ' δ ν ε'

  --
  -- The terminal opetopic type
  --
  
  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆 ℓ n
  𝕋 O = tt
  𝕋 (S n) = 𝕋 n , λ _ → ⊤ 
