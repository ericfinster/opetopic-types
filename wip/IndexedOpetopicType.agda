--
--  OpetopicType.agda - Definition of Opetopic Types Indexed over Opetopes
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Prelude
open import Opetopes

module IndexedOpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Type (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ n} → 𝕆 ℓ n → 𝒪 n → Type ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
    → 𝒫 𝑜 → Type ℓ 
  Shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
    → (p : Pos 𝑝) → Frm X (Typ 𝑝 p) 

  η : ∀ {n ℓ} (X : 𝕆 ℓ n)
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
    → Cns X f (ηₒ 𝑜)

  {-# TERMINATING #-} 
  μ : ∀ {n ℓ} (X : 𝕆 ℓ n)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
    → {ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (κ : (p : Pos 𝑝) → Cns X (Shp X c p) (ι p))
    → Cns X f (μₒ 𝑝 ι)

  postulate

    η-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → (p : Pos (ηₒ 𝑜))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
      → {ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (κ : (p : Pos 𝑝) → Cns X (Shp X c p) (ι p))
      → (p : Pos (μₒ 𝑝 ι))
      → Shp X (μ X c κ) p ↦ Shp X (κ (μₒ-pos-fst 𝑝 ι p)) (μₒ-pos-snd 𝑝 ι p)
    {-# REWRITE μ-pos-shp #-} 

    -- Monad Laws
    μ-unit-r : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → {f : Frm X 𝑜} (c : Cns X f 𝑝)
      → μ X c (λ p → η X (Shp X c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → (ι : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → (δ : (p : Pos (ηₒ 𝑜)) → Cns X f (ι p))
      → μ X (η X f) δ ↦ δ (ηₒ-pos 𝑜)
    {-# REWRITE μ-unit-l #-} 

    μ-assoc : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
      → {ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (κ : (p : Pos 𝑝) → Cns X (Shp X c p) (ι p))
      → (δ : (p : Pos (μₒ 𝑝 ι)) → 𝒫 (Typ (μₒ 𝑝 ι) p))
      → (ε : (p : Pos (μₒ 𝑝 ι)) → Cns X (Shp X (κ (μₒ-pos-fst 𝑝 ι p)) (μₒ-pos-snd 𝑝 ι p)) (δ p))
      → μ X (μ X c κ) ε
        ↦ μ X c (λ p → μ X (κ p) (λ q → ε (μₒ-pos 𝑝 ι p q)))
    {-# REWRITE μ-assoc #-} 

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ) where
  
    η-dec : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) (x : Xₛₙ f)
      → (p : Pos (ηₒ 𝑜)) → Xₛₙ (Shp Xₙ (η Xₙ f) p)
    η-dec {𝑜} f x = ηₒ-pos-elim 𝑜 (λ p → Xₛₙ (Shp Xₙ (η Xₙ f) p)) x 

    μ-dec : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
      → (ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (ι p))
      → (ν : (p : Pos 𝑝) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
      → (p : Pos (μₒ 𝑝 ι)) → Xₛₙ (Shp Xₙ (μ Xₙ c δ) p)
    μ-dec {𝑝 = 𝑝} c ι δ ν p = ν (μₒ-pos-fst 𝑝 ι p) (μₒ-pos-snd 𝑝 ι p)

    {-# NO_POSITIVITY_CHECK #-}
    record WebFrm (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) : Type ℓ where
      inductive
      eta-equality
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ 𝑜
        cns : Cns Xₙ frm 𝑝
        tgt : Xₛₙ frm
        src : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ cns p)

    open WebFrm public

    -- Attempt at a recursive version ...
    WebRec : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑜 𝑝 → 𝒯r 𝑜 𝑝 → Type ℓ
    WebRec ⟪ f , c , x , ν ⟫ (lfₒ 𝑜) = (c , ν) == (η _ f , const x)
    WebRec ⟪ f , c , x , ν ⟫ (ndₒ 𝑜 𝑝 δ ε) = {!!}

    data Web : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑜 𝑝 → 𝒯r 𝑜 𝑝 → Type ℓ where

      lf : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
        → Web ⟪ f , η Xₙ f , x , const x ⟫ (lfₒ 𝑜) 

      nd : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (φ : WebFrm 𝑜 𝑝)
        → (ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
        → (κ : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p) (ι p))
        → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ (cns φ) p) (ι p))
        → (ν : (p : Pos 𝑝) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
        → (ε : (p : Pos 𝑝) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (κ p)) 
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) ι δ ν ⟫ (ndₒ 𝑜 𝑝 ι κ) 

    WebPos : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑜 𝑝} {𝑡 : 𝒯r 𝑜 𝑝} (ω : Web φ 𝑡) → Type ℓ
    WebPos (lf _) = Lift ⊥
    WebPos (nd {𝑝 = 𝑝} φ ι κ δ ν ε) = Unit ⊎ Σ (Pos 𝑝) (λ p → WebPos (ε p))

    WebShp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑜 𝑝} {𝑡 : 𝒯r 𝑜 𝑝}
      → (ω : Web φ 𝑡) (p : 𝒯rPos 𝑡)
      → WebFrm (fst (𝒯rTyp 𝑡 p)) (snd (𝒯rTyp 𝑡 p))
    WebShp (nd φ ι κ δ ν ε) (inl tt) = φ
    WebShp (nd φ ι κ δ ν ε) (inr (p , q)) = WebShp (ε p) q

    graft : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑜 𝑝} {𝑡 : 𝒯r 𝑜 𝑝} (ω : Web φ 𝑡)
      → (ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (κ : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p) (ι p))
      → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ (cns φ) p) (ι p))
      → (ν : (p : Pos 𝑝) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
      → (ε : (p : Pos 𝑝) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (κ p)) 
      → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) ι δ ν ⟫ (γₒ 𝑡 ι κ)
    graft (lf {𝑜} {f} x) ι₁ κ₁ δ₁ ν₁ ε₁ = ε₁ (ηₒ-pos 𝑜)
    graft (nd {𝑝 = 𝑝} φ ι κ δ ν ε) ι₁ κ₁ δ₁ ν₁ ε₁ =
      let ι' p = μₒ (ι p) (ι-ih p)
          δ' p = μ Xₙ (δ p) (δ-ih p)
          κ' p = γₒ (κ p) (ι-ih p) (κ-ih p)
          ν' p q = ν₁ (μₒ-pos 𝑝 ι p (μₒ-pos-fst (ι p) (ι-ih p) q)) (μₒ-pos-snd (ι p) (ι-ih p) q)
          ε' p = graft (ε p) (ι-ih p) (κ-ih p) (δ-ih p) (ν-ih p) (ε-ih p)
      in nd φ ι' κ' δ' ν' ε'  

        where ι-ih : (p : Pos 𝑝) (q : Pos (ι p)) → 𝒫 (Typ (ι p) q)
              ι-ih p q = ι₁ (μₒ-pos 𝑝 ι p q)

              κ-ih : (p : Pos 𝑝) (q : Pos (ι p)) → 𝒯r (Typ (ι p) q) (ι-ih p q)
              κ-ih p q = κ₁ (μₒ-pos 𝑝 ι p q)

              δ-ih : (p : Pos 𝑝) (q : Pos (ι p)) → Cns Xₙ (Shp Xₙ (δ p) q) (ι-ih p q)
              δ-ih p q = δ₁ (μₒ-pos 𝑝 ι p q)
  
              ν-ih : (p : Pos 𝑝) (q : Pos (ι p)) (r : Pos (ι-ih p q))  → Xₛₙ (Shp Xₙ (δ-ih p q) r)
              ν-ih p q = ν₁ (μₒ-pos 𝑝 ι p q)

              ε-ih : (p : Pos 𝑝) (q : Pos (ι p)) → Web ⟪ Shp Xₙ (δ p) q , δ-ih p q , ν p q , ν-ih p q ⟫ (κ-ih p q)
              ε-ih p q = ε₁ (μₒ-pos 𝑝 ι p q) 

      -- TODO: Grafting Axioms

  𝕆 ℓ zero = Lift Unit 
  𝕆 ℓ (suc n) = Σ (𝕆 ℓ n) (λ Xₙ → {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
  
  Frm {n = zero} X tt = Lift Unit
  Frm {n = suc n} (Xₙ , Xₛₙ) (𝑜 , 𝑝) = WebFrm Xₙ Xₛₙ 𝑜 𝑝 

  Cns {n = zero} _ _ _ = Lift Unit 
  Cns {n = suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} = Web Xₙ Xₛₙ {𝑜} {𝑝} 
  
  Shp {n = zero} _ _ _ = lift tt
  Shp {n = suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} ω p = WebShp Xₙ Xₛₙ ω p

  -- η : ∀ {n ℓ} (X : 𝕆 ℓ n)
  --   → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
  --   → Cns X f (ηₒ 𝑜)
  η {n = zero} _ _ = lift tt
  η {n = suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} φ =
    let ι p = ηₒ (Typ 𝑝 p)
        κ p = lfₒ (Typ 𝑝 p)
        δ p = η Xₙ (Shp Xₙ (cns φ) p)
        ν p q = src φ p
        ε p = lf (src φ p)
    in nd φ ι κ δ ν ε
    
  -- μ : ∀ {n ℓ} (X : 𝕆 ℓ n)
  --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  --   → {ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → (κ : (p : Pos 𝑝) → Cns X (Shp X c p) (ι p))
  --   → Cns X f (μₒ 𝑝 ι)
  μ {n = zero} _ _ _ = lift tt
  μ {n = suc n} (Xₙ , Xₛₙ) (lf x) θ = lf x
  μ {n = suc n} (Xₙ , Xₛₙ) (nd φ ι κ δ ν ε) {ζ} θ =
    let ω = θ (inl tt)
        κ' p = μₒ (κ p) (λ q → ζ (inr (p , q)))
        ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → θ (inr (p , q)))
    in graft Xₙ Xₛₙ ω ι κ' δ ν ε'

  --
  -- The terminal opetopic type
  --
  
  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆 ℓ n
  𝕋 zero = lift tt
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 
