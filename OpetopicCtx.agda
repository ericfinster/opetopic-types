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

module OpetopicCtx where

  𝕆Ctx : (ℓ : Level) → ℕ → Type (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ n} → 𝕆Ctx ℓ n → 𝒪 n → Type ℓ
  Cns : ∀ {ℓ n} (Γ : 𝕆Ctx ℓ n)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
    → 𝒫 𝑜 → Type ℓ 
  Shp : ∀ {ℓ n} (Γ : 𝕆Ctx ℓ n)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
    → (p : Pos 𝑝) → Frm Γ (Typ 𝑝 p) 

  -- I'm not sure this really helped.  The dependencies get
  -- complicated no matter what you do ....
  -- Dec : ∀ {n ℓ ℓ' ℓ''} {Γ : 𝕆Ctx ℓ n}
  --   → {P : 𝒪 n → Type ℓ''}
  --   → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → P 𝑜 → Type ℓ')
  --   → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
  --   → {𝑝 : 𝒫 𝑜} (𝑞 : Decₒ P 𝑝)
  --   → Cns Γ f 𝑝 → Type ℓ'
  -- Dec X {𝑝 = 𝑝} 𝑞 c = (p : Pos 𝑝) → X (Shp _ c p) (𝑞 p) 

  -- ⟦_⟧ : ∀ {n ℓ ℓ' ℓ''} {Γ : 𝕆Ctx ℓ n}
  --   → {P : 𝒪 n → Type ℓ''}
  --   → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → P 𝑜 → Type ℓ')
  --   → {𝑜 : 𝒪 n} → Frm Γ 𝑜 → ⟦ P ⟧ₒ 𝑜 → Type (ℓ-max ℓ ℓ')
  -- ⟦ X ⟧ {𝑜} f (𝑝 , 𝑞) = Σ (Cns _ f 𝑝) (Dec X 𝑞)

  -- Dec' : ∀ {n ℓ ℓ'} {Γ : 𝕆Ctx ℓ n}
  --   → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → Type ℓ')
  --   → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
  --   → {𝑝 : 𝒫 𝑜} → Cns Γ f 𝑝 → Type ℓ'
  -- Dec' X {𝑝 = 𝑝} c = (p : Pos 𝑝) → X (Shp _ c p)

  -- ⟦_⟧' : ∀ {n ℓ ℓ'} {Γ : 𝕆Ctx ℓ n}
  --   → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → Type ℓ')
  --   → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜) (𝑝 : 𝒫 𝑜)
  --   → Type (ℓ-max ℓ ℓ')
  -- ⟦ X ⟧' f 𝑝 = Σ (Cns _ f 𝑝) (λ c → Dec' X c)


  -- Monadic signature
  
  η : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
    → Cns Γ f (ηₒ 𝑜)

  μ : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
    → {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜}
    → {f : Frm Γ 𝑜} (c : Cns Γ f (fst 𝑝))
    → (d : (p : Pos (fst 𝑝)) → Cns Γ (Shp Γ c p) (snd 𝑝 p))
    → Cns Γ f (μₒ 𝑝)
    
  postulate

    η-pos-shp : ∀ {ℓ n} (X : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → (p : Pos (ηₒ 𝑜))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜}
      → {f : Frm Γ 𝑜} (c : Cns Γ f (fst 𝑝))
      → (d : (p : Pos (fst 𝑝)) → Cns Γ (Shp Γ c p) (snd 𝑝 p))
      → (p : Pos (μₒ 𝑝))
      → Shp Γ (μ Γ c) p ↦ Shp Γ (snd c (fstₒ 𝑝 p)) (sndₒ 𝑝 p)
    {-# REWRITE μ-pos-shp #-}

    -- Monad Laws
    μ-unit-r : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → {f : Frm Γ 𝑜} (c : Cns Γ f 𝑝)
      → μ Γ (c , λ p → η Γ (Shp Γ c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
      → (𝑞 : Decₒ 𝒫 (ηₒ 𝑜))
      → (d : Dec (Cns Γ) 𝑞 (η Γ f))
      → μ Γ (η Γ f , d) ↦ d (ηₒ-pos 𝑜)
    {-# REWRITE μ-unit-l #-} 

    μ-assoc : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} (𝑒 : Decₒ 𝒫 (μₒ 𝑝))
      → {f : Frm Γ 𝑜} (c : ⟦ Cns Γ ⟧ f 𝑝) (ε : Dec (Cns Γ) 𝑒 (μ Γ c))
      → μ Γ (μ Γ c , ε) ↦ μ Γ (fst c , λ p → μ Γ (snd c p , λ q → ε (pairₒ 𝑝 p q)))
    {-# REWRITE μ-assoc #-} 

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Γₙ : 𝕆Ctx ℓ n) (Γₛₙ : {𝑜 : 𝒪 n} (f : Frm Γₙ 𝑜) → Type ℓ) where
  
    WebFrm : {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) →  Type ℓ
    WebFrm {𝑜} 𝑝 =
      Σ[ f ∈ Frm Γₙ 𝑜 ]
      Σ[ x ∈ Γₛₙ f ]
      Σ[ c ∈ Cns Γₙ f 𝑝 ]
      ((p : Pos 𝑝) → Γₛₙ (Shp Γₙ c p))  

    data Web : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑝 → 𝒯r 𝑝 → Type ℓ where

      lf : {𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (x : Γₛₙ f)
        → Web (f , x , η Γₙ f , const x) lfₒ

      nd : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
        → {f : Frm Γₙ 𝑜} (x : Γₛₙ f)
        → (c : Cns Γₙ f 𝑝) (y : (p : Pos 𝑝) → Γₛₙ (Shp Γₙ c p))
        → {𝑠 : (p : Pos 𝑝) → 𝒯r (𝑞 p)}
        → (d : (p : Pos 𝑝) → Cns Γₙ (Shp Γₙ c p) (𝑞 p))
        → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Γₛₙ (Shp Γₙ (d p) q))
        → (ψ : (p : Pos 𝑝) → Web (Shp Γₙ c p , y p , d p , z p ) (𝑠 p)) 
        → Web (f , x , μ Γₙ (c , d) , λ p → z (fstₒ (𝑝 , 𝑞) p) (sndₒ (𝑝 , 𝑞) p)) (ndₒ (𝑝 , 𝑞) 𝑠) 

    -- WebShp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑝} {𝑡 : 𝒯r 𝑝}
    --   → (ω : Web φ 𝑡) (p : 𝒯rPos 𝑡)
    --   → WebFrm (snd (𝒯rTyp 𝑡 p))
    -- WebShp {φ = (f , x , ._ , ._)} {𝑡 = ndₒ (𝑝 , 𝑞) 𝑒} (c , y , d , θ , ε , refl) (inl tt) = f , x , c , y
    -- WebShp {φ = (f , x , ._ , ._)} {𝑡 = ndₒ (𝑝 , 𝑞) 𝑒} (c , y , d , θ , ε , refl) (inr (p , q)) = WebShp (ε p) q

    graft : {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
      → {𝑠 : 𝒯r (fst 𝑝)} {𝑡 : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p)}
      → {f : Frm Γₙ 𝑜} (x : Γₛₙ f)
      → (c : Cns Γₙ f (fst 𝑝))
      → (y : Dec' Γₛₙ c)
      → (ψ : Web (f , x , c , y) 𝑠)
      → (d : Dec (Cns Γₙ) (snd 𝑝) c)
      → (z : (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p)) → Γₛₙ (Shp Γₙ (d p) q))
      → (ω : (p : Pos (fst 𝑝)) → Web (Shp Γₙ c p , y p , d p , z p) (𝑡 p)) 
      → Web (f , x , μ Γₙ (c , d) , λ p → z (fstₒ 𝑝 p) (sndₒ 𝑝 p)) (γₒ 𝑠 𝑡)
    graft = {!!} 

  --   graft (lf {𝑜} {f} x) 𝑞₁ 𝑒₁ d₁ y₁ ε₁ = ε₁ (ηₒ-pos 𝑜)
  --   graft (nd {𝑝 = 𝑝} φ 𝑞 𝑒 d y ε) 𝑞₁ 𝑒₁ d₁ y₁ ε₁ =
  --     let 𝑞' p = μₒ (𝑞 p) (𝑞-ih p)
  --         d' p = μ Γₙ (d p) (d-ih p)
  --         𝑒' p = γₒ (𝑒 p) (𝑞-ih p) (𝑒-ih p)
  --         y' p q = y₁ (pairₒ 𝑝 𝑞 p (fstₒ (𝑞 p) (𝑞-ih p) q)) (sndₒ (𝑞 p) (𝑞-ih p) q)
  --         ε' p = graft (ε p) (𝑞-ih p) (𝑒-ih p) (d-ih p) (y-ih p) (ε-ih p)
  --     in nd φ 𝑞' 𝑒' d' y' ε'  

  --       where 𝑞-ih : (p : Pos 𝑝) (q : Pos (𝑞 p)) → 𝒫 (Typ (𝑞 p) q)
  --             𝑞-ih p q = 𝑞₁ (pairₒ 𝑝 𝑞 p q)

  --             𝑒-ih : (p : Pos 𝑝) (q : Pos (𝑞 p)) → 𝒯r (Typ (𝑞 p) q) (𝑞-ih p q)
  --             𝑒-ih p q = 𝑒₁ (pairₒ 𝑝 𝑞 p q)

  --             d-ih : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Cns Γₙ (Shp Γₙ (d p) q) (𝑞-ih p q)
  --             d-ih p q = d₁ (pairₒ 𝑝 𝑞 p q)
  
  --             y-ih : (p : Pos 𝑝) (q : Pos (𝑞 p)) (r : Pos (𝑞-ih p q))  → Γₛₙ (Shp Γₙ (d-ih p q) r)
  --             y-ih p q = y₁ (pairₒ 𝑝 𝑞 p q)

  --             ε-ih : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Web ⟪ Shp Γₙ (d p) q , d-ih p q , y p q , y-ih p q ⟫ (𝑒-ih p q)
  --             ε-ih p q = ε₁ (pairₒ 𝑝 𝑞 p q) 

  --     -- TODO: Grafting Axioms

  𝕆Ctx ℓ zero = Lift Unit 
  𝕆Ctx ℓ (suc n) = Σ (𝕆Ctx ℓ n) (λ Γₙ → {𝑜 : 𝒪 n} → Frm Γₙ 𝑜 → Type ℓ)
  
  Frm {n = zero} X tt = Lift Unit
  Frm {n = suc n} (Γₙ , Γₛₙ) (𝑜 , 𝑝) = WebFrm Γₙ Γₛₙ 𝑝 

  Cns {n = zero} _ _ _ = Lift Unit 
  Cns {n = suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} = Web Γₙ Γₛₙ {𝑜} {𝑝} 
  
  Shp {n = zero} _ _ _ = lift tt
  Shp {n = suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} ψ p = {!!} -- WebShp Γₙ Γₛₙ ω p
  
  -- η : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
  --   → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
  --   → Cns Γ f (ηₒ 𝑜)
  η {n = zero} Γ f = lift tt
  η {n = suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} (f , x , c , y) = {!!} 
    -- let d p = η Γₙ (Shp Γₙ c p)
    --     θ p q = y p
    --     ε p = idp
    -- in c , y , d , θ , ε , idp
    
  -- -- μ : ∀ {n ℓ} (X : 𝕆Ctx ℓ n)
  -- --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  -- --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  -- --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  -- --   → (𝑒 : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
  -- --   → Cns X f (μₒ 𝑝 𝑞)
  -- μ {n = zero} _ _ _ = lift tt
  -- μ {n = suc n} (Γₙ , Γₛₙ) (lf x) θ = lf x
  -- μ {n = suc n} (Γₙ , Γₛₙ) (nd φ 𝑞 𝑒 d y ε) {ζ} θ =
  --   let ω = θ (inl tt)
  --       𝑒' p = μₒ (𝑒 p) (λ q → ζ (inr (p , q)))
  --       ε' p = μ (Γₙ , Γₛₙ) (ε p) (λ q → θ (inr (p , q)))
  --   in graft Γₙ Γₛₙ ω 𝑞 𝑒' d y ε'
  μ = {!!}
  
  --
  -- The terminal opetopic context
  --
  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Ctx ℓ n
  𝕋 zero = lift tt
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 
