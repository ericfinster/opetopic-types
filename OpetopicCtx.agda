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
  Dec : ∀ {n ℓ ℓ' ℓ''} {Γ : 𝕆Ctx ℓ n}
    → {P : 𝒪 n → Type ℓ''}
    → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → P 𝑜 → Type ℓ')
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → {𝑝 : 𝒫 𝑜} (𝑑 : Decₒ P 𝑝)
    → Cns Γ f 𝑝 → Type ℓ'
  Dec X {𝑝 = 𝑝} 𝑑 c = (p : Pos 𝑝) → X (Shp _ c p) (𝑑 p) 

  ⟦_⟧ : ∀ {n ℓ ℓ' ℓ''} {Γ : 𝕆Ctx ℓ n}
    → {P : 𝒪 n → Type ℓ''}
    → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → P 𝑜 → Type ℓ')
    → {𝑜 : 𝒪 n} → Frm Γ 𝑜 → ⟦ P ⟧ₒ 𝑜 → Type (ℓ-max ℓ ℓ')
  ⟦ X ⟧ {𝑜} f (𝑝 , 𝑑) = Σ (Cns _ f 𝑝) (Dec X 𝑑)

  Dec' : ∀ {n ℓ ℓ'} {Γ : 𝕆Ctx ℓ n}
    → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → Type ℓ')
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → {𝑝 : 𝒫 𝑜} → Cns Γ f 𝑝 → Type ℓ'
  Dec' X {𝑝 = 𝑝} c = (p : Pos 𝑝) → X (Shp _ c p)

  ⟦_⟧' : ∀ {n ℓ ℓ'} {Γ : 𝕆Ctx ℓ n}
    → (X : {𝑜 : 𝒪 n} → Frm Γ 𝑜 → Type ℓ')
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜) (𝑝 : 𝒫 𝑜)
    → Type (ℓ-max ℓ ℓ')
  ⟦ X ⟧' f 𝑝 = Σ (Cns _ f 𝑝) (λ c → Dec' X c)


  -- Monadic signature
  
  η : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
    → Cns Γ f (ηₒ 𝑜)

  μ : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
    → {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜}
    → {f : Frm Γ 𝑜} (c : ⟦ Cns Γ ⟧ f 𝑝)
    → Cns Γ f (μₒ 𝑝)
    
  postulate

    η-pos-shp : ∀ {ℓ n} (X : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → (p : Pos (ηₒ 𝑜))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
      → {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜}
      → {f : Frm Γ 𝑜} (c : ⟦ Cns Γ ⟧ f 𝑝)
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
      → (𝑑 : Decₒ 𝒫 (ηₒ 𝑜))
      → (δ : Dec (Cns Γ) 𝑑 (η Γ f))
      → μ Γ (η Γ f , δ) ↦ δ (ηₒ-pos 𝑜)
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
    
    Web : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑝 → 𝒯r 𝑝 → Type ℓ
    Web (f , x , ηc , ην) lfₒ =
      Ident (⟦ Γₛₙ ⟧' f _) (η Γₙ f , const x) (ηc , ην) 
    Web (f , x , μc , μν) (ndₒ (𝑝 , 𝑑) 𝑒) =
      Σ[ c ∈ Cns Γₙ f 𝑝 ]
      Σ[ ν ∈ Dec' Γₛₙ c ] 
      Σ[ δ ∈ Dec (Cns Γₙ) 𝑑 c ]
      Σ[ θ ∈ ((p : Pos 𝑝) (q : Pos (𝑑 p)) → Γₛₙ (Shp Γₙ (δ p) q)) ]
      Σ[ ε ∈ ((p : Pos 𝑝) → Web (Shp Γₙ c p , ν p , δ p , θ p) (𝑒 p)) ]
      Ident (⟦ Γₛₙ ⟧' f (μₒ (𝑝 , 𝑑))) (μ Γₙ (c , δ) , (λ p → θ (fstₒ (𝑝 , 𝑑) p) (sndₒ (𝑝 , 𝑑) p))) (μc , μν)

    WebShp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑝} {𝑡 : 𝒯r 𝑝}
      → (ω : Web φ 𝑡) (p : 𝒯rPos 𝑡)
      → WebFrm (snd (𝒯rTyp 𝑡 p))
    WebShp {φ = (f , x , ._ , ._)} {𝑡 = ndₒ (𝑝 , 𝑑) 𝑒} (c , ν , δ , θ , ε , refl) (inl tt) = f , x , c , ν
    WebShp {φ = (f , x , ._ , ._)} {𝑡 = ndₒ (𝑝 , 𝑑) 𝑒} (c , ν , δ , θ , ε , refl) (inr (p , q)) = WebShp (ε p) q

    graft : {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
      → (𝑡 : 𝒯r (fst 𝑝)) (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → {f : Frm Γₙ 𝑜} (x : Γₛₙ f)
      → (c : Cns Γₙ f (fst 𝑝))
      → (ν : Dec' Γₛₙ c)
      → (ω : Web (f , x , c , ν) 𝑡)
      → (δ : Dec (Cns Γₙ) (snd 𝑝) c)
      → (θ : (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p)) → Γₛₙ (Shp Γₙ (δ p) q))
      → (ε : (p : Pos (fst 𝑝)) → Web (Shp Γₙ c p , ν p , δ p , θ p) (ψ p)) 
      → Web (f , x , μ Γₙ (c , δ) , (λ p → θ (fstₒ 𝑝 p) (sndₒ 𝑝 p))) (γₒ 𝑡 ψ)
    graft {𝑜 = 𝑜} lfₒ ψ x ._ ._ idp δ θ ε = ε (ηₒ-pos 𝑜)
    graft (ndₒ (𝑝 , 𝑑) 𝑒) ψ x c ν ω δ θ ε₁ = {!!}

  --   graft (lf {𝑜} {f} x) 𝑑₁ 𝑒₁ δ₁ ν₁ ε₁ = ε₁ (ηₒ-pos 𝑜)
  --   graft (nd {𝑝 = 𝑝} φ 𝑑 𝑒 δ ν ε) 𝑑₁ 𝑒₁ δ₁ ν₁ ε₁ =
  --     let 𝑑' p = μₒ (𝑑 p) (𝑑-ih p)
  --         δ' p = μ Γₙ (δ p) (δ-ih p)
  --         𝑒' p = γₒ (𝑒 p) (𝑑-ih p) (𝑒-ih p)
  --         ν' p q = ν₁ (pairₒ 𝑝 𝑑 p (fstₒ (𝑑 p) (𝑑-ih p) q)) (sndₒ (𝑑 p) (𝑑-ih p) q)
  --         ε' p = graft (ε p) (𝑑-ih p) (𝑒-ih p) (δ-ih p) (ν-ih p) (ε-ih p)
  --     in nd φ 𝑑' 𝑒' δ' ν' ε'  

  --       where 𝑑-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → 𝒫 (Typ (𝑑 p) q)
  --             𝑑-ih p q = 𝑑₁ (pairₒ 𝑝 𝑑 p q)

  --             𝑒-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → 𝒯r (Typ (𝑑 p) q) (𝑑-ih p q)
  --             𝑒-ih p q = 𝑒₁ (pairₒ 𝑝 𝑑 p q)

  --             δ-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Cns Γₙ (Shp Γₙ (δ p) q) (𝑑-ih p q)
  --             δ-ih p q = δ₁ (pairₒ 𝑝 𝑑 p q)
  
  --             ν-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) (r : Pos (𝑑-ih p q))  → Γₛₙ (Shp Γₙ (δ-ih p q) r)
  --             ν-ih p q = ν₁ (pairₒ 𝑝 𝑑 p q)

  --             ε-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Web ⟪ Shp Γₙ (δ p) q , δ-ih p q , ν p q , ν-ih p q ⟫ (𝑒-ih p q)
  --             ε-ih p q = ε₁ (pairₒ 𝑝 𝑑 p q) 

  --     -- TODO: Grafting Axioms

  𝕆Ctx ℓ zero = Lift Unit 
  𝕆Ctx ℓ (suc n) = Σ (𝕆Ctx ℓ n) (λ Γₙ → {𝑜 : 𝒪 n} → Frm Γₙ 𝑜 → Type ℓ)
  
  Frm {n = zero} X tt = Lift Unit
  Frm {n = suc n} (Γₙ , Γₛₙ) (𝑜 , 𝑝) = WebFrm Γₙ Γₛₙ 𝑝 

  Cns {n = zero} _ _ _ = Lift Unit 
  Cns {n = suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} = Web Γₙ Γₛₙ {𝑜} {𝑝} 
  
  Shp {n = zero} _ _ _ = lift tt
  Shp {n = suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} ω p = WebShp Γₙ Γₛₙ ω p
  
  -- η : ∀ {n ℓ} (Γ : 𝕆Ctx ℓ n)
  --   → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
  --   → Cns Γ f (ηₒ 𝑜)
  η {n = zero} Γ f = lift tt
  η {n = suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} (f , x , c , ν) =
    let δ p = η Γₙ (Shp Γₙ c p)
        θ p q = ν p
        ε p = idp
    in c , ν , δ , θ , ε , idp
    
  -- -- μ : ∀ {n ℓ} (X : 𝕆Ctx ℓ n)
  -- --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  -- --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  -- --   → {𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  -- --   → (𝑒 : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑑 p))
  -- --   → Cns X f (μₒ 𝑝 𝑑)
  -- μ {n = zero} _ _ _ = lift tt
  -- μ {n = suc n} (Γₙ , Γₛₙ) (lf x) θ = lf x
  -- μ {n = suc n} (Γₙ , Γₛₙ) (nd φ 𝑑 𝑒 δ ν ε) {ζ} θ =
  --   let ω = θ (inl tt)
  --       𝑒' p = μₒ (𝑒 p) (λ q → ζ (inr (p , q)))
  --       ε' p = μ (Γₙ , Γₛₙ) (ε p) (λ q → θ (inr (p , q)))
  --   in graft Γₙ Γₛₙ ω 𝑑 𝑒' δ ν ε'
  μ = {!!}
  
  --
  -- The terminal opetopic context
  --
  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Ctx ℓ n
  𝕋 zero = lift tt
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 
