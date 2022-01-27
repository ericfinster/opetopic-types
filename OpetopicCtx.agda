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

  -- --
  -- --  Definition of the Derived Monad 
  -- --

  -- module _ {ℓ n} (Xₙ : 𝕆Ctx ℓ n) (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ) where
  
  --   η-dec : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) (x : Xₛₙ f)
  --     → (p : Pos (ηₒ 𝑜)) → Xₛₙ (Shp Xₙ (η Xₙ f) p)
  --   η-dec {𝑜} f x = ηₒ-pos-elim 𝑜 (λ p → Xₛₙ (Shp Xₙ (η Xₙ f) p)) x 

  --   μ-dec : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
  --     → (𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --     → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑑 p))
  --     → (ν : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Xₛₙ (Shp Xₙ (δ p) q))
  --     → (p : Pos (μₒ 𝑝 𝑑)) → Xₛₙ (Shp Xₙ (μ Xₙ c δ) p)
  --   μ-dec {𝑝 = 𝑝} c 𝑑 δ ν p = ν (fstₒ 𝑝 𝑑 p) (sndₒ 𝑝 𝑑 p)

  --   {-# NO_POSITIVITY_CHECK #-}
  --   record WebFrm (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜) : Type ℓ where
  --     inductive
  --     eta-equality
  --     constructor ⟪_,_,_,_⟫ 
  --     field
  --       frm : Frm Xₙ 𝑜
  --       cns : Cns Xₙ frm 𝑝
  --       tgt : Xₛₙ frm
  --       src : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ cns p)

  --   open WebFrm public

  --   data Web : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑜 𝑝 → 𝒯r 𝑜 𝑝 → Type ℓ where

  --     lf : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
  --       → Web ⟪ f , η Xₙ f , x , const x ⟫ (lfₒ 𝑜) 

  --     nd : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (φ : WebFrm 𝑜 𝑝)
  --       → (𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --       → (𝑒 : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p) (𝑑 p))
  --       → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ (cns φ) p) (𝑑 p))
  --       → (ν : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Xₛₙ (Shp Xₙ (δ p) q))
  --       → (ε : (p : Pos 𝑝) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (𝑒 p)) 
  --       → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) 𝑑 δ ν ⟫ (ndₒ 𝑜 𝑝 𝑑 𝑒) 

  --   WebShp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑜 𝑝} {𝑡 : 𝒯r 𝑜 𝑝}
  --     → (ω : Web φ 𝑡) (p : 𝒯rPos 𝑡)
  --     → WebFrm (fst (𝒯rTyp 𝑡 p)) (snd (𝒯rTyp 𝑡 p))
  --   WebShp (nd φ 𝑑 𝑒 δ ν ε) (inl tt) = φ
  --   WebShp (nd φ 𝑑 𝑒 δ ν ε) (inr (p , q)) = WebShp (ε p) q

  --   graft : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑜 𝑝} {𝑡 : 𝒯r 𝑜 𝑝} (ω : Web φ 𝑡)
  --     → (𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --     → (𝑒 : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p) (𝑑 p))
  --     → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ (cns φ) p) (𝑑 p))
  --     → (ν : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Xₛₙ (Shp Xₙ (δ p) q))
  --     → (ε : (p : Pos 𝑝) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (𝑒 p)) 
  --     → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) 𝑑 δ ν ⟫ (γₒ 𝑡 𝑑 𝑒)
  --   graft (lf {𝑜} {f} x) 𝑑₁ 𝑒₁ δ₁ ν₁ ε₁ = ε₁ (ηₒ-pos 𝑜)
  --   graft (nd {𝑝 = 𝑝} φ 𝑑 𝑒 δ ν ε) 𝑑₁ 𝑒₁ δ₁ ν₁ ε₁ =
  --     let 𝑑' p = μₒ (𝑑 p) (𝑑-ih p)
  --         δ' p = μ Xₙ (δ p) (δ-ih p)
  --         𝑒' p = γₒ (𝑒 p) (𝑑-ih p) (𝑒-ih p)
  --         ν' p q = ν₁ (pairₒ 𝑝 𝑑 p (fstₒ (𝑑 p) (𝑑-ih p) q)) (sndₒ (𝑑 p) (𝑑-ih p) q)
  --         ε' p = graft (ε p) (𝑑-ih p) (𝑒-ih p) (δ-ih p) (ν-ih p) (ε-ih p)
  --     in nd φ 𝑑' 𝑒' δ' ν' ε'  

  --       where 𝑑-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → 𝒫 (Typ (𝑑 p) q)
  --             𝑑-ih p q = 𝑑₁ (pairₒ 𝑝 𝑑 p q)

  --             𝑒-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → 𝒯r (Typ (𝑑 p) q) (𝑑-ih p q)
  --             𝑒-ih p q = 𝑒₁ (pairₒ 𝑝 𝑑 p q)

  --             δ-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Cns Xₙ (Shp Xₙ (δ p) q) (𝑑-ih p q)
  --             δ-ih p q = δ₁ (pairₒ 𝑝 𝑑 p q)
  
  --             ν-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) (r : Pos (𝑑-ih p q))  → Xₛₙ (Shp Xₙ (δ-ih p q) r)
  --             ν-ih p q = ν₁ (pairₒ 𝑝 𝑑 p q)

  --             ε-ih : (p : Pos 𝑝) (q : Pos (𝑑 p)) → Web ⟪ Shp Xₙ (δ p) q , δ-ih p q , ν p q , ν-ih p q ⟫ (𝑒-ih p q)
  --             ε-ih p q = ε₁ (pairₒ 𝑝 𝑑 p q) 

  --     -- TODO: Grafting Axioms

  -- 𝕆Ctx ℓ zero = Lift Unit 
  -- 𝕆Ctx ℓ (suc n) = Σ (𝕆Ctx ℓ n) (λ Xₙ → {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
  
  -- Frm {n = zero} X tt = Lift Unit
  -- Frm {n = suc n} (Xₙ , Xₛₙ) (𝑜 , 𝑝) = WebFrm Xₙ Xₛₙ 𝑜 𝑝 

  -- Cns {n = zero} _ _ _ = Lift Unit 
  -- Cns {n = suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} = Web Xₙ Xₛₙ {𝑜} {𝑝} 
  
  -- Shp {n = zero} _ _ _ = lift tt
  -- Shp {n = suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} ω p = WebShp Xₙ Xₛₙ ω p

  -- -- η : ∀ {n ℓ} (X : 𝕆Ctx ℓ n)
  -- --   → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
  -- --   → Cns X f (ηₒ 𝑜)
  -- η {n = zero} _ _ = lift tt
  -- η {n = suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} φ =
  --   let 𝑑 p = ηₒ (Typ 𝑝 p)
  --       𝑒 p = lfₒ (Typ 𝑝 p)
  --       δ p = η Xₙ (Shp Xₙ (cns φ) p)
  --       ν p q = src φ p
  --       ε p = lf (src φ p)
  --   in nd φ 𝑑 𝑒 δ ν ε
    
  -- -- μ : ∀ {n ℓ} (X : 𝕆Ctx ℓ n)
  -- --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  -- --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  -- --   → {𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  -- --   → (𝑒 : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑑 p))
  -- --   → Cns X f (μₒ 𝑝 𝑑)
  -- μ {n = zero} _ _ _ = lift tt
  -- μ {n = suc n} (Xₙ , Xₛₙ) (lf x) θ = lf x
  -- μ {n = suc n} (Xₙ , Xₛₙ) (nd φ 𝑑 𝑒 δ ν ε) {ζ} θ =
  --   let ω = θ (inl tt)
  --       𝑒' p = μₒ (𝑒 p) (λ q → ζ (inr (p , q)))
  --       ε' p = μ (Xₙ , Xₛₙ) (ε p) (λ q → θ (inr (p , q)))
  --   in graft Xₙ Xₛₙ ω 𝑑 𝑒' δ ν ε'

  -- --
  -- -- The terminal opetopic context
  -- --
  -- 𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Ctx ℓ n
  -- 𝕋 zero = lift tt
  -- 𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 
