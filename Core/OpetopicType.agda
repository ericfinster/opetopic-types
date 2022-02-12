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
open import Core.Opetopes

module Core.OpetopicType where
  
  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → 𝒪 n → Type ℓ
  Cns : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
    → 𝒫 𝑜 → Type ℓ 
  Shp : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
    → (p : Pos 𝑝) → Frm X (Typ 𝑝 p) 

  η : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
    → Cns X f (ηₒ 𝑜)

  μ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
    → Cns X f (μₒ 𝑝 𝑞)

  postulate

    -- shape compatibilities
    η-pos-shp : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → (p : Pos (ηₒ 𝑜))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
      → (p : Pos (μₒ 𝑝 𝑞))
      → Shp X (μ X c d) p ↦ Shp X (d (fstₚ 𝑝 𝑞 p)) (sndₚ 𝑝 𝑞 p)
    {-# REWRITE μ-pos-shp #-} 

    -- Monad Laws
    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → {f : Frm X 𝑜} (c : Cns X f 𝑝)
      → μ X c (λ p → η X (Shp X c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → (𝑞 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → (d : (p : Pos (ηₒ 𝑜)) → Cns X f (𝑞 p))
      → μ X (η X f) d ↦ d (ηₒ-pos 𝑜)
    {-# REWRITE μ-unit-l #-} 

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
      → (𝑟 : (p : Pos (μₒ 𝑝 𝑞)) → 𝒫 (Typ (μₒ 𝑝 𝑞) p))
      → (e : (p : Pos (μₒ 𝑝 𝑞)) → Cns X (Shp X (d (fstₚ 𝑝 𝑞 p)) (sndₚ 𝑝 𝑞 p)) (𝑟 p))
      → μ X (μ X c d) e
        ↦ μ X c (λ p → μ X (d p) (λ q → e (pairₚ 𝑝 𝑞 p q)))
    {-# REWRITE μ-assoc #-}
    
  --
  --  Implementation of the Polynomials
  --

  𝕆Type zero ℓ = Lift Unit 
  𝕆Type (suc n) ℓ = Σ (𝕆Type n ℓ) (λ Xₙ → {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
  
  Frm {zero} X ● = Lift Unit
  Frm {suc n} (Xₙ , Xₛₙ) (𝑜 ∣ 𝑝) = 
    Σ[ f ∈ Frm Xₙ 𝑜 ]
    Σ[ x ∈ Xₛₙ f ]
    Σ[ c ∈ Cns Xₙ f 𝑝 ]
    ((p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))  

  DecCns : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → Frm Xₙ 𝑜 → Type ℓ
  DecCns Xₙ Xₛₙ {𝑝 = 𝑝} f =
    Σ[ c ∈ Cns Xₙ f 𝑝 ]
    ((p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p)) 

  Cns X f objₒ = Lift Unit
  Cns (Xₙ , Xₛₙ) {𝑜 ∣ ._} (f , x , μc , μy) lfₒ = 
    Ident (DecCns Xₙ Xₛₙ {𝑜} {ηₒ 𝑜} f) (η Xₙ f , const x) (μc , μy)
  Cns (Xₙ , Xₛₙ) {𝑜 ∣ ._} (f , x , μc , μy) (ndₒ 𝑝 𝑞 𝑟) = 
    Σ[ c ∈ Cns Xₙ f 𝑝 ]
    Σ[ y ∈ ((p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p)) ]
    Σ[ d ∈ ((p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑞 p)) ] 
    Σ[ z ∈ ((p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp Xₙ (d p) q)) ]
    Σ[ ψ ∈ ((p : Pos 𝑝) → Cns (Xₙ , Xₛₙ) (Shp Xₙ c p , y p , d p , z p) (𝑟 p)) ]
    Ident (DecCns Xₙ Xₛₙ {𝑜} {μₒ 𝑝 𝑞} f) (μ Xₙ c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) (μc , μy) 

  Shp X {f = f} {objₒ} c p = tt*
  Shp (Xₙ , Xₛₙ) {𝑜 ∣ ._} {f = f , x , ._ , ._} {ndₒ 𝑝 𝑞 𝑟} (c , y , d , z , ψ , idp) (inl tt) = f , x , c , y 
  Shp (Xₙ , Xₛₙ) {𝑜 ∣ ._} {f = f , x , ._ , ._} {ndₒ 𝑝 𝑞 𝑟} (c , y , d , z , ψ , idp) (inr (p , q)) = Shp (Xₙ , Xₛₙ) (ψ p) q

  graft : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑠 : 𝒫 (𝑜 ∣ 𝑝)}
    → {f : Frm Xₙ 𝑜} (x : Xₛₙ f) (c : Cns Xₙ f 𝑝)
    → (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → (ψ : Cns (Xₙ , Xₛₙ) (f , x , c , y) 𝑠)
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → {𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p)}
    → (d : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑞 p))
    → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp Xₙ (d p) q))
    → (ω : (p : Pos 𝑝) → Cns (Xₙ , Xₛₙ) (Shp Xₙ c p , y p , d p , z p) (𝑡 p)) 
    → Cns (Xₙ , Xₛₙ) (f , x , μ Xₙ c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) (graftₒ 𝑠 𝑡)
  graft Xₙ Xₛₙ {𝑜 = 𝑜} {𝑠 = lfₒ} x ._ ._ idp d z ω = ω (ηₒ-pos 𝑜)
  graft Xₙ Xₛₙ {𝑜 = 𝑜} {𝑠 = ndₒ 𝑝 𝑞 𝑟} x ._ ._ (c , y , d , z , ψ , idp) {𝑞𝑞} dd zz ψψ =
    let d' p = μ Xₙ (d p) (λ q → dd (pairₚ 𝑝 𝑞 p q))
        z' p q = zz (pairₚ 𝑝 𝑞 p (fstₚ (𝑞 p) (λ q → 𝑞𝑞 (pairₚ 𝑝 𝑞 p q)) q))
                    (sndₚ (𝑞 p) (λ q → 𝑞𝑞 (pairₚ 𝑝 𝑞 p q)) q)
        ψ' p = graft Xₙ Xₛₙ (y p) (d p) (z p) (ψ p)
                 (λ q → dd (pairₚ 𝑝 𝑞 p q))
                 (λ q → zz (pairₚ 𝑝 𝑞 p q))
                 (λ q → ψψ (pairₚ 𝑝 𝑞 p q))
    in c , y , d' , z' , ψ' , idp 
  
  -- η : ∀ {n ℓ} (X : 𝕆Type n ℓ)
  --   → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
  --   → Cns X f (ηₒ 𝑜)
  η X {●} f = tt*
  η (Xₙ , Xₛₙ) {𝑜 ∣ 𝑝} (f , x , c , y) =
    let d p = η Xₙ (Shp Xₙ c p)
        z p q = y p
        ψ p = idp 
    in c , y , d , z , ψ , idp
  
  -- μ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
  --   → Cns X f (μₒ (𝑝 , 𝑞))
  μ X {𝑝 = objₒ} c d = tt*
  μ X {𝑝 = lfₒ} idp d = idp
  μ (Xₙ , Xₛₙ) {𝑜 = 𝑜 ∣ ._} {f = f , x , ._ , ._} {ndₒ 𝑝 𝑞 𝑟} (c , y , d , z , ψ , idp) {𝑞𝑞} ψψ =  {!!} 
    -- graft Xₙ Xₛₙ {𝑠 = 𝑞𝑞 (inl tt)} x c y (ψψ (inl tt)) d z 
    --   (λ p → μ (Xₙ , Xₛₙ) (ψ p) {𝑞 = λ q → 𝑞𝑞 (inr (p , q))} (λ q → ψψ (inr (p , q))))

  --
  --  The terminal opetopic context
  --
  𝕋 : (n : ℕ) {ℓ : Level} → 𝕆Type n ℓ
  𝕋 zero = lift tt
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 

  --
  --  Infinite dimensional contexts
  --
  
  record 𝕆Type∞ {n} (ℓ : Level) (X : 𝕆Type n ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      Fill : {o : 𝒪 n} → Frm X o → Type ℓ 
      Hom : 𝕆Type∞ ℓ (X , Fill) 

  open 𝕆Type∞ public
