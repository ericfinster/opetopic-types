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

  {-# TERMINATING #-}
  μ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
    → Cns X f (μₒ (𝑝 , 𝑞))

  postulate

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
      → (p : Pos (μₒ (𝑝 , 𝑞)))
      → Shp X (μ X c d) p ↦ Shp X (d (fstₚ (𝑝 , 𝑞) p)) (sndₚ (𝑝 , 𝑞) p)
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
      → (𝑟 : (p : Pos (μₒ (𝑝 , 𝑞))) → 𝒫 (Typ (μₒ (𝑝 , 𝑞)) p))
      → (e : (p : Pos (μₒ (𝑝 , 𝑞))) → Cns X (Shp X (d (fstₚ (𝑝 , 𝑞) p)) (sndₚ (𝑝 , 𝑞) p)) (𝑟 p))
      → μ X (μ X c d) e
        ↦ μ X c (λ p → μ X (d p) (λ q → e (pairₚ (𝑝 , 𝑞) p q)))
    {-# REWRITE μ-assoc #-}
    
  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ) where
  
    WebFrm : {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) →  Type ℓ
    WebFrm {𝑜} 𝑝 =
      Σ[ f ∈ Frm Xₙ 𝑜 ]
      Σ[ x ∈ Xₛₙ f ]
      Σ[ c ∈ Cns Xₙ f 𝑝 ]
      ((p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))  

    data Web : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑝 → 𝒯r 𝑝 → Type ℓ where

      lf : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
        → Web (f , x , η Xₙ f , const x) lfₒ

      nd : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
        → {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
        → (c : Cns Xₙ f 𝑝) (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
        → {𝑠 : (p : Pos 𝑝) → 𝒯r (𝑞 p)}
        → (d : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑞 p))
        → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp Xₙ (d p) q))
        → (ψ : (p : Pos 𝑝) → Web (Shp Xₙ c p , y p , d p , z p) (𝑠 p)) 
        → Web (f , x , μ Xₙ c d , λ p → z (fstₚ (𝑝 , 𝑞) p) (sndₚ (𝑝 , 𝑞) p)) (ndₒ (𝑝 , 𝑞) 𝑠) 

    WebShp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑝} {𝑡 : 𝒯r 𝑝}
      → (ω : Web φ 𝑡) (p : 𝒯rPos 𝑡)
      → WebFrm (snd (𝒯rTyp 𝑡 p))
    WebShp (nd x c y d z ψ) (inl tt) = _ , x , c , y
    WebShp (nd x c y d z ψ) (inr (p , q)) = WebShp (ψ p) q
    
    graft : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} 
      → {𝑠 : 𝒯r 𝑝} {f : Frm Xₙ 𝑜} (x : Xₛₙ f) (c : Cns Xₙ f 𝑝)
      → (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
      → (ψ : Web (f , x , c , y) 𝑠)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {𝑡 : (p : Pos 𝑝) → 𝒯r (𝑞 p)}
      → (d : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑞 p))
      → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp Xₙ (d p) q))
      → (ω : (p : Pos 𝑝) → Web (Shp Xₙ c p , y p , d p , z p) (𝑡 p)) 
      → Web (f , x , μ Xₙ c d , λ p → z (fstₚ (𝑝 , 𝑞) p) (sndₚ (𝑝 , 𝑞) p)) (graftₒ 𝑠 𝑡)
    graft {𝑜} x ._ ._ (lf .x) d z ω = ω (ηₒ-pos 𝑜)
    graft {_} x ._ ._ (nd {𝑜} {𝑝} {𝑞} .x c y d z ψ) {𝑞𝑞} dd zz ω =
      nd x c y
        (λ p → μ Xₙ (d p) (λ q → dd (pairₚ (𝑝 , 𝑞) p q)))
        (λ p q → zz (pairₚ (𝑝 , 𝑞) p (fstₚ (𝑞 p , λ q → 𝑞𝑞 (pairₚ (𝑝 , 𝑞) p q)) q))
                    (sndₚ (𝑞 p , λ q → 𝑞𝑞 (pairₚ (𝑝 , 𝑞) p q)) q))
        (λ p → graft (y p) (d p) (z p) (ψ p)
                 (λ q → dd (pairₚ (𝑝 , 𝑞) p q))
                 (λ q → zz (pairₚ (𝑝 , 𝑞) p q))
                 (λ q → ω (pairₚ (𝑝 , 𝑞) p q)))
    
      -- TODO: Grafting Axioms

  𝕆Type zero ℓ = Lift Unit 
  𝕆Type (suc n) ℓ = Σ (𝕆Type n ℓ) (λ Xₙ → {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
  
  Frm {zero} X tt = Lift Unit
  Frm {suc n} (Xₙ , Xₛₙ) (𝑜 , 𝑝) = WebFrm Xₙ Xₛₙ 𝑝 

  Cns {zero} _ _ _ = Lift Unit 
  Cns {suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} = Web Xₙ Xₛₙ {𝑜} {𝑝} 
  
  Shp {zero} _ _ _ = lift tt
  Shp {suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} ψ p = WebShp Xₙ Xₛₙ ψ p
  
  -- η : ∀ {n ℓ} (X : 𝕆Type n ℓ)
  --   → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
  --   → Cns X f (ηₒ 𝑜)
  η {zero} X f = lift tt
  η {suc n} (Xₙ , Xₛₙ) {𝑜 , 𝑝} (f , x , c , y) =  
    let d p = η Xₙ (Shp Xₙ c p)
        z p q = y p
        ψ p = lf (y p) 
    in nd x c y d z ψ

  -- μ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
  --   → Cns X f (μₒ (𝑝 , 𝑞))
  μ {zero} X c d = lift tt
  μ {suc n} (Xₙ , Xₛₙ) (lf x) d = lf x
  μ {suc n} (Xₙ , Xₛₙ) (nd x c y d z ψ) ω =
    graft Xₙ Xₛₙ x c y (ω (inl tt)) d z 
      (λ p → μ (Xₙ , Xₛₙ) (ψ p) (λ q → ω (inr (p , q))))

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
