--
--  OpetopicCtx.agda - Opetopic Contexts
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

  -- Ech.  You should invert the order of the
  -- level and dimension here....
  𝕆Ctx : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  
  Frm : ∀ {n ℓ} → 𝕆Ctx n ℓ → 𝒪 n → Type ℓ
  Cns : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
    → 𝒫 𝑜 → Type ℓ 
  Shp : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
    → (p : Pos 𝑝) → Frm Γ (Typ 𝑝 p) 

  η : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
    → Cns Γ f (ηₒ 𝑜)

  {-# TERMINATING #-}
  μ : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → (d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p))
    → Cns Γ f (μₒ (𝑝 , 𝑞))

  postulate

    η-pos-shp : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
      → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
      → (p : Pos (ηₒ 𝑜))
      → Shp Γ (η Γ f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p))
      → (p : Pos (μₒ (𝑝 , 𝑞)))
      → Shp Γ (μ Γ c d) p ↦ Shp Γ (d (fstₒ (𝑝 , 𝑞) p)) (sndₒ (𝑝 , 𝑞) p)
    {-# REWRITE μ-pos-shp #-} 

    -- Monad Laws
    μ-unit-r : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
      → {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → {f : Frm Γ 𝑜} (c : Cns Γ f 𝑝)
      → μ Γ c (λ p → η Γ (Shp Γ c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
      → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
      → (𝑞 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p))
      → (d : (p : Pos (ηₒ 𝑜)) → Cns Γ f (𝑞 p))
      → μ Γ (η Γ f) d ↦ d (ηₒ-pos 𝑜)
    {-# REWRITE μ-unit-l #-} 

    μ-assoc : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p))
      → (𝑟 : (p : Pos (μₒ (𝑝 , 𝑞))) → 𝒫 (Typ (μₒ (𝑝 , 𝑞)) p))
      → (e : (p : Pos (μₒ (𝑝 , 𝑞))) → Cns Γ (Shp Γ (d (fstₒ (𝑝 , 𝑞) p)) (sndₒ (𝑝 , 𝑞) p)) (𝑟 p))
      → μ Γ (μ Γ c d) e
        ↦ μ Γ c (λ p → μ Γ (d p) (λ q → e (pairₒ (𝑝 , 𝑞) p q)))
    {-# REWRITE μ-assoc #-}
    
  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Γₙ : 𝕆Ctx n ℓ) (Γₛₙ : {𝑜 : 𝒪 n} (f : Frm Γₙ 𝑜) → Type ℓ) where
  
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
        → (ψ : (p : Pos 𝑝) → Web (Shp Γₙ c p , y p , d p , z p) (𝑠 p)) 
        → Web (f , x , μ Γₙ c d , λ p → z (fstₒ (𝑝 , 𝑞) p) (sndₒ (𝑝 , 𝑞) p)) (ndₒ (𝑝 , 𝑞) 𝑠) 

    WebShp : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm 𝑝} {𝑡 : 𝒯r 𝑝}
      → (ω : Web φ 𝑡) (p : 𝒯rPos 𝑡)
      → WebFrm (snd (𝒯rTyp 𝑡 p))
    WebShp (nd x c y d z ψ) (inl tt) = _ , x , c , y
    WebShp (nd x c y d z ψ) (inr (p , q)) = WebShp (ψ p) q
    
    graft : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} 
      → {𝑠 : 𝒯r 𝑝} {f : Frm Γₙ 𝑜} (x : Γₛₙ f) (c : Cns Γₙ f 𝑝)
      → (y : (p : Pos 𝑝) → Γₛₙ (Shp Γₙ c p))
      → (ψ : Web (f , x , c , y) 𝑠)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {𝑡 : (p : Pos 𝑝) → 𝒯r (𝑞 p)}
      → (d : (p : Pos 𝑝) → Cns Γₙ (Shp Γₙ c p) (𝑞 p))
      → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Γₛₙ (Shp Γₙ (d p) q))
      → (ω : (p : Pos 𝑝) → Web (Shp Γₙ c p , y p , d p , z p) (𝑡 p)) 
      → Web (f , x , μ Γₙ c d , λ p → z (fstₒ (𝑝 , 𝑞) p) (sndₒ (𝑝 , 𝑞) p)) (graftₒ 𝑠 𝑡)
    graft {𝑜} x ._ ._ (lf .x) d z ω = ω (ηₒ-pos 𝑜)
    graft {_} x ._ ._ (nd {𝑜} {𝑝} {𝑞} .x c y d z ψ) {𝑞𝑞} dd zz ω =
      nd x c y
        (λ p → μ Γₙ (d p) (λ q → dd (pairₒ (𝑝 , 𝑞) p q)))
        (λ p q → zz (pairₒ (𝑝 , 𝑞) p (fstₒ (𝑞 p , λ q → 𝑞𝑞 (pairₒ (𝑝 , 𝑞) p q)) q))
                    (sndₒ (𝑞 p , λ q → 𝑞𝑞 (pairₒ (𝑝 , 𝑞) p q)) q))
        (λ p → graft (y p) (d p) (z p) (ψ p)
                 (λ q → dd (pairₒ (𝑝 , 𝑞) p q))
                 (λ q → zz (pairₒ (𝑝 , 𝑞) p q))
                 (λ q → ω (pairₒ (𝑝 , 𝑞) p q)))
    
      -- TODO: Grafting Axioms

  𝕆Ctx zero ℓ = Lift Unit 
  𝕆Ctx (suc n) ℓ = Σ (𝕆Ctx n ℓ) (λ Γₙ → {𝑜 : 𝒪 n} → Frm Γₙ 𝑜 → Type ℓ)
  
  Frm {zero} X tt = Lift Unit
  Frm {suc n} (Γₙ , Γₛₙ) (𝑜 , 𝑝) = WebFrm Γₙ Γₛₙ 𝑝 

  Cns {zero} _ _ _ = Lift Unit 
  Cns {suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} = Web Γₙ Γₛₙ {𝑜} {𝑝} 
  
  Shp {zero} _ _ _ = lift tt
  Shp {suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} ψ p = WebShp Γₙ Γₛₙ ψ p
  
  -- η : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
  --   → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
  --   → Cns Γ f (ηₒ 𝑜)
  η {zero} Γ f = lift tt
  η {suc n} (Γₙ , Γₛₙ) {𝑜 , 𝑝} (f , x , c , y) =  
    let d p = η Γₙ (Shp Γₙ c p)
        z p q = y p
        ψ p = lf (y p) 
    in nd x c y d z ψ

  -- μ : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
  --   → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
  --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → (d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p))
  --   → Cns Γ f (μₒ (𝑝 , 𝑞))
  μ {zero} Γ c d = lift tt
  μ {suc n} (Γₙ , Γₛₙ) (lf x) d = lf x
  μ {suc n} (Γₙ , Γₛₙ) (nd x c y d z ψ) ω =
    graft Γₙ Γₛₙ x c y (ω (inl tt)) d z 
      (λ p → μ (Γₙ , Γₛₙ) (ψ p) (λ q → ω (inr (p , q))))

  --
  --  The terminal opetopic context
  --
  𝕋 : (n : ℕ) → 𝕆Ctx n ℓ-zero
  𝕋 zero = lift tt
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 


  --
  --  Infinite dimensional contexts
  --
  
  record 𝕆Ctx∞ {n ℓ} (Γ : 𝕆Ctx n ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      Fill : {o : 𝒪 n} → Frm Γ o → Type ℓ 
      Hom : 𝕆Ctx∞ (Γ , Fill) 

  open 𝕆Ctx∞ public
