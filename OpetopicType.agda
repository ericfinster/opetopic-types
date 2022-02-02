--
--  OpetopicType.agda - Definition of Opetopic Types in Context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Prelude
open import Opetopes
open import OpetopicCtx

module OpetopicType where

  𝕆Type : ∀ {n ℓ₀} (Γ : 𝕆Ctx n ℓ₀)
    → (ℓ : Level) → Type (ℓ-max ℓ₀ (ℓ-suc ℓ))

  Frm↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜) → Type ℓ
    
  Cns↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
    → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝) → Type ℓ 

  Shp↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
    → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
    → (p : Pos 𝑝) → Frm↓ X (Shp Γ c p) 

  η↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
    → Cns↓ X f↓ (η Γ f)

  {-# TERMINATING #-}
  μ↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
    → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
    → (d↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (d p))
    → Cns↓ X f↓ (μ Γ c d)
    
  postulate

    η↓-shp : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → (p : Pos (ηₒ 𝑜))
      → Shp↓ X (η↓ X f↓) p ↦ f↓
    {-# REWRITE η↓-shp #-}

    μ↓-shp : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (d p))
      → (p : Pos (μₒ (𝑝 , 𝑞)))
      → Shp↓ X (μ↓ X c↓ d↓) p ↦ Shp↓ X (d↓ (fstₒ (𝑝 , 𝑞) p)) (sndₒ (𝑝 , 𝑞) p)
    {-# REWRITE μ↓-shp #-} 

    μ↓-unit-r : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → μ↓ X c↓ (λ p → η↓ X (Shp↓ X c↓ p)) ↦ c↓
    {-# REWRITE μ↓-unit-r #-} 

    μ↓-unit-l : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑞 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p)}
      → {d : (p : Pos (ηₒ 𝑜)) → Cns Γ f (𝑞 p)}
      → (d↓ : (p : Pos (ηₒ 𝑜)) → Cns↓ X f↓ (d p))
      → μ↓ X (η↓ X f↓) d↓ ↦ d↓ (ηₒ-pos 𝑜)
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (d p))
      → {𝑟 : (p : Pos (μₒ (𝑝 , 𝑞))) → 𝒫 (Typ (μₒ (𝑝 , 𝑞)) p)}
      → {e : (p : Pos (μₒ (𝑝 , 𝑞))) → Cns Γ (Shp Γ (μ Γ c d) p) (𝑟 p)}
      → (e↓ : (p : Pos (μₒ (𝑝 , 𝑞))) → Cns↓ X (Shp↓ X (μ↓ X c↓ d↓) p) (e p))
      → μ↓ X (μ↓ X c↓ d↓) e↓ ↦ μ↓ X c↓ (λ p → μ↓ X (d↓ p) (λ q → e↓ (pairₒ (𝑝 , 𝑞) p q)))
    {-# REWRITE μ↓-assoc #-} 


  module _ {n ℓ₀ ℓ} {Γₙ : 𝕆Ctx n ℓ₀} {Γₛₙ : {𝑜 : 𝒪 n} (f : Frm Γₙ 𝑜) → Type ℓ₀}
           (Xₙ : 𝕆Type Γₙ ℓ) (Xₛₙ : {𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (f↓ : Frm↓ Xₙ f) → Γₛₙ f → Type ℓ)
    where

    -- Not a good name.  Just a placeholder ...
    IdentType : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm Γₙ 𝑜} (c : Cns Γₙ f 𝑝)
      → (y : (p : Pos 𝑝) → Γₛₙ (Shp Γₙ c p))
      → (f↓ : Frm↓ Xₙ f)
      → Type ℓ
    IdentType {𝑝 = 𝑝} c y f↓ = 
      Σ[ c↓ ∈ Cns↓ Xₙ f↓ c ]
      ((p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ c↓ p) (y p))

    WebFrm↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (φ : WebFrm Γₙ Γₛₙ 𝑝) → Type ℓ
    WebFrm↓ {𝑝 = 𝑝} (f , x , c , y) = 
      Σ[ f↓ ∈ Frm↓ Xₙ f ]
      Σ[ x↓ ∈ Xₛₙ f↓ x ]
      IdentType c y f↓

    Web↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm Γₙ Γₛₙ 𝑝} {𝑡 : 𝒯r 𝑝}
      → WebFrm↓ φ → Web Γₙ Γₛₙ φ 𝑡 → Type ℓ
    Web↓ {𝑜} .{_} {f , x , ._ , ._} (f↓ , x↓ , ηc↓ , ηy↓) (lf x) =
      Ident (IdentType (η Γₙ f) (const x) f↓) (η↓ Xₙ f↓ , const x↓) (ηc↓ , ηy↓)
    Web↓ {𝑜} .{_}  {f , x , ._ , ._} (f↓ , x↓ , μc↓ , μy↓) (nd .{𝑜} {𝑝} {𝑞} x c y d z ψ) =
      Σ[ c↓ ∈ Cns↓ Xₙ f↓ c ]
      Σ[ y↓ ∈ ((p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ c↓ p) (y p)) ]
      Σ[ d↓ ∈ ((p : Pos 𝑝) → Cns↓ Xₙ (Shp↓ Xₙ c↓ p) (d p)) ]
      Σ[ z↓ ∈ ((p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp↓ Xₙ (d↓ p) q) (z p q)) ]
      Σ[ ψ↓ ∈ ((p : Pos 𝑝) → Web↓ (Shp↓ Xₙ c↓ p , y↓ p , d↓ p , z↓ p) (ψ p)) ]
      Ident (IdentType (μ Γₙ c d) (λ p → z (fstₒ (𝑝 , 𝑞) p) (sndₒ (𝑝 , 𝑞) p)) f↓)
        (μ↓ Xₙ c↓ d↓ , λ p → z↓ (fstₒ (𝑝 , 𝑞) p) (sndₒ (𝑝 , 𝑞) p)) (μc↓ , μy↓)

    WebShp↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm Γₙ Γₛₙ 𝑝} {𝑡 : 𝒯r 𝑝}
      → {φ↓ : WebFrm↓ φ} {ω : Web Γₙ Γₛₙ φ 𝑡} (ω↓ : Web↓ φ↓ ω)
      → (p : 𝒯rPos 𝑡) → WebFrm↓ (WebShp Γₙ Γₛₙ ω p)
    WebShp↓ {φ↓ = f↓ , x↓ , ._ , ._} {ω = nd x c y d z ψ} (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) (inl tt) = f↓ , x↓ , c↓ , y↓
    WebShp↓ {φ↓ = f↓ , x↓ , ._ , ._} {ω = nd x c y d z ψ} (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) (inr (p , q)) = WebShp↓ (ψ↓ p) q 

    graft↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} 
      → {𝑠 : 𝒯r 𝑝} {f : Frm Γₙ 𝑜} {x : Γₛₙ f} {c : Cns Γₙ f 𝑝}
      → {y : (p : Pos 𝑝) → Γₛₙ (Shp Γₙ c p)}
      → {ψ : Web Γₙ Γₛₙ (f , x , c , y) 𝑠}
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {𝑡 : (p : Pos 𝑝) → 𝒯r (𝑞 p)}
      → {d : (p : Pos 𝑝) → Cns Γₙ (Shp Γₙ c p) (𝑞 p)}
      → {z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Γₛₙ (Shp Γₙ (d p) q)}
      → {ω : (p : Pos 𝑝) → Web Γₙ Γₛₙ (Shp Γₙ c p , y p , d p , z p) (𝑡 p)}
      → {f↓ : Frm↓ Xₙ f} (x↓ : Xₛₙ f↓ x) (c↓ : Cns↓ Xₙ f↓ c)
      → (y↓ : (p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ c↓ p) (y p))
      → (ψ↓ : Web↓ (f↓ , x↓ , c↓ , y↓) ψ)
      → (d↓ : (p : Pos 𝑝) → Cns↓ Xₙ (Shp↓ Xₙ c↓ p) (d p))
      → (z↓ : (p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp↓ Xₙ (d↓ p) q) (z p q))
      → (ω↓ : (p : Pos 𝑝) → Web↓ (Shp↓ Xₙ c↓ p , y↓ p , d↓ p , z↓ p) (ω p))
      → Web↓ (f↓ , x↓ , μ↓ Xₙ c↓ d↓ , λ p → z↓ (fstₒ (𝑝 , 𝑞) p) (sndₒ (𝑝 , 𝑞) p))
             (graft Γₙ Γₛₙ x c y ψ d z ω)
    graft↓ {𝑜} {ψ = lf _} x↓ ._ ._ idp d↓ z↓ ω↓ = ω↓ (ηₒ-pos 𝑜)
    graft↓ {ψ = nd {𝑜} {𝑝} {𝑞} x c y d z ψ} {𝑞𝑞} x↓ ._ ._ (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) dd↓ zz↓ ω↓ =
      let d↓' p   = μ↓ Xₙ (d↓ p) (λ q → dd↓ (pairₒ (𝑝 , 𝑞) p q))
          z↓' p q = zz↓ (pairₒ (𝑝 , 𝑞) p (fstₒ (𝑞 p , λ q → 𝑞𝑞 (pairₒ (𝑝 , 𝑞) p q)) q))
                         (sndₒ (𝑞 p , λ q → 𝑞𝑞 (pairₒ (𝑝 , 𝑞) p q)) q)
          ψ↓' p   = graft↓ (y↓ p) (d↓ p) (z↓ p) (ψ↓ p)
                      (λ q → dd↓ (pairₒ (𝑝 , 𝑞) p q))
                      (λ q → zz↓ (pairₒ (𝑝 , 𝑞) p q))
                      (λ q → ω↓ (pairₒ (𝑝 , 𝑞) p q))
      in (c↓ , y↓ , d↓' , z↓' , ψ↓' , idp)

  --
  --  Implementations
  --
  
  𝕆Type {n = zero} Γ ℓ = Lift Unit
  𝕆Type {n = suc n} (Γₙ , Γₛₙ) ℓ =
    Σ[ Xₙ ∈ 𝕆Type Γₙ ℓ ]
    ({𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (f↓ : Frm↓ Xₙ f) → Γₛₙ f → Type ℓ)

  Frm↓ {n = zero} X _ = Lift Unit
  Frm↓ {n = suc n} (Xₙ , Xₛₙ) φ = WebFrm↓ Xₙ Xₛₙ φ

  Cns↓ {n = zero} _ _ _ = Lift Unit 
  Cns↓ {n = suc n} (Xₙ , Xₛₙ) ω = Web↓ Xₙ Xₛₙ ω
  
  Shp↓ {n = zero} _ _ _ = lift tt
  Shp↓ {n = suc n} (Xₙ , Xₛₙ) ω↓ p = WebShp↓ Xₙ Xₛₙ ω↓ p


  -- η↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
  --   → Cns↓ X f↓ (η Γ f)
  η↓ {n = zero} X f↓ = lift tt
  η↓ {n = suc n} (Xₙ , Xₛₙ) (f↓ , x↓ , c↓ , y↓) = 
    let d↓ p = η↓ Xₙ (Shp↓ Xₙ c↓ p)
        z↓ p q = y↓ p
        ψ↓ p = idp
    in (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) 

  -- μ↓ : ∀ {n ℓ₀ ℓ} {Γ : 𝕆Ctx n ℓ₀} (X : 𝕆Type Γ ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
  --   → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
  --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
  --   → (d↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (d p))
  --   → Cns↓ X f↓ (μ Γ c d) 
  μ↓ {n = zero} X c↓ d↓ = lift tt
  μ↓ {n = suc n} (Xₙ , Xₛₙ) {c = lf x} c↓ ω↓ = c↓
  μ↓ {n = suc n} (Xₙ , Xₛₙ) {c = nd x c y d z ψ} (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) ω↓ = 
    graft↓ Xₙ Xₛₙ _ c↓ y↓ (ω↓ (inl tt)) d↓ z↓
      (λ p → μ↓ (Xₙ , Xₛₙ) (ψ↓ p) (λ q → ω↓ (inr (p , q))))

  --
  --  Infinite dimensional types
  --
  
  record 𝕆Type∞ {n ℓ₀ ℓ₁} {Γₙ : 𝕆Ctx n ℓ₀} (Γ : 𝕆Ctx∞ ℓ₀ Γₙ)
      (Xₙ : 𝕆Type Γₙ ℓ₁) : Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁)) where
    coinductive
    field
      FillTy : {𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} → Frm↓ Xₙ f → Fill Γ f → Type ℓ₁
      HomTy : 𝕆Type∞ (Hom Γ) (Xₙ , FillTy)

  open 𝕆Type∞ 
