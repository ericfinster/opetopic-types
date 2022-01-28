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

  𝕆Type : ∀ {ℓ₀ n} (Γ : 𝕆Ctx ℓ₀ n)
    → (ℓ : Level) → Type (ℓ-suc ℓ)

  Frm↓ : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜) → Type ℓ
    
  Cns↓ : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
    → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝) → Type ℓ 

  Shp↓ : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
    → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
    → (p : Pos 𝑝) → Frm↓ X (Shp Γ c p) 

  postulate

    η↓ : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → Cns↓ X f↓ (η Γ f)

    μ↓ : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (d p))
      → Cns↓ X f↓ (μ Γ c d) 

    η↓-shp : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → (p : Pos (ηₒ 𝑜))
      → Shp↓ X (η↓ X f↓) p ↦ f↓
    {-# REWRITE η↓-shp #-}

    μ↓-shp : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (d p))
      → (p : Pos (μₒ (𝑝 , 𝑞)))
      → Shp↓ X (μ↓ X c↓ d↓) p ↦ Shp↓ X (d↓ (fstₒ (𝑝 , 𝑞) p)) (sndₒ (𝑝 , 𝑞) p)
    {-# REWRITE μ↓-shp #-} 

    μ↓-unit-r : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → μ↓ X c↓ (λ p → η↓ X (Shp↓ X c↓ p)) ↦ c↓
    {-# REWRITE μ↓-unit-r #-} 

    μ↓-unit-l : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑞 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p)}
      → {d : (p : Pos (ηₒ 𝑜)) → Cns Γ f (𝑞 p)}
      → (d↓ : (p : Pos (ηₒ 𝑜)) → Cns↓ X f↓ (d p))
      → μ↓ X (η↓ X f↓) d↓ ↦ d↓ (ηₒ-pos 𝑜)
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
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


  module _ {ℓ₀ ℓ n} (Γₙ : 𝕆Ctx ℓ₀ n) (Γₛₙ : {𝑜 : 𝒪 n} (f : Frm Γₙ 𝑜) → Type ℓ₀)
           (Xₙ : 𝕆Type Γₙ ℓ) (Xₛₙ : {𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (f↓ : Frm↓ Xₙ f) → Type ℓ)
    where

    IdentType : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm Γₙ 𝑜} (f↓ : Frm↓ Xₙ f)
      → Cns Γₙ f 𝑝 → Type ℓ
    IdentType {𝑝 = 𝑝} f↓ c = 
      Σ[ c↓ ∈ Cns↓ Xₙ f↓ c ]
      ((p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ c↓ p)) 

    WebFrm↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (φ : WebFrm Γₙ Γₛₙ 𝑝) → Type ℓ
    WebFrm↓ {𝑝 = 𝑝} (f , x , c , y) = 
      Σ[ f↓ ∈ Frm↓ Xₙ f ]
      Σ[ x↓ ∈ Xₛₙ f↓ ]
      IdentType f↓ c

    Web↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm Γₙ Γₛₙ 𝑝} {𝑡 : 𝒯r 𝑝}
      → WebFrm↓ φ → Web Γₙ Γₛₙ φ 𝑡 → Type ℓ
    Web↓ {𝑜} .{_} {f , x , ._ , ._} (f↓ , x↓ , ηc↓ , ηy↓) (lf x) =
      Ident (IdentType f↓ (η Γₙ f)) (η↓ Xₙ f↓ , const x↓) (ηc↓ , ηy↓)
    Web↓ {𝑜} .{_}  {f , x , ._ , ._} (f↓ , x↓ , μc↓ , μy↓) (nd .{𝑜} {𝑝} {𝑞} x c y d z ψ) =
      Σ[ c↓ ∈ Cns↓ Xₙ f↓ c ]
      Σ[ y↓ ∈ ((p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ c↓ p)) ]
      Σ[ d↓ ∈ ((p : Pos 𝑝) → Cns↓ Xₙ (Shp↓ Xₙ c↓ p) (d p)) ]
      Σ[ z↓ ∈ ((p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp↓ Xₙ (d↓ p) q)) ]
      Σ[ ψ↓ ∈ ((p : Pos 𝑝) → Web↓ (Shp↓ Xₙ c↓ p , y↓ p , d↓ p , z↓ p) (ψ p)) ]
      Ident (IdentType f↓ (μ Γₙ c d)) ({!!} , {!!}) (μc↓ , μy↓)

  𝕆Type = {!!}
  Frm↓ = {!!}
  Cns↓ = {!!}
  Shp↓ = {!!}

