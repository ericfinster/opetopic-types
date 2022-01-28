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
      → {𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {δ : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑑 p)}
      → (δ↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (δ p))
      → Cns↓ X f↓ (μ Γ c δ) 

    η↓-shp : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → (p : Pos (ηₒ 𝑜))
      → Shp↓ X (η↓ X f↓) p ↦ f↓
    {-# REWRITE η↓-shp #-}

    μ↓-shp : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} (f↓ : Frm↓ X f)
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → {𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {δ : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑑 p)}
      → (δ↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (δ p))
      → (p : Pos (μₒ (𝑝 , 𝑑)))
      → Shp↓ X (μ↓ X c↓ δ↓) p ↦ Shp↓ X (δ↓ (fstₒ (𝑝 , 𝑑) p)) (sndₒ (𝑝 , 𝑑) p)
    {-# REWRITE μ↓-shp #-} 

    μ↓-unit-r : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → μ↓ X c↓ (λ p → η↓ X (Shp↓ X c↓ p)) ↦ c↓
    {-# REWRITE μ↓-unit-r #-} 

    μ↓-unit-l : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑑 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p)}
      → {δ : (p : Pos (ηₒ 𝑜)) → Cns Γ f (𝑑 p)}
      → (δ↓ : (p : Pos (ηₒ 𝑜)) → Cns↓ X f↓ (δ p))
      → μ↓ X (η↓ X f↓) δ↓ ↦ δ↓ (ηₒ-pos 𝑜)
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ₀ ℓ n} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜} {f↓ : Frm↓ X f}
      → {𝑝 : 𝒫 𝑜} {c : Cns Γ f 𝑝} (c↓ : Cns↓ X f↓ c)
      → {𝑑 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {δ : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑑 p)}
      → (δ↓ : (p : Pos 𝑝) → Cns↓ X (Shp↓ X c↓ p) (δ p))
      → {𝑒 : (p : Pos (μₒ (𝑝 , 𝑑))) → 𝒫 (Typ (μₒ (𝑝 , 𝑑)) p)}
      → {ε : (p : Pos (μₒ (𝑝 , 𝑑))) → Cns Γ (Shp Γ (μ Γ c δ) p) (𝑒 p)}
      → (ε↓ : (p : Pos (μₒ (𝑝 , 𝑑))) → Cns↓ X (Shp↓ X (μ↓ X c↓ δ↓) p) (ε p))
      → μ↓ X (μ↓ X c↓ δ↓) ε↓ ↦ μ↓ X c↓ (λ p → μ↓ X (δ↓ p) (λ q → ε↓ (pairₒ (𝑝 , 𝑑) p q)))
    {-# REWRITE μ↓-assoc #-} 


  module _ {ℓ₀ ℓ n} (Γₙ : 𝕆Ctx ℓ₀ n) (Γₛₙ : {𝑜 : 𝒪 n} (f : Frm Γₙ 𝑜) → Type ℓ₀)
           (Xₙ : 𝕆Type Γₙ ℓ) (Xₛₙ : {𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (f↓ : Frm↓ Xₙ f) → Type ℓ)
    where
  
    -- η-dec : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) (x : Xₛₙ f)
    --   → (p : Pos (ηₒ 𝑜)) → Xₛₙ (Shp Xₙ (η Xₙ f) p)
    -- η-dec {𝑜} f x = ηₒ-pos-elim 𝑜 (λ p → Xₛₙ (Shp Xₙ (η Xₙ f) p)) x 

    -- μ-dec : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
    --   → (ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    --   → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (ι p))
    --   → (ν : (p : Pos 𝑝) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
    --   → (p : Pos (μₒ 𝑝 ι)) → Xₛₙ (Shp Xₙ (μ Xₙ c δ) p)
    -- μ-dec {𝑝 = 𝑝} c ι δ ν p = ν (μₒ-pos-fst 𝑝 ι p) (μₒ-pos-snd 𝑝 ι p)

    -- record WebFrm↓ {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (φ : WebFrm Γₙ Γₛₙ 𝑜 𝑝) : Type ℓ where
    --   inductive
    --   eta-equality
    --   constructor ⟪_,_,_,_⟫↓
    --   field
    --     frm↓ : Frm↓ Xₙ (frm φ)
    --     cns↓ : Cns↓ Xₙ frm↓ (cns φ)
    --     tgt↓ : Xₛₙ frm↓
    --     src↓ : (p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ cns↓ p)

    -- open WebFrm↓ public

    -- This is simply the action of the appropriate polynomial.
    -- Perhaps you could simplify things a bit by making this
    -- a formal definition?
    
    -- CnsAndDec : {𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (f↓ : Frm↓ Xₙ f)
    --   → {𝑝 : 𝒫 𝑜} (c : Cns Γₙ f 𝑝)
    --   → Type ℓ
    -- CnsAndDec f↓ {𝑝 = 𝑝} c = Σ (Cns↓ Xₙ f↓ c) (λ c↓ → (p : Pos 𝑝) → Xₛₙ (Shp↓ Xₙ c↓ p)) 

    -- Web↓ : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {φ : WebFrm Γₙ Γₛₙ 𝑜 𝑝} {𝑡 : 𝒯r 𝑜 𝑝}
    --   → WebFrm↓ φ → Web Γₙ Γₛₙ φ 𝑡 → Type ℓ
    -- Web↓ {φ = ⟪ f , ._ , g , ._ ⟫} ⟪ f↓ , c↓ , x↓ , ν↓ ⟫↓ (lf 𝑜) =
    --   Ident (CnsAndDec f↓ (η Γₙ f)) (c↓ , ν↓) (η↓ Xₙ f↓ , const x↓)
    -- Web↓ {φ = ⟪ f , ._ , g , ._ ⟫} ⟪ f↓ , c↓ , x↓ , ν↓ ⟫↓ (nd φ 𝑑 𝑒 δ ν ε) =
    --   Ident (CnsAndDec f↓ (μ Γₙ (cns φ) δ)) (c↓ , ν↓) ({!!} , {!!})

    -- data Web : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} → WebFrm 𝑜 𝑝 → 𝒯r 𝑜 𝑝 → Type ℓ where

    --   lf : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
    --     → Web ⟪ f , η Xₙ f , x , const x ⟫ (lfₒ 𝑜) 

    --   nd : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} (φ : WebFrm 𝑜 𝑝)
    --     → (ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
    --     → (κ : (p : Pos 𝑝) → 𝒯r (Typ 𝑝 p) (ι p))
    --     → (δ : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ (cns φ) p) (ι p))
    --     → (ν : (p : Pos 𝑝) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
    --     → (ε : (p : Pos 𝑝) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (κ p)) 
    --     → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) ι δ ν ⟫ (ndₒ 𝑜 𝑝 ι κ) 

  𝕆Type = {!!}
  Frm↓ = {!!}
  Cns↓ = {!!}
  Shp↓ = {!!}

