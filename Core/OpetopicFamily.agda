--
--  OpetopicFamily.agda - Dependent families of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Core.Opetopes
open import Core.OpetopicType

module Core.OpetopicFamily where

  𝕆Fam : ∀ {n ℓ₀} (X : 𝕆Type n ℓ₀)
    → (ℓ : Level) → Type (ℓ-max ℓ₀ (ℓ-suc ℓ))

  Frm↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
    → {𝑜 : 𝒪 n} (f : Frm X 𝑜) → Type ℓ
    
  Cns↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜} (f↓ : Frm↓ P f)
    → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝) → Type ℓ 

  Shp↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
    → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
    → (p : Pos 𝑝) → Frm↓ P (Shp X c p) 
  
  η↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜} (f↓ : Frm↓ P f)
    → Cns↓ P f↓ (η X f)

  μ↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
    → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
    → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
    → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → {d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p)}
    → (d↓ : (p : Pos 𝑝) → Cns↓ P (Shp↓ P c↓ p) (d p))
    → Cns↓ P f↓ (μ X c d)
    
  postulate

    η↓-shp : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} (f↓ : Frm↓ P f)
      → (p : Pos (ηₒ 𝑜))
      → Shp↓ P (η↓ P f↓) p ↦ f↓
    {-# REWRITE η↓-shp #-}

    μ↓-shp : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} (f↓ : Frm↓ P f)
      → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ P (Shp↓ P c↓ p) (d p))
      → (p : Pos (μₒ 𝑝 𝑞))
      → Shp↓ P (μ↓ P c↓ d↓) p ↦ Shp↓ P (d↓ (fstₚ 𝑝 𝑞 p)) (sndₚ 𝑝 𝑞 p)
    {-# REWRITE μ↓-shp #-} 

    μ↓-unit-r : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
      → μ↓ P c↓ (λ p → η↓ P (Shp↓ P c↓ p)) ↦ c↓
    {-# REWRITE μ↓-unit-r #-} 

    μ↓-unit-l : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → {𝑞 : (p : Pos (ηₒ 𝑜)) → 𝒫 (Typ (ηₒ 𝑜) p)}
      → {d : (p : Pos (ηₒ 𝑜)) → Cns X f (𝑞 p)}
      → (d↓ : (p : Pos (ηₒ 𝑜)) → Cns↓ P f↓ (d p))
      → μ↓ P (η↓ P f↓) d↓ ↦ d↓ (ηₒ-pos 𝑜)
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
      → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
      → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p)}
      → (d↓ : (p : Pos 𝑝) → Cns↓ P (Shp↓ P c↓ p) (d p))
      → {𝑟 : (p : Pos (μₒ 𝑝 𝑞)) → 𝒫 (Typ (μₒ 𝑝 𝑞) p)}
      → {e : (p : Pos (μₒ 𝑝 𝑞)) → Cns X (Shp X (μ X c d) p) (𝑟 p)}
      → (e↓ : (p : Pos (μₒ 𝑝 𝑞)) → Cns↓ P (Shp↓ P (μ↓ P c↓ d↓) p) (e p))
      → μ↓ P (μ↓ P c↓ d↓) e↓ ↦ μ↓ P c↓ (λ p → μ↓ P (d↓ p) (λ q → e↓ (pairₚ 𝑝 𝑞 p q)))
    {-# REWRITE μ↓-assoc #-} 

  --
  --  Implementations
  --
  
  𝕆Fam {n = zero} X ℓ = Lift Unit
  𝕆Fam {n = suc n} (Xₙ , Xₛₙ) ℓ =
    Σ[ Pₙ ∈ 𝕆Fam Xₙ ℓ ]
    ({𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (f↓ : Frm↓ Pₙ f) → Xₛₙ f → Type ℓ)

  Frm↓ P {●} f = Lift Unit
  Frm↓ (Pₙ , Pₛₙ) {𝑜 ∣ 𝑝} (f , x , c , y) = 
    Σ[ f↓ ∈ Frm↓ Pₙ f ]
    Σ[ x↓ ∈ Pₛₙ f↓ x ]
    Σ[ c↓ ∈ Cns↓ Pₙ f↓ c ]
    ((p : Pos 𝑝) → Pₛₙ (Shp↓ Pₙ c↓ p) (y p))  

  data LfCns↓ {n ℓ₀ ℓ₁} {X : 𝕆Type (suc n) ℓ₀} (P : 𝕆Fam X ℓ₁)
      {𝑜 : 𝒪 n} {f : Frm (fst X) 𝑜} (x : (snd X) f)
    : Frm↓ P (f , x , η (fst X) f , const x) → Type ℓ₁ where

    lf↓ : {f↓ : Frm↓ (fst P) f} (x↓ : (snd P) f↓ x)
      → LfCns↓ P x (f↓ , x↓ , η↓ (fst P) f↓ , const x↓)

  data NdCns↓ {n ℓ₀ ℓ₁} {X : 𝕆Type (suc n) ℓ₀} (P : 𝕆Fam X ℓ₁)
        {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
        {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
        {𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p)}
        {f : Frm (fst X) 𝑜} (x : (snd X) f) (c : Cns (fst X) f 𝑝)
        (y : (p : Pos 𝑝) → (snd X) (Shp (fst X) c p))
        (d : (p : Pos 𝑝) → Cns (fst X) (Shp (fst X) c p) (𝑞 p))
        (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → (snd X) (Shp (fst X) (d p) q))
        (ψ : (p : Pos 𝑝) → Cns X (Shp (fst X) c p , y p , d p , z p) (𝑟 p)) 
    : Frm↓ P (f , x , μ (fst X) c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) → Type ℓ₁ where

    nd↓ : {f↓ : Frm↓ (fst P) f} (x↓ : (snd P) f↓ x) (c↓ : Cns↓ (fst P) f↓ c) 
      → (y↓ : ((p : Pos 𝑝) → (snd P) (Shp↓ (fst P) c↓ p) (y p)))
      → (d↓ : ((p : Pos 𝑝) → Cns↓ (fst P) (Shp↓ (fst P) c↓ p) (d p)))
      → (z↓ : ((p : Pos 𝑝) (q : Pos (𝑞 p)) → (snd P) (Shp↓ (fst P) (d↓ p) q) (z p q)))
      → (ψ↓ : ((p : Pos 𝑝) → Cns↓ P (Shp↓ (fst P) c↓ p , y↓ p , d↓ p , z↓ p) (ψ p)))
      → NdCns↓ P x c y d z ψ (f↓ , x↓ , μ↓ (fst P) c↓ d↓ , λ p → z↓ (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p))

  Cns↓ P {●} f c = Lift Unit
  Cns↓ P {𝑜 ∣ ._} f {lfₒ} (lf x) = LfCns↓ P x f
  Cns↓ P {𝑜 ∣ ._} f {ndₒ 𝑝 𝑞 𝑟} (nd x c y d z ψ) = NdCns↓ P x c y d z ψ f
  
  Shp↓ P {●} {𝑝 = objₒ} c↓ p = tt*
  Shp↓ P {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} {c = nd x c y d z ψ} (nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓) (inl tt) = _ , x↓ , c↓ , y↓
  Shp↓ P {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} {c = nd x c y d z ψ} (nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓) (inr (p , q)) = Shp↓ P (ψ↓ p) q 

  graft↓ : ∀ {n ℓ₀ ℓ} {Xₙ : 𝕆Type n ℓ₀} {Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ₀}
    → (Pₙ : 𝕆Fam Xₙ ℓ) (Pₛₙ : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (f↓ : Frm↓ Pₙ f) → Xₛₙ f → Type ℓ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑞 : 𝒫 (𝑜 ∣ 𝑝)}
    → {𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → {𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑟 p)}
    → {f : Frm Xₙ 𝑜} {x : Xₛₙ f} {c : Cns Xₙ f 𝑝}
    → {y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p)}
    → {ψ : Cns (Xₙ , Xₛₙ) (f , x , c , y) 𝑞}
    → {d : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑟 p)}
    → {z : (p : Pos 𝑝) (q : Pos (𝑟 p)) → Xₛₙ (Shp Xₙ (d p) q)}
    → {ω : (p : Pos 𝑝) → Cns (Xₙ , Xₛₙ) (Shp Xₙ c p , y p , d p , z p) (𝑡 p)}
    → {f↓ : Frm↓ Pₙ f} (x↓ : Pₛₙ f↓ x) (c↓ : Cns↓ Pₙ f↓ c)
    → (y↓ : (p : Pos 𝑝) → Pₛₙ (Shp↓ Pₙ c↓ p) (y p))
    → (ψ↓ : Cns↓ (Pₙ , Pₛₙ) (f↓ , x↓ , c↓ , y↓) ψ)
    → (d↓ : (p : Pos 𝑝) → Cns↓ Pₙ (Shp↓ Pₙ c↓ p) (d p))
    → (z↓ : (p : Pos 𝑝) (q : Pos (𝑟 p)) → Pₛₙ (Shp↓ Pₙ (d↓ p) q) (z p q))
    → (ω↓ : (p : Pos 𝑝) → Cns↓ (Pₙ , Pₛₙ) (Shp↓ Pₙ c↓ p , y↓ p , d↓ p , z↓ p) (ω p))
    → Cns↓ (Pₙ , Pₛₙ) (f↓ , x↓ , μ↓ Pₙ c↓ d↓ , λ p → z↓ (fstₚ 𝑝 𝑟 p) (sndₚ 𝑝 𝑟 p))
           (graft Xₙ Xₛₙ x c y ψ d z ω)
  graft↓ Pₙ Pₛₙ {𝑜} {𝑞 = lfₒ} {ψ = lf x} .x↓ ._ ._ (lf↓ x↓) dd↓ zz↓ ω↓ = ω↓ (ηₒ-pos 𝑜)
  graft↓ Pₙ Pₛₙ {𝑜} {𝑞 = ndₒ 𝑝 𝑞 𝑟} {𝑟 = 𝑟𝑟} {ψ = nd x c y d z ψ} .x↓ ._ ._ (nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓) dd↓ zz↓ ω↓ = 
    let d↓' p   = μ↓ Pₙ (d↓ p) (λ q → dd↓ (pairₚ 𝑝 𝑞 p q))
        z↓' p q = zz↓ (pairₚ 𝑝 𝑞 p (fstₚ (𝑞 p) (λ q → 𝑟𝑟 (pairₚ 𝑝 𝑞 p q)) q))
                       (sndₚ (𝑞 p) (λ q → 𝑟𝑟 (pairₚ 𝑝 𝑞 p q)) q)
        ψ↓' p   = graft↓ Pₙ Pₛₙ (y↓ p) (d↓ p) (z↓ p) (ψ↓ p)
                    (λ q → dd↓ (pairₚ 𝑝 𝑞 p q))
                    (λ q → zz↓ (pairₚ 𝑝 𝑞 p q))
                    (λ q → ω↓ (pairₚ 𝑝 𝑞 p q))
    in nd↓ x↓ c↓ y↓ d↓' z↓' ψ↓' 
  
  -- η↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜} (f↓ : Frm↓ P f)
  --   → Cns↓ P f↓ (η X f)
  η↓ P {●} f↓ = tt*
  η↓ (Pₙ , Pₛₙ) {𝑜 ∣ 𝑝} (f↓ , x↓ , c↓ , y↓) = 
    let d↓ p = η↓ Pₙ (Shp↓ Pₙ c↓ p)
        z↓ p q = y↓ p
        ψ↓ p = lf↓ (y↓ p)
    in nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓ 

  -- μ↓ : ∀ {n ℓ₀ ℓ} {X : 𝕆Type n ℓ₀} (P : 𝕆Fam X ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜} {f↓ : Frm↓ P f}
  --   → {𝑝 : 𝒫 𝑜} {c : Cns X f 𝑝} (c↓ : Cns↓ P f↓ c)
  --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → {d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p)}
  --   → (d↓ : (p : Pos 𝑝) → Cns↓ P (Shp↓ P c↓ p) (d p))
  --   → Cns↓ P f↓ (μ X c d)
  μ↓ P {●} c↓ d↓ = tt*
  μ↓ P {𝑜 ∣ ._} {𝑝 = lfₒ} {c = lf x} c↓ d↓ = c↓
  μ↓ (Pₙ , Pₛₙ) {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} {c = nd x c y d z ψ} (nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓) ω↓ = 
    graft↓ Pₙ Pₛₙ _ c↓ y↓ (ω↓ (inl tt)) d↓ z↓
      (λ p → μ↓ (Pₙ , Pₛₙ) (ψ↓ p) (λ q → ω↓ (inr (p , q))))

  --
  --  Infinite dimensional families
  --
  
  record 𝕆Fam∞ {n ℓ₀ ℓ₁} {Xₙ : 𝕆Type n ℓ₀} (X : 𝕆Type∞ Xₙ)
      (Pₙ : 𝕆Fam Xₙ ℓ₁) : Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁)) where
    coinductive
    field
      FillTy : {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} → Frm↓ Pₙ f → Fill X f → Type ℓ₁
      HomTy : 𝕆Fam∞ (Hom X) (Pₙ , FillTy)

  open 𝕆Fam∞ public

  
