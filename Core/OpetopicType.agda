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

  η-dec : ∀ {n ℓ} (X : 𝕆Type (suc n) ℓ)
    → {𝑜 : 𝒪 n} {f : Frm (fst X) 𝑜}
    → (x : snd X f)
    → (p : Pos (ηₒ 𝑜)) → snd X (Shp (fst X) (η (fst X) f) p)
  η-dec (Xₙ , Xₛₙ) {𝑜} {f} x = ηₒ-pos-elim 𝑜 (λ p → Xₛₙ (Shp Xₙ (η Xₙ f) p)) x 

  data LfCns {n ℓ} (X : 𝕆Type (suc n) ℓ) {𝑜 : 𝒪 n} : Frm X (𝑜 ∣ ηₒ 𝑜) → Type ℓ where

    lf : {f : Frm (fst X) 𝑜} (x : (snd X) f)
      → LfCns X (f , x , η (fst X) f , η-dec X x) 

  data NdCns {n ℓ} (X : 𝕆Type (suc n) ℓ)
        (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
        (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
        (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
        
    : Frm X (𝑜 ∣ μₒ 𝑝 𝑞) → Type ℓ where

    nd : {f : Frm (fst X) 𝑜} (x : (snd X) f) (c : Cns (fst X) f 𝑝)
      → (y : (p : Pos 𝑝) → (snd X) (Shp (fst X) c p))
      → (d : (p : Pos 𝑝) → Cns (fst X) (Shp (fst X) c p) (𝑞 p))
      → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → (snd X) (Shp (fst X) (d p) q))
      → (ψ : (p : Pos 𝑝) → Cns X (Shp (fst X) c p , y p , d p , z p) (𝑟 p)) 
      → NdCns X 𝑜 𝑝 𝑞 𝑟 (f , x , μ (fst X) c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) 

  Cns X {●} f 𝑝 = Lift Unit
  Cns X {𝑜 ∣ ._} f lfₒ = LfCns X f
  Cns X {𝑜 ∣ ._} f (ndₒ 𝑝 𝑞 𝑟) = NdCns X 𝑜 𝑝 𝑞 𝑟 f

  Shp X {●} {𝑝 = objₒ} c p = tt*
  Shp X {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd {f} x c y d z ψ) (inl tt) = f , x , c , y
  Shp X {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd {f} x c y d z ψ) (inr (p , q)) = Shp X (ψ p) q

  graft : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : {𝑜 : 𝒪 n} → Frm Xₙ 𝑜 → Type ℓ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑞 : 𝒫 (𝑜 ∣ 𝑝)}
    → {𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
    → {𝑡 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑟 p)}
    → {f : Frm Xₙ 𝑜} (x : Xₛₙ f) (c : Cns Xₙ f 𝑝)
    → (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → (ψ : Cns (Xₙ , Xₛₙ) (f , x , c , y) 𝑞)
    → (d : (p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑟 p))
    → (z : (p : Pos 𝑝) (q : Pos (𝑟 p)) → Xₛₙ (Shp Xₙ (d p) q))
    → (ω : (p : Pos 𝑝) → Cns (Xₙ , Xₛₙ) (Shp Xₙ c p , y p , d p , z p) (𝑡 p)) 
    → Cns (Xₙ , Xₛₙ) (f , x , μ Xₙ c d , λ p → z (fstₚ 𝑝 𝑟 p) (sndₚ 𝑝 𝑟 p)) (graftₒ 𝑞 𝑡)
  graft Xₙ Xₛₙ {𝑜} {𝑞 = lfₒ} .x ._ ._ (lf x) dd zz ψψ = ψψ (ηₒ-pos 𝑜)
  graft Xₙ Xₛₙ {𝑜} {𝑞 = ndₒ 𝑝 𝑞 𝑟} {𝑟𝑟} .x ._ ._ (nd x c y d z ψ) dd zz ψψ = 
    let d' p = μ Xₙ (d p) (λ q → dd (pairₚ 𝑝 𝑞 p q))
        z' p q = zz (pairₚ 𝑝 𝑞 p (fstₚ (𝑞 p) (λ q → 𝑟𝑟 (pairₚ 𝑝 𝑞 p q)) q))
                    (sndₚ (𝑞 p) (λ q → 𝑟𝑟 (pairₚ 𝑝 𝑞 p q)) q)
        ψ' p = graft Xₙ Xₛₙ (y p) (d p) (z p) (ψ p)
                 (λ q → dd (pairₚ 𝑝 𝑞 p q))
                 (λ q → zz (pairₚ 𝑝 𝑞 p q))
                 (λ q → ψψ (pairₚ 𝑝 𝑞 p q))
    in nd x c y d' z' ψ'
  
  -- η : ∀ {n ℓ} (X : 𝕆Type n ℓ)
  --   → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
  --   → Cns X f (ηₒ 𝑜)
  η X {●} f = tt*
  η X {𝑜 ∣ 𝑝} (f , x , c , y) =
    let d p = η (fst X) (Shp (fst X) c p)
        z p q = η-dec X (y p) q
        ψ p = lf (y p)
    in nd x c y d z ψ

  -- μ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
  --   → {𝑜 : 𝒪 n} {f : Frm X 𝑜}
  --   → {𝑝 : 𝒫 𝑜} (c : Cns X f 𝑝)
  --   → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
  --   → (d : (p : Pos 𝑝) → Cns X (Shp X c p) (𝑞 p))
  --   → Cns X f (μₒ (𝑝 , 𝑞))
  μ X {●} c d = tt*
  μ X {𝑜 ∣ ._} {𝑝 = lfₒ} (lf x) ω = lf x
  μ X {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd x c y d z ψ) ω = 
    graft (fst X) (snd X) x c y (ω (inl tt)) d z 
      (λ p → μ X (ψ p) (λ q → ω (inr (p , q))))

  --
  --  Infinite dimensional opetopic types
  --
  
  record 𝕆Type∞ {n ℓ} (X : 𝕆Type n ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      Fill : {o : 𝒪 n} → Frm X o → Type ℓ 
      Hom : 𝕆Type∞ (X , Fill) 

  open 𝕆Type∞ public

  --
  --  The skeleton of an infinite opetopic type
  ---
  
  Skeleton : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type n ℓ

  SkeletonExt : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type∞ {ℓ = ℓ} (Skeleton X n) 

  Skeleton X zero = lift tt
  Skeleton X (suc n) = Skeleton X n , Fill (SkeletonExt X n)

  SkeletonExt X zero = X
  SkeletonExt X (suc n) = Hom (SkeletonExt X n)

  --
  --  The terminal opetopic type
  --

  𝕋Ext : ∀ {n ℓ} (X : 𝕆Type n ℓ) → 𝕆Type∞ X
  Fill (𝕋Ext X) _ = Lift Unit
  Hom (𝕋Ext X) = 𝕋Ext (X , (λ _ → Lift Unit))
    
  𝕋 : (n : ℕ) {ℓ : Level} → 𝕆Type n ℓ
  𝕋 zero = lift tt
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit 

  𝕋∞ : ∀ {ℓ} → 𝕆Type∞ tt*
  𝕋∞ {ℓ} = 𝕋Ext {ℓ = ℓ} tt*
