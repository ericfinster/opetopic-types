{-# OPTIONS --rewriting #-}
--
--  OpetopicTypes2.agda - Basic Constructions on Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Prelude
open import Opetopes
open import OpetopicType
open import OpetopicMap

module OpetopicType2 where

  -- The product of two opetopic types.
  infixl 45 _×ₒ_
  
  _×ₒ_ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : 𝕆 ℓ₁ n) → 𝕆 (ℓ-max ℓ₀ ℓ₁) n
  π₀ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} → X ×ₒ Y ⇒ X
  π₁ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} → X ×ₒ Y ⇒ Y

  _×ₒ_ {n = zero} X Y = lift tt
  _×ₒ_ {n = suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Xₙ ×ₒ Yₙ , λ f → Xₛₙ (Frm⇒ π₀ f) × Yₛₙ (Frm⇒ π₁ f)

  π₀ {n = zero} {X} {Y} = lift tt
  π₀ {n = suc n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} =
    π₀ {X = Xₙ} {Y = Yₙ} , fst
  
  π₁ {n = zero} {X} {Y} = lift tt
  π₁ {n = suc n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} = 
    π₁ {X = Xₙ} {Y = Yₙ} , snd

  -- Hmm.  So you gave the elim principles.  But what about the intro?
  
  -- Frm-pair : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : 𝕆 ℓ₁ n)
  --   → {o : 𝒪 n} (fX : Frm X o) (fY : Frm Y o)
  --   → Frm (X ×ₒ Y) o
  -- Frm-pair {n = zero} X Y fx fy = lift tt
  -- Frm-pair {n = suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) fx fy =
  --   ⟪ Frm-pair Xₙ Yₙ (frm fx) (frm fy) , {!!} , ({!tgt fx!} , {!!}) , {!!} ⟫

  -- The pullback of two opetopic types 
  Pb : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n} 
    → (f : X ⇒ Z) (g : Y ⇒ Z) → 𝕆 (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ₂) n
  
  pb-fst : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n}
    → (f : X ⇒ Z) (g : Y ⇒ Z) → Pb f g ⇒ X
    
  pb-snd : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n}
    → (f : X ⇒ Z) (g : Y ⇒ Z) → Pb f g ⇒ Y
  
  pb-comm : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} {Z : 𝕆 ℓ₂ n}
    → (f : X ⇒ Z) (g : Y ⇒ Z)
    → f ⊚ pb-fst f g ≡ g ⊚ pb-snd f g 

  Pb {n = zero} f g = lift tt
  Pb {n = suc n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (fₙ , fₛₙ) (gₙ , gₛₙ) = 
    Pb fₙ gₙ , λ {o} φ →
      Σ (Xₛₙ (Frm⇒ (pb-fst fₙ gₙ) φ)) (λ x →
      Σ (Yₛₙ (Frm⇒ (pb-snd fₙ gₙ) φ)) (λ y →
        PathP (λ i → Zₛₙ (Frm⇒ (pb-comm fₙ gₙ i) φ)) (fₛₙ x) (gₛₙ y)))
  
  pb-fst {n = zero} _ _ = lift tt
  pb-fst {n = suc n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (fₙ , fₛₙ) (gₙ , gₛₙ) =
    pb-fst fₙ gₙ , λ { (x , _ , _) → x } 

  pb-snd {n = zero} _ _ = lift tt
  pb-snd {n = suc n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (fₙ , fₛₙ) (gₙ , gₛₙ) =
    pb-snd fₙ gₙ , λ { (_ , y , _) → y } 

  pb-comm {n = zero} _ _ = refl
  pb-comm {n = suc n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (fₙ , fₛₙ) (gₙ , gₛₙ) =
    λ i → pb-comm fₙ gₙ i , λ {o} {φ} → λ { (x , y , e) → e i} 

  --
  -- What is a global section?
  --

  Sec : ∀ {ℓ n} (X : 𝕆 ℓ n) → Type ℓ
  
  Frm-Sec : ∀ {ℓ n} {X : 𝕆 ℓ n} (σ : Sec X)
    → (o : 𝒪 n) → Frm X o
    
  Cns-Sec : ∀ {ℓ n} {X : 𝕆 ℓ n} (σ : Sec X)
    → {o : 𝒪 n} (ρ : 𝒫 o)
    → Cns X (Frm-Sec σ o) ρ 

  postulate

    Shp-Frm-Cns : ∀ {ℓ n} (X : 𝕆 ℓ n) (σ : Sec X)
      → {o : 𝒪 n} (ρ : 𝒫 o) (p : Pos ρ)
      → Frm-Sec σ (Typ ρ p) ↦ Shp X (Cns-Sec σ ρ) p 
    {-# REWRITE Shp-Frm-Cns #-}

    η-Sec : ∀ {ℓ n} (X : 𝕆 ℓ n) (σ : Sec X)
      → (o : 𝒪 n)
      → η X (Frm-Sec σ o) ↦ Cns-Sec σ (ηₒ o)
    {-# REWRITE η-Sec #-}

  Sec {n = zero} X = Lift Unit
  Sec {n = suc n} (Xₙ , Xₛₙ) =
    Σ (Sec Xₙ) (λ σ → (o : 𝒪 n) → Xₛₙ (Frm-Sec σ o))

  Frm-Sec {n = zero} σ o = lift tt
  Frm-Sec {n = suc n} {Xₙ , Xₛₙ} (σₙ , σₛₙ) (o , ρ) =
    ⟪ Frm-Sec σₙ o  , Cns-Sec σₙ ρ , σₛₙ o , (λ p → σₛₙ (Typ ρ p)) ⟫

  Cns-Sec {n = zero} σ ρ = lift tt
  Cns-Sec {n = suc n} {Xₙ , Xₛₙ} (σₙ , σₛₙ) {o , .(ηₒ o)} (lfₒ .o) = lf (σₛₙ o)
  Cns-Sec {n = suc n} σ {o , .(μₒ ρ δ)} (ndₒ .o ρ δ ε) = {!!}

