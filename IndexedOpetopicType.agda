{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes

module IndexedOpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ n} → 𝕆 ℓ n → 𝒪 n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} (f : Frm X o)
    → 𝒫 o → Set ℓ 
  Shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} {f : Frm X o}
    → {ρ : 𝒫 o} (c : Cns X f ρ)
    → (p : Pos ρ) → Frm X (Typ ρ p) 

  postulate

    η : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o)
      → Cns X f (ηₒ o)

    μ : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → Cns X f (μₒ ρ ι)

  postulate

    η-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o)
      → (p : Pos (ηₒ o))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → (p : Pos (μₒ ρ ι))
      → Shp X (μ X c κ) p ↦ Shp X (κ (μₒ-pos-fst ρ ι p)) (μₒ-pos-snd ρ ι p)
    {-# REWRITE μ-pos-shp #-} 

  --
  --  Definition of the Derived Monad 
  --

  module _ {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : {o : 𝒪 n} (f : Frm Xₙ o) → Set ℓ) where
  
    η-dec : {o : 𝒪 n} (f : Frm Xₙ o) (x : Xₛₙ f)
      → (p : Pos (ηₒ o)) → Xₛₙ (Shp Xₙ (η Xₙ f) p)
    η-dec {o} f x = ηₒ-pos-elim o (λ p → Xₛₙ (Shp Xₙ (η Xₙ f) p)) x 

    μ-dec : {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm Xₙ o} (c : Cns Xₙ f ρ)
      → (ι : (p : Pos ρ) → 𝒫 (Typ ρ p))
      → (δ : (p : Pos ρ) → Cns Xₙ (Shp Xₙ c p) (ι p))
      → (ν : (p : Pos ρ) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
      → (p : Pos (μₒ ρ ι)) → Xₛₙ (Shp Xₙ (μ Xₙ c δ) p)
    μ-dec {ρ = ρ} c ι δ ν p = ν (μₒ-pos-fst ρ ι p) (μₒ-pos-snd ρ ι p)

    {-# NO_POSITIVITY_CHECK #-}
    record WebFrm (o : 𝒪 n) (ρ : 𝒫 o) : Set ℓ where
      inductive
      eta-equality
      constructor ⟪_,_,_,_⟫ 
      field
        frm : Frm Xₙ o
        cns : Cns Xₙ frm ρ
        tgt : Xₛₙ frm
        src : (p : Pos ρ) → Xₛₙ (Shp Xₙ cns p)

    open WebFrm public
    
    data Web : {o : 𝒪 n} {ρ : 𝒫 o} → WebFrm o ρ → 𝒯r o ρ → Set ℓ where

      lf : {o : 𝒪 n} {f : Frm Xₙ o} (x : Xₛₙ f)
        → Web ⟪ f , η Xₙ f , x , η-dec f x ⟫ (lf o) 

      nd : {o : 𝒪 n} {ρ : 𝒫 o} (φ : WebFrm o ρ)
        → (ι : (p : Pos ρ) → 𝒫 (Typ ρ p))
        → (κ : (p : Pos ρ) → 𝒯r (Typ ρ p) (ι p))
        → (δ : (p : Pos ρ) → Cns Xₙ (Shp Xₙ (cns φ) p) (ι p))
        → (ν : (p : Pos ρ) (q : Pos (ι p)) → Xₛₙ (Shp Xₙ (δ p) q))
        → (ε : (p : Pos ρ) → Web ⟪ Shp Xₙ (cns φ) p , δ p , src φ p , ν p ⟫ (κ p)) 
        → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) ι δ ν ⟫ (nd o ρ ι κ) 

  𝕆 ℓ O = ⊤ 
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ Xₙ → {o : 𝒪 n} → Frm Xₙ o → Set ℓ)
  
  Frm {n = O} X tt = ⊤
  Frm {n = S n} (Xₙ , Xₛₙ) (o , ρ) = WebFrm Xₙ Xₛₙ o ρ 

  Cns {n = O} _ _ _ = ⊤ 
  Cns {n = S n} (Xₙ , Xₛₙ) {o , ρ} = Web Xₙ Xₛₙ {o} {ρ} 
  
  Shp {n = O} _ _ _ = tt
  Shp {n = S n} X {o , ρ} c p = {!!}




