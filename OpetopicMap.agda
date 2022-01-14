{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import OpetopicType

module OpetopicMap where

  _⇒_ : ∀ {ℓ₀ ℓ₁ n} → 𝕆 ℓ₀ n → 𝕆 ℓ₁ n
    → Set (ℓ-max ℓ₀ ℓ₁)

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
    → (X ⇒ Y) → Frm X → Frm Y
    
  Cns⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
    → (α : X ⇒ Y) {f : Frm X}
    → Cns X f → Cns Y (Frm⇒ α f)
    
  Pos⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
    → (α : X ⇒ Y) {f : Frm X} (c : Cns X f)
    → Pos X c → Pos Y (Cns⇒ α c)

  Pos⇐ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
    → (α : X ⇒ Y) {f : Frm X} (c : Cns X f)
    → Pos Y (Cns⇒ α c) → Pos X c 


  Dec⇒ : ∀ {ℓ₀ ℓ₁ n} {Xₙ : 𝕆 ℓ₀ n} {Yₙ : 𝕆 ℓ₁ n}
    → (Xₛₙ : Frm Xₙ → Set ℓ₀) (Yₛₙ : Frm Yₙ → Set ℓ₁)
    → (αₙ : Xₙ ⇒ Yₙ) (αₛₙ : {f : Frm Xₙ} → Xₛₙ f → Yₛₙ (Frm⇒ αₙ f))
    → {f : Frm Xₙ} (c : Cns Xₙ f) (ν : (p : Pos Xₙ c) → Xₛₙ (Typ Xₙ c p))
    → (p : Pos Yₙ (Cns⇒ αₙ c)) → Yₛₙ (Typ Yₙ (Cns⇒ αₙ c) p)

  postulate

    η⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
      → (α : X ⇒ Y) (f : Frm X)
      → Cns⇒ α (η X f) ↦ η Y (Frm⇒ α f)
    {-# REWRITE η⇒ #-} 

    η-pos⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
      → (α : X ⇒ Y) (f : Frm X)
      → Pos⇒ α (η X f) (η-pos X f) ↦ η-pos Y (Frm⇒ α f)
    {-# REWRITE η-pos⇒ #-} 

    -- This one is backwards from the others in terms of direction ..
    η-pos-elim⇒ : ∀ {ℓ₀ ℓ₁ ℓ' n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
      → (α : X ⇒ Y) (f : Frm X)
      → (P : (p : Pos Y (η Y (Frm⇒ α f))) → Set ℓ')
      → (η-pos* : P (η-pos Y (Frm⇒ α f)))
      → (p : Pos X (η X f))
      → η-pos-elim Y (Frm⇒ α f) P η-pos* (Pos⇒ α (η X f) p)
        ↦ η-pos-elim X f (λ p → P (Pos⇒ α (η X f) p)) η-pos* p
    {-# REWRITE η-pos-elim⇒ #-} 

    Typ-Frm⇒ :  ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
      → (α : X ⇒ Y) {f : Frm X} (c : Cns X f) (p : Pos X c)
      → Frm⇒ α (Typ X c p) ↦ Typ Y (Cns⇒ α c) (Pos⇒ α c p)
    {-# REWRITE Typ-Frm⇒ #-} 

    Pos-inv-l : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n}
      → (α : X ⇒ Y) {f : Frm X} (c : Cns X f)
      → (p : Pos Y (Cns⇒ α c))
      → Pos⇒ α c (Pos⇐ α c p) ↦ p
    {-# REWRITE Pos-inv-l #-}

    -- η-dec : (f : Frm Xₙ) (x : Xₛₙ f)
    --   → (p : Pos Xₙ (η Xₙ f)) → Xₛₙ (Typ Xₙ (η Xₙ f) p)
    -- η-dec f = η-pos-elim Xₙ f (λ p → Xₛₙ (Typ Xₙ (η Xₙ f) p)) 

  module _ {ℓ₀ ℓ₁ n} {Xₙ : 𝕆 ℓ₀ n} {Yₙ : 𝕆 ℓ₁ n}
           (Xₛₙ : Frm Xₙ → Set ℓ₀) (Yₛₙ : Frm Yₙ → Set ℓ₁)
           (αₙ : Xₙ ⇒ Yₙ) (αₛₙ : {f : Frm Xₙ} → Xₛₙ f → Yₛₙ (Frm⇒ αₙ f)) where

    WebFrm⇒ : WebFrm Xₙ Xₛₙ → WebFrm Yₙ Yₛₙ
    WebFrm⇒ φ = ⟪ Frm⇒ αₙ (frm φ) , Cns⇒ αₙ (cns φ) , αₛₙ (tgt φ) , (λ p → αₛₙ (src φ (Pos⇐ αₙ (cns φ) p))) ⟫ 

    -- Hmmm.  So we'll need to do a bit better to make this compute...
    -- test : {f : Frm Xₙ} (x : Xₛₙ f) →  Dec⇒ Xₛₙ Yₛₙ αₙ αₛₙ (η Xₙ f) (η-dec Xₙ Xₛₙ f x) ≡ (η-dec Yₙ Yₛₙ (Frm⇒ αₙ f) (αₛₙ x))
    -- test x = {!refl!} 

    Web⇒ : {φ : WebFrm Xₙ Xₛₙ} → Web Xₙ Xₛₙ φ → Web Yₙ Yₛₙ (WebFrm⇒ φ)
    Web⇒ (lf {f} x) = {!lf {Xₛₙ = Yₛₙ} {f = Frm⇒ αₙ f} (αₛₙ x)!}
    Web⇒ (nd φ δ ν ε) = {!!}

    -- data Web : WebFrm → Set ℓ where

    --   lf : {f : Frm Xₙ} (x : Xₛₙ f)
    --     → Web ⟪ f , η Xₙ f , x , η-dec f x ⟫ 

    --   nd : (φ : WebFrm)
    --     → (δ : (p : Pos Xₙ (cns φ)) → Cns Xₙ (Typ Xₙ (cns φ) p))
    --     → (ν : (p : Pos Xₙ (cns φ)) (q : Pos Xₙ (δ p)) → Xₛₙ (Typ Xₙ (δ p) q))
    --     → (ε : (p : Pos Xₙ (cns φ)) → Web ⟪ Typ Xₙ (cns φ) p , δ p , src φ p , ν p ⟫)
    --     → Web ⟪ frm φ , μ Xₙ (cns φ) δ , tgt φ , μ-dec (cns φ) δ ν ⟫ 

  _⇒_ {n = O} _ _ = ⊤
  _⇒_ {n = S n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Σ (Xₙ ⇒ Yₙ) (λ α → {f : Frm Xₙ} → Xₛₙ f → Yₛₙ (Frm⇒ α f))

  Frm⇒ {n = O} α _ = tt
  Frm⇒ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) φ =
    ⟪ Frm⇒ αₙ (frm φ) , Cns⇒ αₙ (cns φ) , αₛₙ (tgt φ) ,
      Dec⇒ Xₛₙ Yₛₙ αₙ αₛₙ (cns φ) (src φ) ⟫
  
  Cns⇒ {n = O} _ _ = tt
  Cns⇒ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) c = {!!}
  
  Pos⇒ α c p = {!!} 
  Pos⇐ α c p = {!!} 

  Dec⇒ = {!!} 
