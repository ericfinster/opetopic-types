{-# OPTIONS --opetopic-types --verbose=tc.primitive.optypes:10 #-}

open import Native.Opetopes

module Native.Test where

  --
  --  Testing
  --

  data _≡_ {i} {A : Type i} (a : A) : A → Type i where
    refl : a ≡ a

  {-# BUILTIN EQUALITY _≡_ #-}

  𝕆Type-zero : (ℓ : Level)
    → 𝕆Type zero ℓ ≡ ● 
  𝕆Type-zero ℓ = refl 

  𝕆Type-suc : (n : ℕ) (ℓ : Level)
    → 𝕆Type (suc n) ℓ ≡ (Σ[ X ∈ 𝕆Type n ℓ ] (Frm X → Type ℓ))
  𝕆Type-suc n ℓ = refl

  Frm-zero : (ℓ : Level) (X : 𝕆Type zero ℓ) → Frm {zero} X ≡ ●
  Frm-zero ℓ X = refl
  
  Frm-suc : (n : ℕ) (ℓ : Level) (X : 𝕆Type (suc n) ℓ)
    → Frm {suc n} X ≡ (Σ[ f ∈ Frm {n} (fst X) ]
                       Σ[ s ∈ Src {n} (fst X) (snd X) f ]
                       (snd X) f)
  Frm-suc n ℓ X = refl 

  ⇒-zero : (ℓ : Level) (X Y : 𝕆Type zero ℓ)
    → _⇒_ {zero} X Y ≡ ●
  ⇒-zero ℓ X Y = refl 

  ⇒-suc : (n : ℕ) (ℓ : Level) (X Y : 𝕆Type (suc n) ℓ)
    → _⇒_ {suc n} X Y ≡ (Σ[ σ ∈ (fst X) ⇒(fst Y) ]
                         ({f : Frm (fst X)} → (snd X) f → (snd Y) (Frm⇒ σ f)))
  ⇒-suc n ℓ X Y = refl 

  id-map-zero : ∀ {ℓ} (X : 𝕆Type zero ℓ)
    → id-map {zero} X ≡ ∙
  id-map-zero X = refl 

  id-map-suc : ∀ {n ℓ} → (X : 𝕆Type (suc n) ℓ)
    → id-map {suc n} X ≡ (id-map {n} (fst X) , λ {f} p → p)
  id-map-suc X = refl 

  map-comp-zero : ∀ {ℓ} (X Y Z : 𝕆Type zero ℓ) (σ : _⇒_ {zero} X Y) (τ : _⇒_ {zero} Y Z)
    → _⊙_ {zero} τ σ ≡ ∙  
  map-comp-zero X Y Z σ τ = refl 

  map-comp-suc : ∀ {n ℓ} (X Y Z : 𝕆Type (suc n) ℓ) (σ : _⇒_ {suc n} X Y) (τ : _⇒_ {suc n} Y Z)
    → _⊙_ {suc n} {X = X} {Y} {Z} τ σ ≡ (fst τ ⊙ fst σ , λ {f} p → snd τ (snd σ p))
  map-comp-suc X Y Z σ τ = refl

  map-comp-unit-right : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (σ ⊙ id-map X) ≡ σ
  map-comp-unit-right σ = refl

  map-comp-unit-left : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (id-map Y ⊙ σ) ≡ σ
  map-comp-unit-left σ = {!refl!} 

  Frm⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
    → Frm⇒ (id-map X) f ≡ f
  Frm⇒-id X f = refl 

  Frm⇒-⊙ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
    → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
    → Frm⇒ (τ ⊙ σ) f ≡ Frm⇒ τ (Frm⇒ σ f)
  Frm⇒-⊙ σ τ f = refl 



