open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType

module Native.DependentOpetopicType where

  --
  --  Signature 
  --
  
  data 𝕆Type↓ {ℓ} (ℓ↓ : Level)
    : {n : ℕ} → 𝕆Type ℓ n → Type (ℓ-suc ℓ↓)

  data Frm↓ {ℓ ℓ↓} : {n : ℕ} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} (f : Frm X ο) → Type ℓ↓

  data Web↓ {ℓ ℓ↓} : {n : ℕ} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {ρ : ℙ ο} 
    → {f : Frm X ο} (ω : Web X f ρ) 
    → (f↓ : Frm↓ X↓ f) → Type ℓ↓
    
  Shp↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {ρ : ℙ ο} 
    → {f : Frm X ο} {ω : Web X f ρ}
    → {f↓ : Frm↓ X↓ f} (ω↓ : Web↓ X↓ ω f↓)
    → (p : Pos ρ) → Frm↓ X↓ (Shp X ω p)

  --
  --  Monadic Structure
  --

  η↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
    → Web↓ X↓ (η X f) f↓
    
  μ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {ρ : ℙ ο} {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
    → {f : Frm X ο} {ω : Web X f ρ}
    → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
    → {f↓ : Frm↓ X↓ f} (ω↓ : Web↓ X↓ ω f↓)
    → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (ϵ p) (Shp↓ X↓ ω↓ p))
    → Web↓ X↓ (μ X ω ϵ) f↓

  --
  --  Equations 
  --

  postulate

    Shp↓-η↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {f : Frm X ο} 
      → (f↓ : Frm↓ X↓ f) (p : Pos (ηₒ ο))
      → Shp↓ X↓ (η↓ X↓ f↓) p ↦ f↓
    {-# REWRITE Shp↓-η↓ #-}
    
    Shp↓-μ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {ρ : ℙ ο} {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {f : Frm X ο} {ω : Web X f ρ}
      → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
      → {f↓ : Frm↓ X↓ f} (ω↓ : Web↓ X↓ ω f↓)
      → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (ϵ p) (Shp↓ X↓ ω↓ p))
      → (p : Pos (μₒ ρ δ))
      → Shp↓ X↓ (μ↓ X↓ ω↓ ϵ↓) p ↦ Shp↓ X↓ (ϵ↓ (fstₒ ρ δ p)) (sndₒ ρ δ p) 
    {-# REWRITE Shp↓-μ↓ #-} 

    --
    --  Monadic Laws
    --
    
    μ↓-unit-r : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {ρ : ℙ ο} 
      → {f : Frm X ο} {ω : Web X f ρ}
      → (f↓ : Frm↓ X↓ f) (ω↓ : Web↓ X↓ ω f↓)
      → μ↓ X↓ ω↓ (λ p → η↓ X↓ (Shp↓ X↓ ω↓ p)) ↦ ω↓
    {-# REWRITE μ↓-unit-r #-}
    
    μ↓-unit-l : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {δ : (p : Pos (ηₒ ο)) → ℙ ο}
      → {f : Frm X ο} {ϵ : (p : Pos (ηₒ ο)) → Web X (Shp X (η X f) p) (δ p)}
      → (f↓ : Frm↓ X↓ f) (ϵ↓ : (p : Pos (ηₒ ο)) → Web↓ X↓ (ϵ p) (Shp↓ X↓ (η↓ X↓ f↓) p))
      → μ↓ X↓ (η↓ X↓ f↓) ϵ↓ ↦ ϵ↓ (η-posₒ ο) 
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {ρ : ℙ ο} {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϕ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p)}
      → {f : Frm X ο} {ω : Web X f ρ} 
      → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
      → {ψ : (p : Pos (μₒ ρ δ)) → Web X (Shp X (μ X ω ϵ) p) (ϕ p)}
      → (f↓ : Frm↓ X↓ f) (ω↓ : Web↓ X↓ ω f↓)
      → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (ϵ p) (Shp↓ X↓ ω↓ p))
      → (ψ↓ : (p : Pos (μₒ ρ δ)) → Web↓ X↓ (ψ p) (Shp↓ X↓ (μ↓ X↓ ω↓ ϵ↓) p))
      → μ↓ X↓ (μ↓ X↓ ω↓ ϵ↓) ψ↓ ↦ μ↓ X↓ ω↓ (λ p → μ↓ X↓ (ϵ↓ p) (λ q → ψ↓ (pairₒ ρ δ p q)))
    {-# REWRITE μ↓-assoc #-}

  --
  --  Decorated versions
  --

  Idx↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → Idx X → Type ℓ↓
  Idx↓ {n = n} {X} X↓ (_ , f) = Frm↓ X↓ f

  Src↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {i : Idx X} → Src X P i → Idx↓ X↓ i → Type ℓ↓
  Src↓ X↓ P↓ {ο , f} (ρ , ω , δ) f↓  =
    Σ[ ω↓ ∈ Web↓ X↓ ω f↓ ]
    ((p : Pos ρ) → P↓ (δ p) (Shp↓ X↓ ω↓ p))

  ret↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {i : Idx X} {t : P i} {i↓ : Idx↓ X↓ i}
    → P↓ t i↓ → Src↓ X↓ P↓ (ret X P t) i↓
  ret↓ X↓ P↓ {ο , f} {t} {f↓} t↓ = η↓ X↓ f↓ , cst t↓ 

  join↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {i : Idx X} {s : Src X (Src X P) i}
    → {i↓ : Idx↓ X↓ i} (s↓ : Src↓ X↓ (Src↓ X↓ P↓) s i↓)
    → Src↓ X↓ P↓ (join X P s) i↓ 
  join↓ X↓ P↓ {s = ρ , ω , δ} (ω↓ , δ↓) =
    μ↓ X↓ ω↓ (λ p → δ↓ p .fst) ,
    (λ pq → let p = fstₒ ρ (λ p → δ p .fst) pq
                q = sndₒ ρ (λ p → δ p .fst) pq
             in δ↓ p .snd q)
             
  --
  --  Implementations
  --
  
  {-# NO_UNIVERSE_CHECK #-}
  {-# NO_POSITIVITY_CHECK #-}
  data 𝕆Type↓ {ℓ} ℓ↓ where

    ○↓ : 𝕆Type↓ ℓ↓ ○
    
    _∥↓_ : {n : ℕ} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {P : Idx X → Type ℓ}
      → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
      → 𝕆Type↓ ℓ↓ (X ∥ P)


  {-# NO_UNIVERSE_CHECK #-}
  data Frm↓ {ℓ} {ℓ↓} where

    ●↓ : Frm↓ ○↓ ●

    _►⟦_∣_⟧↓ : {n : ℕ} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
      → {P : Idx X → Type ℓ}
      → {P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓}
      → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)} {s : Src X P (ο , f)}
      → (f↓ : Frm↓ X↓ f) (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ s f↓)
      → Frm↓ (X↓ ∥↓ P↓) (f ►⟦ t ∣ s ⟧)

  Branch↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)}
    → (b : Branch X P t)
    → {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
    → Type ℓ↓
  Branch↓ X↓ P↓ {ο} {f} {t} (s , tr , ω) {f↓} t↓ =
    Σ[ s↓ ∈ Src↓ X↓ P↓ s f↓ ]
    Web↓ (X↓ ∥↓ P↓) ω (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) 

  {-# NO_UNIVERSE_CHECK #-}
  data Web↓ {ℓ} {ℓ↓} where 

    arr↓ : Web↓ ○↓ arr ●↓

    lf↓ : {n : ℕ} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
       → {P : Idx X → Type ℓ}
       → {P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓}
       → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)}
       → {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓)
       → Web↓ (X↓ ∥↓ P↓) (lf t) (f↓ ►⟦ t↓ ∣ ret↓ X↓ P↓ t↓ ⟧↓)

    nd↓ : {n : ℕ} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
       → {P : Idx X → Type ℓ}
       → {P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓}
       → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)} {s : Src X P (ο , f)}
       → {δ : (p : Pos (s .fst)) → Branch X P (s .snd .snd p)}
       → {f↓ : Frm↓ X↓ f} (t↓ : P↓ t f↓) (s↓ : Src↓ X↓ P↓ s f↓)
       → (δ↓ : (p : Pos (s .fst)) -> Branch↓ X↓ P↓ (δ p) (s↓ .snd p))
       → Web↓ (X↓ ∥↓ P↓) (nd t s δ) (f↓ ►⟦ t↓ ∣ join↓ X↓ P↓ (s↓ .fst , λ p → δ↓ p .fst) ⟧↓)  

  Shp↓ ○↓ arr↓ this = ●↓
  Shp↓ (X↓ ∥↓ P↓) (nd↓ t↓ s↓ δ↓) here = _ ►⟦ t↓ ∣ s↓ ⟧↓
  Shp↓ (X↓ ∥↓ P↓) (nd↓ t↓ s↓ δ↓) (there p q) = Shp↓ (X↓ ∥↓ P↓) (δ↓ p .snd) q
  
  η↓ ○↓ ●↓ = arr↓ 
  η↓ (X↓ ∥↓ P↓) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) =
    nd↓ t↓ s↓ (λ p → _ , lf↓ (s↓ .snd p))

  γ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {P : Idx X → Type ℓ}
    → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
    → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)} {s : Src X P (ο , f)}
    → {τ : ℙ (ο ∣ s .fst)} {ω : Web (X ∥ P) (f ►⟦ t ∣ s ⟧) τ}
    → {ϕ : (p : Pos (s .fst)) → Branch X P (s .snd .snd p)}
    → {f↓ : Frm↓ X↓ f} {t↓ : P↓ t f↓} {s↓ : Src↓ X↓ P↓ s f↓}
    → (ω↓ : Web↓ (X↓ ∥↓ P↓) ω (f↓ ►⟦ t↓ ∣ s↓ ⟧↓))
    → (ϕ↓ : (p : Pos (s .fst)) -> Branch↓ X↓ P↓ (ϕ p) (s↓ .snd p))
    → Web↓ (X↓ ∥↓ P↓) (γ X P ω ϕ) (f↓ ►⟦ t↓ ∣ join↓ X↓ P↓ (s↓ .fst , λ p → ϕ↓ p .fst) ⟧↓)
  γ↓ X↓ P↓ (lf↓ t↓) ϕ↓ = ϕ↓ (η-posₒ _) .snd
  γ↓ X↓ P↓ {ω = nd t s δ} (nd↓ t↓ s↓ δ↓) ϕ↓ = 
    nd↓ t↓ s↓ (λ p → _ , γ↓ X↓ P↓ (δ↓ p .snd) (λ q → ϕ↓ (pairₒ (s .fst) (λ r → δ r .fst .fst) p q)))

  μ↓ ○↓ arr↓ ϕ = arr↓
  μ↓ (X↓ ∥↓ P↓) (lf↓ t↓) ϕ = lf↓ t↓
  μ↓ (X↓ ∥↓ P↓) (nd↓ t↓ s↓ δ↓) ϕ↓ = 
    γ↓ X↓ P↓ (ϕ↓ here) (λ p → _ , μ↓ (X↓ ∥↓ P↓) (δ↓ p .snd) (λ q → ϕ↓ (there p q)))
