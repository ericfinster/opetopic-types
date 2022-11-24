open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType

module Native.Universe where

  --
  --  Signature 
  --

  𝕌 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n 

  data Frm↓ {ℓ} : {n : ℕ}
    → {ο : 𝕆 n} (f : Frm (𝕌 ℓ n) ο) → Type ℓ

  data Web↓ {ℓ} : {n : ℕ}
    → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} 
    → {ρ : ℙ ο} (ω : Web (𝕌 ℓ n) f ρ)
    → (f↓ : Frm↓ f) → Type ℓ 

  Shp↓ : ∀ {ℓ n} 
    → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} 
    → {ρ : ℙ ο} {ω : Web (𝕌 ℓ n) f ρ}
    → {f↓ : Frm↓ f} (ω↓ : Web↓ ω f↓)
    → (p : Pos ρ) → Frm↓ (Shp (𝕌 ℓ n) ω p)

  --
  --  Monadic Structure
  --

  postulate
  
    η↓ : ∀ {ℓ n} 
      → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο}
      → (f↓ : Frm↓ f) → Web↓ (η (𝕌 ℓ n) f) f↓ 

    μ↓ : ∀ {ℓ n} 
      → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} 
      → {ρ : ℙ ο} {ω : Web (𝕌 ℓ n) f ρ}
      → {f↓ : Frm↓ f} (ω↓ : Web↓ ω f↓)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϵ : (p : Pos ρ) → Web (𝕌 ℓ n) (Shp (𝕌 ℓ n) ω p) (δ p)}
      → (ϵ↓ : (p : Pos ρ) → Web↓  (ϵ p) (Shp↓ ω↓ p))
      → Web↓ (μ (𝕌 ℓ n) ω ϵ) f↓

  --
  --  Equations 
  --

  postulate

    Shp↓-η↓ : ∀ {ℓ n} 
      → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} 
      → (f↓ : Frm↓ f) (p : Pos (ηₒ ο))
      → Shp↓ (η↓ f↓) p ↦ f↓
    {-# REWRITE Shp↓-η↓ #-}

    Shp↓-μ↓ : ∀ {ℓ n} 
      → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} 
      → {ρ : ℙ ο} {ω : Web (𝕌 ℓ n) f ρ}
      → {f↓ : Frm↓ f} (ω↓ : Web↓ ω f↓)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϵ : (p : Pos ρ) → Web (𝕌 ℓ n) (Shp (𝕌 ℓ n) ω p) (δ p)}
      → (ϵ↓ : (p : Pos ρ) → Web↓  (ϵ p) (Shp↓ ω↓ p))
      → (p : Pos (μₒ ρ δ))
      → Shp↓ (μ↓ ω↓ ϵ↓) p ↦ Shp↓ (ϵ↓ (fstₒ ρ δ p)) (sndₒ ρ δ p) 
    {-# REWRITE Shp↓-μ↓ #-} 

    --
    --  Monadic Laws
    --
    
    μ↓-unit-r : ∀ {ℓ n} 
      → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} 
      → {ρ : ℙ ο} {ω : Web (𝕌 ℓ n) f ρ}
      → (f↓ : Frm↓ f) (ω↓ : Web↓ ω f↓)
      → μ↓ ω↓ (λ p → η↓ (Shp↓ ω↓ p)) ↦ ω↓
    {-# REWRITE μ↓-unit-r #-}
    
    μ↓-unit-l : ∀ {ℓ  n}
      → {ο : 𝕆 n} {δ : (p : Pos (ηₒ ο)) → ℙ ο}
      → {f : Frm (𝕌 ℓ n) ο}
      → {ϵ : (p : Pos (ηₒ ο)) → Web (𝕌 ℓ n) (Shp (𝕌 ℓ n) (η (𝕌 ℓ n) f) p) (δ p)}
      → (f↓ : Frm↓ f)
      → (ϵ↓ : (p : Pos (ηₒ ο)) → Web↓ (ϵ p) (Shp↓ (η↓ f↓) p))
      → μ↓ (η↓ f↓) ϵ↓ ↦ ϵ↓ (η-posₒ ο) 
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ n} 
      → {ο : 𝕆 n} {ρ : ℙ ο} {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {f : Frm (𝕌 ℓ n) ο} {ω : Web (𝕌 ℓ n) f ρ}
      → {ϵ : (p : Pos ρ) → Web (𝕌 ℓ n) (Shp (𝕌 ℓ n) ω p) (δ p)}
      → {ϕ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p)}
      → {ψ : (p : Pos (μₒ ρ δ)) → Web (𝕌 ℓ n) (Shp (𝕌 ℓ n) (μ (𝕌 ℓ n) ω ϵ) p) (ϕ p)}
      → (f↓ : Frm↓ f) (ω↓ : Web↓ ω f↓)
      → (ϵ↓ : (p : Pos ρ) → Web↓ (ϵ p) (Shp↓ ω↓ p))
      → (ψ↓ : (p : Pos (μₒ ρ δ)) → Web↓ (ψ p) (Shp↓ (μ↓ ω↓ ϵ↓) p))
      → μ↓ (μ↓ ω↓ ϵ↓) ψ↓ ↦ μ↓ ω↓ (λ p → μ↓ (ϵ↓ p) (λ q → ψ↓ (pairₒ ρ δ p q)))
    {-# REWRITE μ↓-assoc #-}

  --
  --  Decorated versions
  --

  Idx↓ : ∀ {ℓ n} → Idx (𝕌 ℓ n) → Type ℓ
  Idx↓ {n = n} (_ , f) = Frm↓ f

  𝕌-cell : ∀ {ℓ n} → Idx (𝕌 ℓ n) → Type (ℓ-suc ℓ)
  𝕌-cell {ℓ} i = (i↓ : Idx↓ i) → Type ℓ 

  𝕌-el : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)}
    → 𝕌-cell i → Idx↓ i → Type ℓ
  𝕌-el P i = P i 

  Src↓ : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)}
    → {P : Idx (𝕌 ℓ n) → Type (ℓ-suc ℓ)}
    → (Q : {i : Idx (𝕌 ℓ n)} → P i → Idx↓ i → Type ℓ)
    → Src (𝕌 ℓ n) P i
    → Idx↓ i → Type ℓ
  Src↓ {i = ο , f} Q (ρ , ω , δ) f↓ = 
    Σ[ ω↓ ∈ Web↓ ω f↓  ]
    ((p : Pos ρ) → Q (δ p) (Shp↓ ω↓ p))
    
  ret↓ : ∀ {ℓ n} 
    → {P : Idx (𝕌 ℓ n) → Type (ℓ-suc ℓ)}
    → (Q : {i : Idx (𝕌 ℓ n)} → P i → Idx↓ i → Type ℓ)
    → {i : Idx (𝕌 ℓ n)} {t : P i}
    → {i↓ : Idx↓ i} (t↓ : Q t i↓)
    → Src↓ Q (ret (𝕌 ℓ n) P t) i↓
  ret↓ Q {i↓ = i↓} t↓ = η↓ i↓ , cst t↓ 

  join↓ : ∀ {ℓ n} 
    → {P : Idx (𝕌 ℓ n) → Type (ℓ-suc ℓ)}
    → (Q : {i : Idx (𝕌 ℓ n)} → P i → Idx↓ i → Type ℓ)
    → {i : Idx (𝕌 ℓ n)} {s : Src (𝕌 ℓ n) (Src (𝕌 ℓ n) P) i}
    → {i↓ : Idx↓ i} (s↓ : Src↓ (Src↓ Q) s i↓) 
    → Src↓ Q (join (𝕌 ℓ n) P s) i↓ 
  join↓ Q {s = ρ , ω , δ} (ω↓ , δ↓) =
    μ↓ ω↓ (λ p → δ↓ p .fst) , 
    (λ pq → let p = fstₒ ρ (λ p → δ p .fst) pq
                q = sndₒ ρ (λ p → δ p .fst) pq
             in δ↓ p .snd q)
             
  --
  --  Implementations
  --

  𝕌 ℓ zero = ○
  𝕌 ℓ (suc n) = 𝕌 ℓ n ∥ 𝕌-cell

  {-# NO_UNIVERSE_CHECK #-}
  {-# NO_POSITIVITY_CHECK #-}
  data Frm↓ {ℓ} where

    ●↓ : Frm↓ ● 

    _►⟦_∣_⟧↓ : {n : ℕ}
      → {ο : 𝕆 n} {F : Frm (𝕌 ℓ n) ο}
      → {T : Idx↓ (ο , F) → Type ℓ}
      → {S : Src (𝕌 ℓ n) 𝕌-cell (ο , F)}
      → (f↓ : Frm↓ F) (t↓ : T f↓)
      → (s↓ : Src↓ 𝕌-el S f↓)
      → Frm↓ (F ►⟦ T ∣ S ⟧)

  Branch↓ : ∀ {ℓ n} 
    → {ο : 𝕆 n} {f : Frm (𝕌 ℓ n) ο} {t : 𝕌-cell (ο , f)}
    → (b : Branch (𝕌 ℓ n) 𝕌-cell t)
    → {f↓ : Frm↓ f} (t↓ : t f↓)
    → Type ℓ
  Branch↓ {ο} {f} {t} (s , tr , ω) {f↓} t↓ =
    Σ[ s↓ ∈ Src↓ 𝕌-el s f↓ ]
    Web↓ ω ((f↓ ►⟦ t↓ ∣ s↓ ⟧↓))

  {-# NO_UNIVERSE_CHECK #-}
  data Web↓ {ℓ} where 

    arr↓ : Web↓ arr ●↓ 

    lf↓ : {n : ℕ}
       → {ο : 𝕆 n} {F : Frm (𝕌 ℓ n) ο} {T : 𝕌-cell (ο , F)}
       → {f↓ : Frm↓ F} (t↓ : T f↓)
       → Web↓ (lf T) (f↓ ►⟦ t↓ ∣ ret↓ 𝕌-el {t = T} t↓ ⟧↓)

    nd↓ : {n : ℕ} 
       → {ο : 𝕆 n} {F : Frm (𝕌 ℓ n) ο} {T : 𝕌-cell (ο , F)}
       → {S : Src (𝕌 ℓ n) 𝕌-cell (ο , F)}
       → {Δ : (p : Pos (S .fst)) → Branch (𝕌 ℓ n) 𝕌-cell (S .snd .snd p)}
       → {f↓ : Frm↓ F} (t↓ : T f↓) (s↓ : Src↓ 𝕌-el S f↓)
       → (δ↓ : (p : Pos (S .fst)) -> Branch↓ (Δ p) (s↓ .snd p))
       → Web↓ (nd T S Δ) (f↓ ►⟦ t↓ ∣ join↓ 𝕌-el {s = (S .fst , S .snd .fst , λ p → Δ p .fst)} (s↓ .fst , λ p → δ↓ p .fst) ⟧↓)
                                                
  Shp↓ arr↓ this = ●↓
  Shp↓ (nd↓ {f↓ = f↓} t↓ s↓ δ↓) here = f↓ ►⟦ t↓ ∣ s↓ ⟧↓
  Shp↓ (nd↓ {f↓ = f↓} t↓ s↓ δ↓) (there p q) = Shp↓ (δ↓ p .snd) q
  
  -- η↓ ○↓ ●↓ = arr↓ 
  -- η↓ (X↓ ∥↓ P↓) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) =
  --   nd↓ t↓ s↓ (λ p → _ , lf↓ (s↓ .snd p))

  -- γ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
  --   → {P : Idx X → Type ℓ}
  --   → (P↓ : {i : Idx X} → P i →  Idx↓ X↓ i → Type ℓ↓)
  --   → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)} {s : Src X P (ο , f)}
  --   → {τ : ℙ (ο ∣ s .fst)} {ω : Web (X ∥ P) (f ►⟦ t ∣ s ⟧) τ}
  --   → {ϕ : (p : Pos (s .fst)) → Branch X P (s .snd .snd p)}
  --   → {f↓ : Frm↓ X↓ f} {t↓ : P↓ t f↓} {s↓ : Src↓ X↓ P↓ s f↓}
  --   → (ω↓ : Web↓ (X↓ ∥↓ P↓) (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) ω)
  --   → (ϕ↓ : (p : Pos (s .fst)) -> Branch↓ X↓ P↓ (ϕ p) (s↓ .snd p))
  --   → Web↓ (X↓ ∥↓ P↓) (f↓ ►⟦ t↓ ∣ join↓ X↓ P↓ (s↓ .fst , λ p → ϕ↓ p .fst) ⟧↓) (γ X P ω ϕ)
  -- γ↓ X↓ P↓ (lf↓ t↓) ϕ↓ = ϕ↓ (η-posₒ _) .snd
  -- γ↓ X↓ P↓ {ω = nd t s δ} (nd↓ t↓ s↓ δ↓) ϕ↓ = 
  --   nd↓ t↓ s↓ (λ p → _ , γ↓ X↓ P↓ (δ↓ p .snd) (λ q → ϕ↓ (pairₒ (s .fst) (λ r → δ r .fst .fst) p q)))

  -- μ↓ ○↓ arr↓ ϕ = arr↓
  -- μ↓ (X↓ ∥↓ P↓) (lf↓ t↓) ϕ = lf↓ t↓
  -- μ↓ (X↓ ∥↓ P↓) (nd↓ t↓ s↓ δ↓) ϕ↓ = 
  --   γ↓ X↓ P↓ (ϕ↓ here) (λ p → _ , μ↓ (X↓ ∥↓ P↓) (δ↓ p .snd) (λ q → ϕ↓ (there p q)))
