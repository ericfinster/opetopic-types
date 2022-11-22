open import Core.Prelude
open import Native.InductiveOpetopes

module Native.InductiveOpetopicType where

  --
  --  Signature 
  --
  
  data 𝕆Type (ℓ : Level) : (n : ℕ) → Type (ℓ-suc ℓ)

  data Frm {ℓ} : {n : ℕ} (X : 𝕆Type ℓ n)
    → 𝕆 n → Type 

  data Web {ℓ} : {n : ℕ} (X : 𝕆Type ℓ n)
    → {ο : 𝕆 n} (f : Frm X ο)
    → (ρ : ℙ ο) → Type 

  Shp : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (s : Web X f ρ)
    → (p : Pos ρ) → Frm X (Typ ρ p)

  --
  --  Monadic Structure
  --

  η : ∀ {ℓ n} (X : 𝕆Type ℓ n) 
    → {ο : 𝕆 n} (f : Frm X ο)
    → Web X f (ηₒ ο) 

  μ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (s : Web X f ρ)
    → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
    → (ϵ : (p : Pos ρ) → Web X (Shp X s p) (δ p))
    → Web X f (μₒ ρ δ)

  --
  --  Equations
  --

  postulate

    Shp-η : ∀ {ℓ n} (X : 𝕆Type ℓ n) 
      → {ο : 𝕆 n} (f : Frm X ο)
      → (p : Pos (ηₒ ο))
      → Shp X (η X f) p ↦ f 
    {-# REWRITE Shp-η #-}      
    
    Shp-μ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → {ο : 𝕆 n} (f : Frm X ο)
      → {ρ : ℙ ο} (s : Web X f ρ)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → (ϵ : (p : Pos ρ) → Web X (Shp X s p) (δ p))
      → (p : Pos (μₒ ρ δ))
      → Shp X (μ X s ϵ) p ↦ Shp X (ϵ (fstₒ ρ δ p)) (sndₒ ρ δ p)
    {-# REWRITE Shp-μ #-} 

    --
    --  Monadic Laws
    --
    
    μ-unit-r : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (s : Web X f ρ)
      → μ X s (λ p → η X (Shp X s p)) ↦ s 
    {-# REWRITE μ-unit-r #-}
    
    μ-unit-l : ∀ {ℓ n} (X : 𝕆Type ℓ n) 
      → {ο : 𝕆 n} (f : Frm X ο)
      → {δ : (p : Pos (ηₒ ο)) → ℙ ο}
      → (ϵ : (p : Pos (ηₒ ο)) → Web X (Shp X (η X f) p) (δ p))
      → μ X (η X f) ϵ ↦ ϵ (η-posₒ ο) 
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (s : Web X f ρ)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → (ϵ : (p : Pos ρ) → Web X (Shp X s p) (δ p))
      → {δ' : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p)}
      → (ϵ' : (p : Pos (μₒ ρ δ)) → Web X (Shp X (μ X s ϵ) p) (δ' p))
      → μ X (μ X s ϵ) ϵ' ↦ μ X s (λ p → μ X (ϵ p) (λ q → ϵ' (pairₒ ρ δ p q)))
    {-# REWRITE μ-assoc #-}

  --
  --  Decorated versions
  --

  Idx : ∀ {ℓ n} → 𝕆Type ℓ n → Type 
  Idx {n = n} X = Σ[ ο ∈ 𝕆 n ] Frm X ο 

  Src : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → (i : Idx X) → Type ℓ
  Src X P (ο , f) =
    Σ[ ρ ∈ ℙ ο ] 
    Σ[ ω ∈ Web X f ρ ]
    ((p : Pos ρ) → P (Typ ρ p , Shp X ω p))

  ret : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → P i → Src X P i
  ret {n = n} X P {ο , f} x =
    _ , η X f , cst x 
    
  join : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → Src X (Src X P) i → Src X P i
  join X P (ρ , ω , δ)  =
    _ , μ X ω (λ p → δ p .snd .fst) ,
    λ pq → let p = fstₒ ρ (λ p → δ p .fst) pq
               q = sndₒ ρ (λ p → δ p .fst) pq
           in δ p .snd .snd q
           
  --
  --  Implementation
  --

  {-# NO_UNIVERSE_CHECK #-}
  {-# NO_POSITIVITY_CHECK #-}
  data 𝕆Type ℓ where
  
    ○ : 𝕆Type ℓ 0
    
    _∥_ : {n : ℕ} (X : 𝕆Type ℓ n)
      → (P : Idx X → Type ℓ)
      → 𝕆Type ℓ (suc n)

  {-# NO_UNIVERSE_CHECK #-}
  data Frm {ℓ} where

    ● : Frm ○ objₒ

    _►⟦_∣_⟧ : {n : ℕ} {X : 𝕆Type ℓ n}
      → {P : Idx X → Type ℓ}
      → {ο : 𝕆 n} (f : Frm X ο)
      → (t : P (ο , f))
      → (s : Src X P (ο , f))
      → Frm (X ∥ P) (ο ∣ s .fst) 

  Branch : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} (tgt : P i)
    → Type ℓ
  Branch X P {ο , f} t =     
    Σ[ s ∈ Src X P (ο , f) ]
    Σ[ tr ∈ ℙ (ο ∣ s .fst) ]
    Web (X ∥ P) (f ►⟦ t ∣ s ⟧) tr 

  {-# NO_UNIVERSE_CHECK #-}
  data Web {ℓ} where

    arr : Web ○ ● arrₒ

    lf : {n : ℕ} {X : 𝕆Type ℓ n}
       → {P : Idx X → Type ℓ}
       → {ο : 𝕆 n} {f : Frm X ο} (t : P (ο , f))
       → Web (X ∥ P) (f ►⟦ t ∣ ret X P t ⟧) (lfₒ ο) 

    nd : {n : ℕ} {X : 𝕆Type ℓ n}
       → {P : Idx X → Type ℓ}
       → {ο : 𝕆 n} {f : Frm X ο} (t : P (ο , f)) (s : Src X P (ο , f))
       → (δ : (p : Pos (s .fst)) → Branch X P (s .snd .snd p))
       → Web (X ∥ P) (f ►⟦ t ∣ join X P (s .fst , s .snd .fst , λ p → δ p .fst) ⟧)
                     (ndₒ (s .fst) (λ p → _ , δ p .snd .fst )) 

  Shp ○ arr this = ●
  Shp (X ∥ P) (nd t s δ) here = _ ►⟦ t ∣ s ⟧
  Shp (X ∥ P) (nd t s δ) (there p q) = Shp (X ∥ P) (δ p .snd .snd) q

  η ○ ● = arr
  η (X ∥ P) (f ►⟦ t ∣ s ⟧) = 
    nd t s (λ p → _ , _ , lf (s .snd .snd p))

  γ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {ο : 𝕆 n} {f : Frm X ο} {t : P (ο , f)} {s : Src X P (ο , f)}
    → {τ : ℙ (ο ∣ s .fst)}
    → (ω : Web (X ∥ P) (f ►⟦ t ∣ s ⟧) τ)
    → (ϕ : (p : Pos (s .fst)) → Branch X P (s .snd .snd p))
    → Web (X ∥ P) (f ►⟦ t ∣ join X P (s .fst , s .snd .fst , λ p → ϕ p .fst) ⟧)
        (γₒ τ (λ p → _ , ϕ p .snd .fst ))
  γ X P (lf t) ϕ = ϕ (η-posₒ _) .snd .snd 
  γ X P (nd t s δ) ϕ = 
    nd t s (λ p → _ , _ , γ X P (δ p .snd .snd) (λ q → ϕ (pairₒ (s . fst) (λ r → δ r .fst .fst) p q)))

  μ ○ arr ϕ = arr
  μ (X ∥ P) (lf tgt) ϕ = lf tgt
  μ (X ∥ P) (nd tgt src δ) ϕ = 
    γ X P (ϕ here) (λ p → _ , _ , μ (X ∥ P) (δ p .snd .snd) (λ q → ϕ (there p q)))

