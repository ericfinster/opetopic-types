open import Core.Prelude
open import Native.NewOpetopes

module Native.NewOpetopicType where

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

  record Src {ℓ n} (X : 𝕆Type ℓ n)
    (P : Idx X → Type ℓ)
    (i : Idx X) : Type ℓ where
    inductive 
    eta-equality
    constructor ⟪_,_⟫ 
    field

      {pd} : ℙ (fst i)
      web : Web X (snd i) pd
      dec : (p : Pos pd) → P (Typ pd p , Shp X web p)

  open Src public

  ret : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → P i → Src X P i
  ret {n = n} X P {ο , f} x =
    ⟪ η X f , cst x ⟫
    
  join : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → Src X (Src X P) i → Src X P i
  join X P s  =
    ⟪ μ X (web s) (λ p → web (dec s p)) 
    , (λ p → dec (dec s (fstₒ (pd s) (λ p → pd (dec s p)) p))
                 (sndₒ (pd s) (λ p → pd (dec s p)) p)) ⟫ 
    

  --
  --  Implementation
  --

  {-# NO_UNIVERSE_CHECK #-}
  {-# NO_POSITIVITY_CHECK #-}
  data 𝕆Type ℓ where
  
    ■ : 𝕆Type ℓ 0
    
    _∥_ : {n : ℕ} (X : 𝕆Type ℓ n)
      → (P : Idx X → Type ℓ)
      → 𝕆Type ℓ (suc n)

  {-# NO_UNIVERSE_CHECK #-}
  data Frm {ℓ} where

    ▣ : Frm ■ ●

    _►[_,_] : {n : ℕ} {X : 𝕆Type ℓ n}
      → {P : Idx X → Type ℓ}
      → {ο : 𝕆 n} (f : Frm X ο)
      → (t : P (ο , f))
      → (s : Src X P (ο , f))
      → Frm (X ∥ P) (ο ∣ pd s) 

  record CappedPd {ℓ n} (X : 𝕆Type ℓ n)
    (P : Idx X → Type ℓ)
    {i : Idx X} (tgt : P i) : Type ℓ where
    inductive
    eta-equality
    constructor ⟦_⟧
    field

      {lvs} : Src X P i
      {tr} : ℙ (fst i ∣ pd lvs)
      trnk : Web (X ∥ P) (snd i ►[ tgt , lvs ]) tr 

  open CappedPd public

  {-# NO_UNIVERSE_CHECK #-}
  data Web {ℓ} where

    obj : Web ■ ▣ objₒ

    lf : {n : ℕ} {X : 𝕆Type ℓ n}
       → {P : Idx X → Type ℓ}
       → {i : Idx X} (tgt : P i)
       → Web (X ∥ P) (snd i ►[ tgt , ret X P tgt ]) (lfₒ (fst i)) 

    nd : {n : ℕ} {X : 𝕆Type ℓ n}
       → {P : Idx X → Type ℓ}
       → {i : Idx X} (tgt : P i) (src : Src X P i)
       → (δ : (p : Pos (pd src)) → CappedPd X P (dec src p))
       → Web (X ∥ P) (snd i ►[ tgt , join X P ⟪ web src , (λ p → lvs (δ p)) ⟫ ]) 
           (ndₒ (pd src) (λ p → ⟨ tr (δ p) ⟩))

  Shp ■ obj this = ▣
  Shp (X ∥ P) (nd {i = _ , frm} tgt src δ) here = frm ►[ tgt , src ]
  Shp (X ∥ P) (nd tgt src δ) (there p q) = Shp (X ∥ P) (trnk (δ p)) q

  η ■ ▣ = obj
  η (X ∥ P) (f ►[ t , s ]) =
    nd t s (λ p → ⟦ lf (dec s p) ⟧)

  γ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} {s : Src X P i} {t : P i}
    → {τ : ℙ (fst i ∣ pd s)}
    → (ω : Web (X ∥ P) (snd i ►[ t , s ]) τ)
    → (ϕ : (p : Pos (pd s)) → CappedPd X P (dec s p))
    → Web (X ∥ P) (snd i ►[ t , join X P ⟪ web s , (λ p → lvs (ϕ p)) ⟫ ])
        (γₒ τ (λ p → ⟨ tr (ϕ p) ⟩))
  γ X P (lf t) ϕ = trnk (ϕ (η-posₒ _))
  γ X P (nd t s δ) ϕ = 
    nd t s (λ p → ⟦ γ X P (trnk (δ p)) (λ q → ϕ (pairₒ (pd s) (λ r → pd (lvs (δ r))) p q)) ⟧)
  
  μ ■ obj ϕ = obj
  μ (X ∥ P) (lf tgt) ϕ = lf tgt
  μ (X ∥ P) (nd tgt src δ) ϕ = 
    γ X P (ϕ here) (λ p → ⟦ μ (X ∥ P) (trnk (δ p)) (λ q → ϕ (there p q)) ⟧)

