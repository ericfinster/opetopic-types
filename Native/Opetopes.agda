{-# OPTIONS --no-positivity-check #-}

open import Core.Prelude

module Native.Opetopes where

  --
  --  Polynomial Signature
  --
  
  𝕆 : (n : ℕ) → Type
  {-# BUILTIN OP 𝕆 #-}
  
  ℙ : (n : ℕ) (ο : 𝕆 n) → Type
  {-# BUILTIN PD ℙ #-}

  Pos : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) → Type
  {-# BUILTIN POS Pos #-}
  
  Typ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (p : Pos n ο ρ) → 𝕆 n 
  {-# BUILTIN TYP Typ #-}

  --
  --  Monadic Signature 
  --
  
  ηₒ : (n : ℕ) (ο : 𝕆 n) → ℙ n ο
  {-# BUILTIN UNT ηₒ #-}

  η-posₒ : (n : ℕ) (ο : 𝕆 n) → Pos n ο (ηₒ n ο)
  {-# BUILTIN UNTPOS η-posₒ #-}

  μₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
    → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → ℙ n ο
  {-# BUILTIN SUBST μₒ #-}

  pairₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
    → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (p : Pos n ο ρ) (q : Pos n (Typ n ο ρ p) (δ p))
    → Pos n ο (μₒ n ο ρ δ)
  {-# BUILTIN SUBSTPOS pairₒ #-}

  fstₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
    → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (p : Pos n ο (μₒ n ο ρ δ))
    → Pos n ο ρ
  {-# BUILTIN SUBSTFST fstₒ #-}

  sndₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
    → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (p : Pos n ο (μₒ n ο ρ δ))
    → Pos n (Typ n ο ρ (fstₒ n ο ρ δ p)) (δ (fstₒ n ο ρ δ p))
  {-# BUILTIN SUBSTSND sndₒ #-}

  --
  --  Equations
  --
  
  postulate
  
    --
    --  Position Equations
    --

    Typ-η : (n : ℕ) (ο : 𝕆 n) (p : Pos n ο (ηₒ n ο))
      → Typ n ο (ηₒ n ο) p ↦ ο 
    {-# REWRITE Typ-η #-}

    Typ-μₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (p : Pos n ο (μₒ n ο ρ δ))
      → Typ n ο (μₒ n ο ρ δ) p ↦
        Typ n (Typ n ο ρ (fstₒ n ο ρ δ p)) (δ (fstₒ n ο ρ δ p))
              (sndₒ n ο ρ δ p) 
    {-# REWRITE Typ-μₒ #-} 

    fstₒ-β : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (p : Pos n ο ρ) (q : Pos n (Typ n ο ρ p) (δ p))
      → fstₒ n ο ρ δ (pairₒ n ο ρ δ p q) ↦ p
    {-# REWRITE fstₒ-β #-}

    sndₒ-β : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (p : Pos n ο ρ) (q : Pos n (Typ n ο ρ p) (δ p))
      → sndₒ n ο ρ δ (pairₒ n ο ρ δ p q) ↦ q
    {-# REWRITE sndₒ-β #-}

    --
    --  Monadic Equations
    --

    -- TODO - missing elim compatibilities 

    μ-unit-r : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
      → μₒ n ο ρ (λ p → ηₒ n (Typ n ο ρ p)) ↦ ρ
    {-# REWRITE μ-unit-r #-}

    μ-unit-ℓ : (n : ℕ) (ο : 𝕆 n)
      → (δ : (p : Pos n ο (ηₒ n ο)) → ℙ n ο)
      → μₒ n ο (ηₒ n ο) δ ↦ δ (η-posₒ n ο) 
    {-# REWRITE μ-unit-ℓ #-}

    μ-assoc : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (ϵ : (p : Pos n ο (μₒ n ο ρ δ)) → ℙ n (Typ n ο (μₒ n ο ρ δ) p))
      → μₒ n ο (μₒ n ο ρ δ) ϵ ↦
        μₒ n ο ρ (λ p → μₒ n (Typ n ο ρ p) (δ p)
                   (λ q → ϵ (pairₒ n ο ρ δ p q)))
    {-# REWRITE μ-assoc #-}

  --
  --  Implementations 
  --

  𝕆 zero = 𝟙 ℓ-zero
  𝕆 (suc n) = Σ[ ο ∈ 𝕆 n ] ℙ n ο

  data Tr (n : ℕ) : 𝕆 (suc n) → Type where

    lfₒ : (ο : 𝕆 n) → Tr n (ο , ηₒ n ο) 

    ndₒ : (ο : 𝕆 n) (ρ : ℙ n ο)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (ϵ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , δ p))
      → Tr n (ο , μₒ n ο ρ δ)

  data TrPos (n : ℕ) : (ο : 𝕆 (suc n)) → Tr n ο → Type where

    nd-hereₒ : {ο : 𝕆 n} {ρ : ℙ n ο}
      → {δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p)}
      → {ϵ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , δ p)}
      → TrPos n (ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ)

    nd-thereₒ : {ο : 𝕆 n} {ρ : ℙ n ο}
      → {δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p)}
      → {ϵ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , δ p)}
      → (p : Pos n ο ρ) (q : TrPos n (Typ n ο ρ p , δ p) (ϵ p))
      → TrPos n (ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ)

  ℙ zero ο = 𝟙 ℓ-zero
  ℙ (suc n) ο = Tr n ο
  
  Pos zero ο ρ = 𝟙 ℓ-zero
  Pos (suc n) ο ρ = TrPos n ο ρ
  
  Typ zero ο ρ p = ●
  Typ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) nd-hereₒ = ο , ρ
  Typ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) (nd-thereₒ p q) =
    Typ (suc n) (Typ n ο ρ p , δ p) (ϵ p) q

  --
  --  Unit 
  --
  
  ηₒ zero ο = ●
  ηₒ (suc n) (ο , ρ) =
    ndₒ ο ρ (λ p → ηₒ n (Typ n ο ρ p))
            (λ p → lfₒ (Typ n ο ρ p))
  
  η-posₒ zero ο = ●
  η-posₒ (suc n) (ο , ρ) = nd-hereₒ

  --
  --  Grafting 
  --
  
  γₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (τ : Tr n (ο , ρ))
    → (ϕ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (ψ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , ϕ p))
    → Tr n (ο , μₒ n ο ρ ϕ)
  γₒ n ο .(ηₒ n ο) (lfₒ .ο) ϕ ψ = ψ (η-posₒ n ο)
  γₒ n ο .(μₒ n ο ρ δ) (ndₒ .ο ρ δ ϵ) ϕ ψ =
    let ϕ' p q = ϕ (pairₒ n ο ρ δ p q)
        ψ' p q = ψ (pairₒ n ο ρ δ p q)
        δ' p = μₒ n (Typ n ο ρ p) (δ p) (ϕ' p)
        ϵ' p = γₒ n (Typ n ο ρ p) (δ p) (ϵ p) (ϕ' p) (ψ' p)
    in ndₒ ο ρ δ' ϵ'

  inlₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (τ : Tr n (ο , ρ))
    → (ϕ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (ψ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , ϕ p))
    → (p : TrPos n (ο , ρ) τ)
    → TrPos n (ο , μₒ n ο ρ ϕ) (γₒ n ο ρ τ ϕ ψ)
  inlₒ n ο .(μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ ψ nd-hereₒ = nd-hereₒ
  inlₒ n ο .(μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ ψ (nd-thereₒ p q) =
    let ϕ' p q = ϕ (pairₒ n ο ρ δ p q)
        ψ' p q = ψ (pairₒ n ο ρ δ p q)
    in nd-thereₒ p (inlₒ n (Typ n ο ρ p) (δ p) (ϵ p) (ϕ' p) (ψ' p) q)

  inrₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (τ : Tr n (ο , ρ))
    → (ϕ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (ψ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , ϕ p))
    → (p : Pos n ο ρ) (q : TrPos n (Typ n ο ρ p , ϕ p) (ψ p))
    → TrPos n (ο , μₒ n ο ρ ϕ) (γₒ n ο ρ τ ϕ ψ)
  inrₒ n ο .(ηₒ n ο) (lfₒ .ο) ϕ ψ p q = q
  inrₒ n ο .(μₒ n ο ρ δ) (ndₒ .ο ρ δ ϵ) ϕ ψ pq r =
    let ϕ' p q = ϕ (pairₒ n ο ρ δ p q)
        ψ' p q = ψ (pairₒ n ο ρ δ p q)
        p = fstₒ n ο ρ δ pq
        q = sndₒ n ο ρ δ pq 
    in nd-thereₒ p (inrₒ n (Typ n ο ρ p) (δ p) (ϵ p) (ϕ' p) (ψ' p) q r)

  caseₒ : ∀ {ℓ} (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (τ : Tr n (ο , ρ))
    → (ϕ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
    → (ψ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , ϕ p))
    → (P : TrPos n (ο , μₒ n ο ρ ϕ) (γₒ n ο ρ τ ϕ ψ) → Type ℓ)
    → (inl* : (p : TrPos n (ο , ρ) τ) → P (inlₒ n ο ρ τ ϕ ψ p))
    → (inr* : (p : Pos n ο ρ) (q : TrPos n (Typ n ο ρ p , ϕ p) (ψ p)) → P (inrₒ n ο ρ τ ϕ ψ p q))
    → (p : TrPos n (ο , μₒ n ο ρ ϕ) (γₒ n ο ρ τ ϕ ψ)) → P p
  caseₒ n ο .(ηₒ n ο) (lfₒ .ο) ϕ ψ P inl* inr* p = inr* (η-posₒ n ο) p
  caseₒ n ο .(μₒ n ο ρ δ) (ndₒ .ο ρ δ ϵ) ϕ ψ P inl* inr* nd-hereₒ = inl* nd-hereₒ
  caseₒ n ο .(μₒ n ο ρ δ) (ndₒ .ο ρ δ ϵ) ϕ ψ P inl* inr* (nd-thereₒ u v) =
    let ϕ' p q = ϕ (pairₒ n ο ρ δ p q)
        ψ' p q = ψ (pairₒ n ο ρ δ p q)
    in caseₒ n (Typ n ο ρ u) (δ u) (ϵ u) (ϕ' u) (ψ' u)
          (λ q → P (nd-thereₒ u q))
          (λ q → inl* (nd-thereₒ u q))
          (λ p q → inr* (pairₒ n ο ρ δ u p) q) v

  postulate

    case-inl-β : ∀ {ℓ} (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (τ : Tr n (ο , ρ))
      → (ϕ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (ψ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , ϕ p))
      → (P : TrPos n (ο , μₒ n ο ρ ϕ) (γₒ n ο ρ τ ϕ ψ) → Type ℓ)
      → (inl* : (p : TrPos n (ο , ρ) τ) → P (inlₒ n ο ρ τ ϕ ψ p))
      → (inr* : (p : Pos n ο ρ) (q : TrPos n (Typ n ο ρ p , ϕ p) (ψ p)) → P (inrₒ n ο ρ τ ϕ ψ p q))
      → (p : TrPos n (ο , ρ) τ)
      → caseₒ n ο ρ τ ϕ ψ P inl* inr* (inlₒ n ο ρ τ ϕ ψ p) ↦ inl* p
    {-# REWRITE case-inl-β #-}

    case-inr-β : ∀ {ℓ} (n : ℕ) (ο : 𝕆 n) (ρ : ℙ n ο) (τ : Tr n (ο , ρ))
      → (ϕ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (ψ : (p : Pos n ο ρ) → Tr n (Typ n ο ρ p , ϕ p))
      → (P : TrPos n (ο , μₒ n ο ρ ϕ) (γₒ n ο ρ τ ϕ ψ) → Type ℓ)
      → (inl* : (p : TrPos n (ο , ρ) τ) → P (inlₒ n ο ρ τ ϕ ψ p))
      → (inr* : (p : Pos n ο ρ) (q : TrPos n (Typ n ο ρ p , ϕ p) (ψ p)) → P (inrₒ n ο ρ τ ϕ ψ p q))
      → (p : Pos n ο ρ) (q : TrPos n (Typ n ο ρ p , ϕ p) (ψ p))     
      → caseₒ n ο ρ τ ϕ ψ P inl* inr* (inrₒ n ο ρ τ ϕ ψ p q) ↦ inr* p q
    {-# REWRITE case-inr-β #-}

  --
  --  Substitution
  --

  μₒ zero ο ρ δ = ●
  μₒ (suc n) .(ο , ηₒ n ο) (lfₒ ο) δ = lfₒ ο
  μₒ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ =
    let ϕ' p q = ϕ (nd-thereₒ p q)
        ih p = μₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p)
    in γₒ n ο ρ (ϕ nd-hereₒ) δ ih 

  pairₒ zero ο ρ δ p q = ●
  pairₒ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ nd-hereₒ q =
    let ϕ' p q = ϕ (nd-thereₒ p q)
        ih p = μₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p)
    in inlₒ n ο ρ (ϕ nd-hereₒ) δ ih q
  pairₒ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ (nd-thereₒ p q) r = 
    let ϕ' p q = ϕ (nd-thereₒ p q)
        ih p = μₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p)
    in inrₒ n ο ρ (ϕ nd-hereₒ) δ ih p (pairₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p) q r) 

  fstₒ zero ο ρ δ p = ●
  fstₒ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ = 
    let ϕ' p q = ϕ (nd-thereₒ p q)
        ih p = μₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p)
    in caseₒ n ο ρ (ϕ nd-hereₒ) δ ih
         (λ p → TrPos n (ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ))
         (λ p → nd-hereₒ)
         (λ p q → nd-thereₒ p (fstₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p) q))
    
  sndₒ zero ο ρ δ p = ●
  sndₒ (suc n) .(ο , μₒ n ο ρ δ) (ndₒ ο ρ δ ϵ) ϕ = 
    let ϕ' p q = ϕ (nd-thereₒ p q)
        ih p = μₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p)
    in caseₒ n ο ρ (ϕ nd-hereₒ) δ ih _
         (λ p → p)
         (λ p q → sndₒ (suc n) (Typ n ο ρ p , δ p) (ϵ p) (ϕ' p) q)
