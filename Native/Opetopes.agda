{-# OPTIONS --no-positivity-check #-}

open import Core.Prelude

module Native.Opetopes where

  --
  --  Polynomial Signature
  --

  𝕆 : (n : ℕ) → Type
  {-# BUILTIN OP 𝕆 #-}

  ℙ : {n : ℕ} (ο : 𝕆 n) → Type
  {-# BUILTIN PD ℙ #-}
  
  Pos : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) → Type
  {-# BUILTIN POS Pos #-}
  
  Typ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → 𝕆 n
  {-# BUILTIN TYP Typ #-}

  ηₒ : {n : ℕ} (ο : 𝕆 n) → ℙ ο
  {-# BUILTIN UNT ηₒ #-}
    
  η-posₒ : {n : ℕ} (ο : 𝕆 n) → Pos (ηₒ ο)
  {-# BUILTIN UNTPOS η-posₒ #-}

  μₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
    → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
    → ℙ ο
  {-# BUILTIN SUBST μₒ #-}

  pairₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
    → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
    → (p : Pos ρ) (q : Pos (δ p))
    → Pos (μₒ ρ δ)
  {-# BUILTIN SUBSTPOS pairₒ #-}

  fstₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
    → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
    → (p : Pos (μₒ ρ δ))
    → Pos ρ
  {-# BUILTIN SUBSTFST fstₒ #-}

  sndₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
    → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
    → (p : Pos (μₒ ρ δ))
    → Pos (δ (fstₒ ρ δ p))
  {-# BUILTIN SUBSTSND sndₒ #-}

  --
  --  Equations
  --
  
  postulate
  
    --
    --  Position Equations
    --

    Typ-η : (n : ℕ) (ο : 𝕆 n) (p : Pos (ηₒ ο))
      → Typ (ηₒ ο) p ↦ ο 
    {-# REWRITE Typ-η #-}

    Typ-μₒ : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (p : Pos (μₒ ρ δ))
      → Typ (μₒ ρ δ) p ↦ Typ (δ (fstₒ ρ δ p)) (sndₒ ρ δ p) 
    {-# REWRITE Typ-μₒ #-} 

    fstₒ-β : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (p : Pos ρ) (q : Pos (δ p))
      → fstₒ ρ δ (pairₒ ρ δ p q) ↦ p
    {-# REWRITE fstₒ-β #-}

    sndₒ-β : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (p : Pos ρ) (q : Pos (δ p))
      → sndₒ ρ δ (pairₒ ρ δ p q) ↦ q
    {-# REWRITE sndₒ-β #-}

    --
    --  Monadic Equations
    --

    -- right unit 
    μₒ-unit-r : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → μₒ ρ (λ p → ηₒ (Typ ρ p)) ↦ ρ
    {-# REWRITE μₒ-unit-r #-}

    fstₒ-unit-r : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (p : Pos ρ)
      → fstₒ ρ (λ p → ηₒ (Typ ρ p)) p ↦ p
    {-# REWRITE fstₒ-unit-r #-}

    -- I think this one is unnecessary because of η-laws
    sndₒ-unit-r : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (p : Pos ρ)
      → sndₒ ρ (λ p → ηₒ (Typ ρ p)) p ↦ η-posₒ (Typ ρ p)
    {-# REWRITE sndₒ-unit-r #-}
    
    pairₒ-unit-r : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (p : Pos ρ) (q : Pos (ηₒ (Typ ρ p)))
      → pairₒ ρ (λ p → ηₒ (Typ ρ p)) p q ↦ p
    {-# REWRITE pairₒ-unit-r #-}

    -- left unit 
    μₒ-unit-l : (n : ℕ) (ο : 𝕆 n)
      → (δ : (p : Pos (ηₒ ο)) → ℙ ο)
      → μₒ (ηₒ ο) δ ↦ δ (η-posₒ ο) 
    {-# REWRITE μₒ-unit-l #-}

    fstₒ-unit-l : (n : ℕ) (ο : 𝕆 n)
      → (δ : (p : Pos (ηₒ ο)) → ℙ ο)
      → (p : Pos (δ (η-posₒ ο)))
      → fstₒ (ηₒ ο) δ p ↦ η-posₒ ο
    {-# REWRITE fstₒ-unit-l #-}
    
    sndₒ-unit-l : (n : ℕ) (ο : 𝕆 n)
      → (δ : (p : Pos (ηₒ ο)) → ℙ ο)
      → (p : Pos (δ (η-posₒ ο)))
      → sndₒ (ηₒ ο) δ p ↦ p
    {-# REWRITE sndₒ-unit-l #-}

    pairₒ-unit-l : (n : ℕ) (ο : 𝕆 n)
      → (δ : (p : Pos (ηₒ ο)) → ℙ ο)
      → (p : Pos (ηₒ ο)) (q : Pos (δ p))
      → pairₒ (ηₒ ο) δ p q ↦ q
    {-# REWRITE pairₒ-unit-l #-}
  
    -- associativity
    μₒ-assoc : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (ϵ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p))
      → μₒ (μₒ ρ δ) ϵ ↦ μₒ ρ (λ p → μₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q)))
    {-# REWRITE μₒ-assoc #-}

    fstₒ-assoc : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (ϵ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p))
      → (pqr : Pos (μₒ (μₒ ρ δ) ϵ))
      → fstₒ (μₒ ρ δ) ϵ pqr ↦
          let p' = fstₒ ρ (λ p → μₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q))) pqr
              q' = sndₒ ρ (λ p → μₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q))) pqr
          in pairₒ ρ δ p' (fstₒ (δ p') (λ q' → ϵ (pairₒ ρ δ p' q')) q')
    {-# REWRITE fstₒ-assoc #-}

    sndₒ-assoc : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (ϵ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p))
      → (pqr : Pos (μₒ (μₒ ρ δ) ϵ))
      → sndₒ (μₒ ρ δ) ϵ pqr ↦ 
          let p' = fstₒ ρ (λ p → μₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q))) pqr
              q' = sndₒ ρ (λ p → μₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q))) pqr
          in sndₒ (δ p') (λ q' → ϵ (pairₒ ρ δ p' q')) q'
    {-# REWRITE sndₒ-assoc #-}

    pairₒ-assoc : (n : ℕ) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (ϵ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p))
      → (pq : Pos (μₒ ρ δ)) (r : Pos (ϵ pq))
      → pairₒ (μₒ ρ δ) ϵ pq r ↦
          let p = fstₒ ρ δ pq
              q = sndₒ ρ δ pq 
          in pairₒ ρ (λ p → μₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q))) p
               (pairₒ (δ p) (λ q → ϵ (pairₒ ρ δ p q)) q r) 
    {-# REWRITE pairₒ-assoc #-}
    
  --
  --  Implementations 
  --

  𝕆 zero = 𝟙 ℓ-zero
  𝕆 (suc n) = Σ[ ο ∈ 𝕆 n ] ℙ ο

  data Tr {n : ℕ} : 𝕆 (suc n) → Type where

    lfₒ : (ο : 𝕆 n) → Tr (ο , ηₒ ο) 

    ndₒ : {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
      → Tr (ο , μₒ ρ (λ p → fst (δ p)))

  data TrPos {n : ℕ} : {ο : 𝕆 (suc n)} → Tr ο → Type where

    here : {ο : 𝕆 n} {ρ : ℙ ο}
      → {δ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs)}
      → TrPos (ndₒ ρ δ)

    there : {ο : 𝕆 n} {ρ : ℙ ο}
      → {δ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs)}
      → (p : Pos ρ) (q : TrPos (snd (δ p)))
      → TrPos (ndₒ ρ δ)

  ℙ {zero} ο = 𝟙 ℓ-zero
  ℙ {suc n} ο = Tr ο
  
  Pos {zero} ρ = 𝟙 ℓ-zero
  Pos {suc n} ρ = TrPos ρ
  
  Typ {zero} ρ p = ●
  Typ {suc n} ._ (here {ο} {ρ})  = ο , ρ
  Typ {suc n} ._ (there {δ = δ} p q) = Typ (snd (δ p)) q

  --
  --  Unit 
  --
  
  ηₒ {zero} ο = ●
  ηₒ {suc n} (ο , ρ) = ndₒ ρ (λ p → ηₒ (Typ ρ p) , lfₒ (Typ ρ p))
  
  η-posₒ {zero} ο = ●
  η-posₒ {suc n} (ο , ρ) = here
  
  --
  --  Grafting 
  --
  
  γₒ : {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο} (τ : Tr (ο , ρ))
    → (ϕ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
    → Tr (ο , μₒ ρ (λ p → fst (ϕ p)))
  γₒ (lfₒ o) ϕ = snd (ϕ (η-posₒ o))
  γₒ (ndₒ ρ δ) ϕ =
    let ϕ' p q = ϕ (pairₒ ρ (λ r → fst (δ r)) p q)
    in ndₒ ρ (λ p → μₒ (fst (δ p)) (λ q → fst (ϕ' p q)) ,
                    γₒ (snd (δ p)) (ϕ' p))

  inlₒ : {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο} (τ : Tr (ο , ρ))
    → (ϕ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
    → (p : TrPos τ) → TrPos (γₒ τ ϕ)
  inlₒ (ndₒ ρ δ) ϕ here = here
  inlₒ (ndₒ ρ δ) ϕ (there p q) =
    let ϕ' p q = ϕ (pairₒ ρ (λ r → fst (δ r)) p q)
    in there p (inlₒ (snd (δ p)) (ϕ' p) q)

  inrₒ : {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο} (τ : Tr (ο , ρ))
    → (ϕ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
    → (p : Pos ρ) (q : TrPos (snd (ϕ p))) → TrPos (γₒ τ ϕ)
  inrₒ (lfₒ ο) ϕ p q = q
  inrₒ (ndₒ ρ δ) ϕ pq r = 
    let ϕ' p q = ϕ (pairₒ ρ (λ r → fst (δ r)) p q)
        p = fstₒ ρ (λ r → fst (δ r)) pq
        q = sndₒ ρ (λ r → fst (δ r)) pq 
    in there p (inrₒ (snd (δ p)) (ϕ' p) q r)

  caseₒ : ∀ {ℓ} {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο} (τ : Tr (ο , ρ))
    → (ϕ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
    → (P : TrPos (γₒ τ ϕ) → Type ℓ)
    → (inl* : (p : TrPos τ) → P (inlₒ τ ϕ p))
    → (inr* : (p : Pos ρ) (q : TrPos (snd (ϕ p))) → P (inrₒ τ ϕ p q))
    → (p : TrPos (γₒ τ ϕ)) → P p
  caseₒ (lfₒ ο) ϕ P inl* inr* p = inr* (η-posₒ ο) p
  caseₒ (ndₒ ρ δ) ϕ P inl* inr* here = inl* here
  caseₒ (ndₒ ρ δ) ϕ P inl* inr* (there u v) = 
    let ϕ' p q = ϕ (pairₒ ρ (λ r → fst (δ r)) p q)
    in caseₒ (snd (δ u)) (ϕ' u) (λ q → P (there u q))
         (λ q → inl* (there u q))
         (λ p q → inr* (pairₒ ρ (λ r → fst (δ r)) u p) q) v

  postulate

    case-inl-β : ∀ {ℓ} {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο} (τ : Tr (ο , ρ))
      → (ϕ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
      → (P : TrPos (γₒ τ ϕ) → Type ℓ)
      → (inl* : (p : TrPos τ) → P (inlₒ τ ϕ p))
      → (inr* : (p : Pos ρ) (q : TrPos (snd (ϕ p))) → P (inrₒ τ ϕ p q))
      → (p : TrPos τ)
      → caseₒ τ ϕ P inl* inr* (inlₒ τ ϕ p) ↦ inl* p
    {-# REWRITE case-inl-β #-}

    case-inr-β : ∀ {ℓ} {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο} (τ : Tr (ο , ρ))
      → (ϕ : (p : Pos ρ) → Σ[ lvs ∈ ℙ (Typ ρ p) ] Tr (Typ ρ p , lvs))
      → (P : TrPos (γₒ τ ϕ) → Type ℓ)
      → (inl* : (p : TrPos τ) → P (inlₒ τ ϕ p))
      → (inr* : (p : Pos ρ) (q : TrPos (snd (ϕ p))) → P (inrₒ τ ϕ p q))
      → (p : Pos ρ) (q : TrPos (snd (ϕ p))) 
      → caseₒ τ ϕ P inl* inr* (inrₒ τ ϕ p q) ↦ inr* p q 
    {-# REWRITE case-inr-β #-}


  --
  --  Substitution 
  --

  μₒ {zero} ρ ϕ = ●
  μₒ {suc n} (lfₒ ο) ϕ = lfₒ ο
  μₒ {suc n} (ndₒ ρ δ) ϕ =
    let ϕ' p q = ϕ (there p q)
        ih p = fst (δ p) , μₒ (snd (δ p)) (ϕ' p)
    in γₒ (ϕ here) ih
  
  pairₒ {zero} ρ ϕ p q = ●
  pairₒ {suc n} (ndₒ ρ δ) ϕ here r = 
    let ϕ' p q = ϕ (there p q)
        ih p = fst (δ p) , μₒ (snd (δ p)) (ϕ' p)
    in inlₒ (ϕ here) ih r 
  pairₒ {suc n} (ndₒ ρ δ) ϕ (there p q) r = 
    let ϕ' p q = ϕ (there p q)
        ih p = fst (δ p) , μₒ (snd (δ p)) (ϕ' p)
    in inrₒ (ϕ here) ih p (pairₒ (snd (δ p)) (ϕ' p) q r) 

  fstₒ {zero} ρ ϕ pq = ●
  fstₒ {suc n} (ndₒ ρ δ) ϕ pq = 
    let ϕ' p q = ϕ (there p q)
        ih p = fst (δ p) , μₒ (snd (δ p)) (ϕ' p)
    in caseₒ (ϕ here) ih (λ _ → TrPos (ndₒ ρ δ))
          (λ _ → here)
          (λ p q → there p (fstₒ (snd (δ p)) (ϕ' p) q)) pq

  sndₒ {zero} ρ ϕ pq = ●
  sndₒ {suc n} (ndₒ ρ δ) ϕ pq = 
    let ϕ' p q = ϕ (there p q)
        ih p = fst (δ p) , μₒ (snd (δ p)) (ϕ' p)
    in caseₒ (ϕ here) ih (λ p → TrPos (ϕ (fstₒ (ndₒ ρ δ) ϕ p)))
         (λ p → p)
         (λ p q → sndₒ (snd (δ p)) (ϕ' p) q) pq

