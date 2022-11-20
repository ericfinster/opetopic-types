{-# OPTIONS --no-termination-check #-}

open import Core.Prelude

module Native.ElimOpetopes where

  postulate
  
    -- Polynomial Signature
    𝕆 : (n : ℕ) → Type 
    ℙ : {n : ℕ} (ο : 𝕆 n) → Type
    Pos : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) → Type

  Typ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → 𝕆 n

  -- Unit
  ηₒ : {n : ℕ} (ο : 𝕆 n) → ℙ ο
  η-posₒ : {n : ℕ} (ο : 𝕆 n) → Pos (ηₒ ο)

  postulate

    -- Substitution
    μₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → ℙ ο

    pairₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (p : Pos ρ) (q : Pos (δ p))
      → Pos (μₒ ρ δ)

    fstₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (p : Pos (μₒ ρ δ))
      → Pos ρ

    sndₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → (p : Pos (μₒ ρ δ))
      → Pos (δ (fstₒ ρ δ p))

  {-# BUILTIN OP 𝕆 #-}
  {-# BUILTIN PD ℙ #-}
  {-# BUILTIN POS Pos #-}
  {-# BUILTIN TYP Typ #-}
  {-# BUILTIN UNT ηₒ #-}
  {-# BUILTIN UNTPOS η-posₒ #-}
  {-# BUILTIN SUBST μₒ #-}
  {-# BUILTIN SUBSTPOS pairₒ #-}
  {-# BUILTIN SUBSTFST fstₒ #-}
  {-# BUILTIN SUBSTSND sndₒ #-}

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
  
  postulate

    -- Opetopic Constructors
    ■ : 𝕆 0
    _∣_ : {n : ℕ} → (ο : 𝕆 n) (ρ : ℙ ο) → 𝕆 (suc n) 

    𝕆-elim : ∀ {ℓ}
      → (P : {n : ℕ} → 𝕆 n → Type ℓ)
      → (■* : P ■)
      → (∣* : {n : ℕ} (ο : 𝕆 n) (ρ : ℙ ο) → P (ο ∣ ρ))
      → {n : ℕ} (ο : 𝕆 n) → P ο 

    𝕆-elim-■-β : ∀ {ℓ}
      → (P : {n : ℕ} → 𝕆 n → Type ℓ)
      → (■* : P ■)
      → (∣* : {n : ℕ} (ο : 𝕆 n) (ρ : ℙ ο) → P (ο ∣ ρ))
      → 𝕆-elim P ■* ∣* ■ ↦ ■*
    {-# REWRITE 𝕆-elim-■-β #-}

    𝕆-elim-∣-β : ∀ {ℓ}
      → (P : {n : ℕ} → 𝕆 n → Type ℓ)
      → (■* : P ■)
      → (∣* : {n : ℕ} (ο : 𝕆 n) (ρ : ℙ ο) → P (ο ∣ ρ))
      → {n : ℕ} (ο : 𝕆 n) (ρ : ℙ ο)
      → 𝕆-elim P ■* ∣* (ο ∣ ρ) ↦ ∣* ο ρ
    {-# REWRITE 𝕆-elim-∣-β #-}

  record Branch {n} (ο : 𝕆 n) : Type where
    eta-equality
    constructor ⟨_⟩  
    field
      {top} : ℙ ο
      br : ℙ (ο ∣ top) 

  open Branch public

  postulate

    --
    --  Tree constructors 
    --
    
    objₒ : ℙ ■
    lfₒ : {n : ℕ} → (ο : 𝕆 n) → ℙ (ο ∣ ηₒ ο)
    ndₒ : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → Branch (Typ ρ p))
      → ℙ (ο ∣ μₒ ρ (λ p → top (δ p)))

    ℙ-elim : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} → ℙ ο → Type ℓ)
      → (obj* : P objₒ)
      → (lf* : {n : ℕ} (ο : 𝕆 n) → P (lfₒ ο))
      → (nd* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
             → (δ : (p : Pos ρ) → Branch (Typ ρ p))
             → P (ndₒ ρ δ))
      → {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) → P ρ 

    ℙ-elim-obj-β : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} → ℙ ο → Type ℓ)
      → (obj* : P objₒ)
      → (lf* : {n : ℕ} (ο : 𝕆 n) → P (lfₒ ο))
      → (nd* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
             → (δ : (p : Pos ρ) → Branch (Typ ρ p))
             → P (ndₒ ρ δ))
      → ℙ-elim P obj* lf* nd* objₒ ↦ obj*
    {-# REWRITE ℙ-elim-obj-β #-}
    
    ℙ-elim-lf-β : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} → ℙ ο → Type ℓ)
      → (obj* : P objₒ)
      → (lf* : {n : ℕ} (ο : 𝕆 n) → P (lfₒ ο))
      → (nd* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
             → (δ : (p : Pos ρ) → Branch (Typ ρ p))
             → P (ndₒ ρ δ))
      → {n : ℕ} (ο : 𝕆 n)
      → ℙ-elim P obj* lf* nd* (lfₒ ο) ↦ lf* ο
    {-# REWRITE ℙ-elim-lf-β #-}

    ℙ-elim-nd-β : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} → ℙ ο → Type ℓ)
      → (obj* : P objₒ)
      → (lf* : {n : ℕ} (ο : 𝕆 n) → P (lfₒ ο))
      → (nd* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
             → (δ : (p : Pos ρ) → Branch (Typ ρ p))
             → P (ndₒ ρ δ))
      → {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → Branch (Typ ρ p))
      → ℙ-elim P obj* lf* nd* (ndₒ ρ δ) ↦ nd* ρ δ
    {-# REWRITE ℙ-elim-nd-β #-}

    --
    --  Position constructors 
    --
    
    this : Pos objₒ

    here : {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο}
      → {δ : (p : Pos ρ) → Branch (Typ ρ p)}
      → Pos (ndₒ ρ δ)

    there : {n : ℕ} {ο : 𝕆 n} {ρ : ℙ ο}
      → {δ : (p : Pos ρ) → Branch (Typ ρ p)}
      → (p : Pos ρ) (q : Pos (br (δ p)))
      → Pos (ndₒ ρ δ)

    Pos-elim : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → Type ℓ)
      → (this* : P objₒ this)
      → (here* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
               → (δ : (p : Pos ρ) → Branch (Typ ρ p))
               → P (ndₒ ρ δ) here)
      → (there* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
                → (δ : (p : Pos ρ) → Branch (Typ ρ p))
                → (p : Pos ρ) (q : Pos (br (δ p)))
                → P (ndₒ ρ δ) (there p q))
      → {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → P ρ p 

    Pos-elim-this-β : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → Type ℓ)
      → (this* : P objₒ this)
      → (here* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
               → (δ : (p : Pos ρ) → Branch (Typ ρ p))
               → P (ndₒ ρ δ) here)
      → (there* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
                → (δ : (p : Pos ρ) → Branch (Typ ρ p))
                → (p : Pos ρ) (q : Pos (br (δ p)))
                → P (ndₒ ρ δ) (there p q))
      → Pos-elim P this* here* there* objₒ this ↦ this*
    {-# REWRITE Pos-elim-this-β #-}

    Pos-elim-here-β : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → Type ℓ)
      → (this* : P objₒ this)
      → (here* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
               → (δ : (p : Pos ρ) → Branch (Typ ρ p))
               → P (ndₒ ρ δ) here)
      → (there* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
                → (δ : (p : Pos ρ) → Branch (Typ ρ p))
                → (p : Pos ρ) (q : Pos (br (δ p)))
                → P (ndₒ ρ δ) (there p q))
      → {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → Branch (Typ ρ p))
      → Pos-elim P this* here* there* (ndₒ ρ δ) here ↦ here* ρ δ
    {-# REWRITE Pos-elim-here-β #-}

    Pos-elim-there-β : ∀ {ℓ}
      → (P : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο) (p : Pos ρ) → Type ℓ)
      → (this* : P objₒ this)
      → (here* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
               → (δ : (p : Pos ρ) → Branch (Typ ρ p))
               → P (ndₒ ρ δ) here)
      → (there* : {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
                → (δ : (p : Pos ρ) → Branch (Typ ρ p))
                → (p : Pos ρ) (q : Pos (br (δ p)))
                → P (ndₒ ρ δ) (there p q))
      → {n : ℕ} {ο : 𝕆 n} (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → Branch (Typ ρ p))
      → (p : Pos ρ) (q : Pos (br (δ p)))
      → Pos-elim P this* here* there* (ndₒ ρ δ) (there p q) ↦ there* ρ δ p q 
    {-# REWRITE Pos-elim-there-β #-}
      
  --
  --  Typing 
  --

  Typ = Pos-elim (λ {n} ρ p → 𝕆 n)
    ■
    (λ ρ δ → _ ∣ ρ)
    (λ ρ δ p q → Typ (br (δ p)) q)

  ηₒ = 𝕆-elim ℙ
    objₒ
    (λ ο ρ → ndₒ ρ (λ p → ⟨ lfₒ (Typ ρ p) ⟩))
    
  -- ηₒ ● = objₒ
  -- ηₒ (ο ∣ ρ) = ndₒ ρ (λ p → ⟨ lfₒ (Typ ρ p) ⟩)

  -- η-posₒ = {!!} 
  -- η-posₒ ● = this
  -- η-posₒ (ο ∣ ρ) = here
  
