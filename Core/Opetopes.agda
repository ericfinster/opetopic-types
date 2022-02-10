--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat 
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum 

open import Core.Prelude

module Core.Opetopes where

  --
  --  The Opetopic Polynomials
  --

  {-# TERMINATING #-}
  
  𝒪 : ℕ → Type
  𝒫 : {n : ℕ} → 𝒪 n → Type
  Pos : {n : ℕ} {o : 𝒪 n} → 𝒫 o → Type 
  Typ : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o) (p : Pos 𝑝) → 𝒪 n

  --
  --  Decorations and the extensions
  --
  
  Decₒ : ∀ {n ℓ} (X : 𝒪 n → Type ℓ) {𝑜 : 𝒪 n} → 𝒫 𝑜 → Type ℓ
  Decₒ X 𝑝 = (p : Pos 𝑝) → X (Typ 𝑝 p) 

  ⟦_⟧ₒ : ∀ {n ℓ} (P : 𝒪 n → Type ℓ) → 𝒪 n → Type ℓ
  ⟦ P ⟧ₒ 𝑜 = Σ (𝒫 𝑜) (Decₒ P) 

  --
  --  Monadic signature
  --

  ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o

  ηₒ-pos : {n : ℕ} (o : 𝒪 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : ∀ {ℓ} {n : ℕ} (o : 𝒪 n)
    → (X : (p : Pos (ηₒ o)) → Type ℓ)
    → (ηₒ-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

  μₒ : {n : ℕ} {o : 𝒪 n} → ⟦ 𝒫 ⟧ₒ o → 𝒫 o

  pairₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
    → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
    → Pos (μₒ 𝑝)

  fstₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
    → Pos (μₒ 𝑝) → Pos (fst 𝑝)

  sndₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
    → (p : Pos (μₒ 𝑝)) → Pos (snd 𝑝 (fstₚ 𝑝 p))
      
  -- 
  --  Monadic Laws
  --
  
  postulate
  
    -- ηₒ-pos laws
    ηₒ-pos-typ : {n : ℕ} (o : 𝒪 n)
      → (p : Pos (ηₒ o))
      → Typ (ηₒ o) p ↦ o
    {-# REWRITE ηₒ-pos-typ #-}

    ηₒ-pos-elim-β : ∀ {ℓ} {n : ℕ} (o : 𝒪 n)
      → (X : (p : Pos (ηₒ o)) → Type ℓ)
      → (ηₒ-pos* : X (ηₒ-pos o))
      → ηₒ-pos-elim o X ηₒ-pos* (ηₒ-pos o) ↦ ηₒ-pos*
    {-# REWRITE ηₒ-pos-elim-β #-}

    -- pairₚ laws
    fstₚ-β : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
      → fstₚ 𝑝 (pairₚ 𝑝 p q) ↦ p
    {-# REWRITE fstₚ-β #-}

    sndₚ-β : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
      → sndₚ 𝑝 (pairₚ 𝑝 p q) ↦ q
    {-# REWRITE sndₚ-β #-}
    
    pairₚ-ηₒ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (μₒ 𝑝))
      → pairₚ 𝑝 (fstₚ 𝑝 p) (sndₚ 𝑝 p) ↦ p
    {-# REWRITE pairₚ-ηₒ #-}

    pairₚ-typ : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (p : Pos (μₒ 𝑝))
      → Typ (μₒ 𝑝) p ↦ Typ (snd 𝑝 (fstₚ 𝑝 p)) (sndₚ 𝑝 p)
    {-# REWRITE pairₚ-typ #-}

  postulate

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) ↦ 𝑝
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → μₒ (ηₒ 𝑜 , ϕ) ↦ ϕ (ηₒ-pos 𝑜)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → μₒ (μₒ 𝑝 , ε) ↦ μₒ (fst 𝑝 , λ p → μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)))
    {-# REWRITE μₒ-assoc #-}

    -- intro compatibilities
    pairₚ-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos 𝑝) (q : Pos (ηₒ (Typ 𝑝 p)))
      → pairₚ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p q ↦ p
    {-# REWRITE pairₚ-unit-r #-}

    pairₚ-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → (q : Pos (ϕ (ηₒ-pos 𝑜)))
      → pairₚ (ηₒ 𝑜 , ϕ) (ηₒ-pos 𝑜) q ↦ q 
    {-# REWRITE pairₚ-unit-l #-}

    pairₚ-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → (pq : Pos (μₒ 𝑝)) (r : Pos (ε pq))
      → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q))
            p = fstₚ 𝑝 pq
            q = sndₚ 𝑝 pq
        in pairₚ (μₒ 𝑝 , ε) pq r
          ↦ pairₚ (fst 𝑝 , ε')
              p (pairₚ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)) q r)
    {-# REWRITE pairₚ-assoc #-} 

    -- first projection compatibilities
    μₒ-fst-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos (μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p))))
      → fstₚ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p ↦ p
    {-# REWRITE μₒ-fst-unit-r #-}

    μₒ-fst-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → (p : Pos (μₒ (ηₒ 𝑜 , ϕ)))
      → fstₚ (ηₒ 𝑜 , ϕ) p ↦ ηₒ-pos 𝑜
    {-# REWRITE μₒ-fst-unit-l #-}

    μₒ-fst-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → (pqr : Pos (μₒ (μₒ 𝑝 , ε)))
      → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q))
            p = fstₚ (fst 𝑝 , ε') pqr
            qr = sndₚ (fst 𝑝 , ε') pqr
            q = fstₚ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)) qr
        in fstₚ (μₒ 𝑝 , ε) pqr ↦ pairₚ 𝑝 p q
    {-# REWRITE μₒ-fst-assoc #-}

    -- second projection compatibilities
    μₒ-snd-unit-r : {n : ℕ} {o : 𝒪 n} (𝑝 : 𝒫 o)
      → (p : Pos (μₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p))))
      → sndₚ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) p ↦ ηₒ-pos (Typ 𝑝 p)
    {-# REWRITE μₒ-snd-unit-r #-}

    μₒ-snd-unit-l : {n : ℕ} {𝑜 : 𝒪 n}
      → (ϕ : Decₒ 𝒫 (ηₒ 𝑜))
      → (p : Pos (μₒ (ηₒ 𝑜 , ϕ)))
      → sndₚ (ηₒ 𝑜 , ϕ) p ↦ p 
    {-# REWRITE μₒ-snd-unit-l #-}

    μₒ-snd-assoc : {n : ℕ} {o : 𝒪 n} 
      → (𝑝 : ⟦ 𝒫 ⟧ₒ o) (ε : Decₒ 𝒫 (μₒ 𝑝))
      → (pqr : Pos (μₒ (μₒ 𝑝 , ε)))
      → let ε' p = μₒ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q))
            p = fstₚ (fst 𝑝 , ε') pqr
            qr = sndₚ (fst 𝑝 , ε') pqr
        in sndₚ (μₒ 𝑝 , ε) pqr ↦ sndₚ (snd 𝑝 p , λ q → ε (pairₚ 𝑝 p q)) qr
    {-# REWRITE μₒ-snd-assoc #-}

  --
  --  Trees and Positions
  --
  
  {-# NO_POSITIVITY_CHECK #-}
  
  data 𝒯r {n : ℕ} {𝑜 : 𝒪 n} : (𝑝 : 𝒫 𝑜) → Type where
  
    lfₒ : 𝒯r (ηₒ 𝑜)
    
    ndₒ : (𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜)
      → (ε : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → 𝒯r {n} {𝑜} (μₒ 𝑝)

  data 𝒯rPos {n : ℕ} {𝑜 : 𝒪 n} : {𝑝 : 𝒫 𝑜} (𝑡 : 𝒯r 𝑝) → Type where
  
    here : {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜}
      → {ε : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p)}
      → 𝒯rPos (ndₒ 𝑝 ε)

    there : {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜}
      → {ε : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p)}
      → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ε p))
      → 𝒯rPos (ndₒ 𝑝 ε)

  --
  --  Grafting 
  --
  
  graftₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → 𝒯r (μₒ 𝑝)
  graftₒ lfₒ ψ = ψ (ηₒ-pos _)
  graftₒ {𝑝 = ._ , ϕ} (ndₒ (𝑝 , 𝑑) ε) ψ =
    ndₒ (𝑝 , λ p → μₒ (𝑑 p , λ q → ϕ (pairₚ (𝑝 , 𝑑) p q)))
        (λ p → graftₒ (ε p) (λ q → ψ (pairₚ (𝑝 , 𝑑) p q)))

  inlₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → 𝒯rPos 𝑡 → 𝒯rPos (graftₒ 𝑡 ψ)
  inlₒ (ndₒ 𝑝 ε) ψ here = here
  inlₒ {𝑝 = ._ , ϕ} (ndₒ (𝑝 , 𝑑) ε) ψ (there u v) = 
    there u (inlₒ (ε u) (λ q → ψ (pairₚ (𝑝 , 𝑑) u q)) v)

  inrₒ : {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p))
    → 𝒯rPos (graftₒ 𝑡 ψ)
  inrₒ {𝑜 = 𝑜} lfₒ ψ =
    ηₒ-pos-elim 𝑜 (λ p → 𝒯rPos (ψ p) → 𝒯rPos (ψ (ηₒ-pos 𝑜))) (λ p → p) 
  inrₒ (ndₒ 𝑝 ε) ψ u v = 
    let u₀ = fstₚ 𝑝 u
        u₁ = sndₚ 𝑝 u
    in there u₀ (inrₒ (ε u₀) (λ q → ψ (pairₚ 𝑝 u₀ q)) u₁ v)

  graftₒ-pos-elim : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
    → (𝑡 : 𝒯r (fst 𝑝))
    → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
    → (X : 𝒯rPos (graftₒ 𝑡 ψ) → Type ℓ)
    → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
    → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
    → (p : 𝒯rPos (graftₒ 𝑡 ψ)) → X p
  graftₒ-pos-elim lfₒ ψ X inl* inr* p = inr* (ηₒ-pos _) p
  graftₒ-pos-elim (ndₒ 𝑝 ε) ψ X inl* inr* here = inl* here
  graftₒ-pos-elim (ndₒ 𝑝 ε) ψ X inl* inr* (there u v) = 
    graftₒ-pos-elim (ε u) (λ q → ψ (pairₚ 𝑝 u q)) 
      (λ q → X (there u  q))
      (λ q → inl* (there u q))
      (λ p q → inr* (pairₚ 𝑝 u p) q) v
      
  --
  --  Grafting Laws
  --

  postulate

    graftₒ-pos-elim-inl-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
      → (𝑡 : 𝒯r (fst 𝑝))
      → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → (X : 𝒯rPos (graftₒ 𝑡 ψ) → Type ℓ)
      → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
      → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
      → (p : 𝒯rPos 𝑡)
      → graftₒ-pos-elim 𝑡 ψ X inl* inr* (inlₒ 𝑡 ψ p) ↦ inl* p
    {-# REWRITE graftₒ-pos-elim-inl-β #-}

    graftₒ-pos-elim-inr-β : ∀ {ℓ} {n : ℕ} {𝑜 : 𝒪 n} {𝑝 : ⟦ 𝒫 ⟧ₒ 𝑜} 
      → (𝑡 : 𝒯r (fst 𝑝))
      → (ψ : (p : Pos (fst 𝑝)) → 𝒯r (snd 𝑝 p))
      → (X : 𝒯rPos (graftₒ 𝑡 ψ) → Type ℓ)
      → (inl* : (p : 𝒯rPos 𝑡) → X (inlₒ 𝑡 ψ p))
      → (inr* : (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p)) → X (inrₒ 𝑡 ψ p q))
      → (p : Pos (fst 𝑝)) (q : 𝒯rPos (ψ p))
      → graftₒ-pos-elim 𝑡 ψ X inl* inr* (inrₒ 𝑡 ψ p q) ↦ inr* p q
    {-# REWRITE graftₒ-pos-elim-inr-β #-}

    -- TODO : More grafting laws...

  --
  --  Polynomial Implementations
  --

  𝒪 zero = Unit
  𝒪 (suc n) = Σ (𝒪 n) 𝒫

  𝒫 {zero} _ = Unit
  𝒫 {suc n} (𝑜 , 𝑝) = 𝒯r {𝑜 = 𝑜} 𝑝
  
  Pos {zero} _ = Unit
  Pos {suc n}  = 𝒯rPos 
  
  Typ {zero} _ _ = tt
  Typ {suc n} ._ (here {𝑝 , _}) = _ , 𝑝
  Typ {suc n} ._ (there {ε = ε} p q) = Typ (ε p) q

  --
  --  Monadic Implementations
  --

  -- ηₒ : {n : ℕ} (o : 𝒪 n) → 𝒫 o
  ηₒ {zero} _ = tt
  ηₒ {suc n} (o , 𝑝) =
    ndₒ (𝑝 , λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ)

  -- ηₒ-pos : {n : ℕ} (o : 𝒪 n)
  --   → Pos (ηₒ o)
  ηₒ-pos {zero} _ = tt
  ηₒ-pos {suc n} (o , 𝑝) = here

  -- ηₒ-pos-elim : {n : ℕ} (o : 𝒪 n)
  --   → (X : (p : Pos (ηₒ o)) → Type)
  --   → (ηₒ-pos* : X (ηₒ-pos o))
  --   → (p : Pos (ηₒ o)) → X p
  ηₒ-pos-elim {n = zero} o X ηₒ-pos* tt = ηₒ-pos*
  ηₒ-pos-elim {n = suc n} o X ηₒ-pos* here = ηₒ-pos*

  -- μₒ : {n : ℕ} {o : 𝒪 n} → ⟦ 𝒫 ⟧ₒ o → 𝒫 o
  μₒ {zero} (𝑝 , 𝑑) = tt
  μₒ {suc n} (lfₒ , 𝑑) = lfₒ
  μₒ {suc n} (ndₒ 𝑝 ε , 𝑑) =
    let 𝑡 = 𝑑 here
        Ψ p = μₒ (ε p , λ q → 𝑑 (there p q))
    in graftₒ 𝑡 Ψ

  -- pairₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  --   → (p : Pos (fst 𝑝)) (q : Pos (snd 𝑝 p))
  --   → Pos (μₒ 𝑝)
  pairₚ {zero} (𝑝 , 𝑑) p q = tt
  pairₚ {suc n} (ndₒ 𝑝 ε , 𝑑) here r = 
    let 𝑡 = 𝑑 here
        Ψ p = μₒ (ε p , λ q → 𝑑 (there p q))
    in inlₒ 𝑡 Ψ r  
  pairₚ {suc n} (ndₒ 𝑝 ε , 𝑑) (there p q) r =
    let 𝑡 = 𝑑 here
        Ψ p = μₒ (ε p , λ q → 𝑑 (there p q))
    in inrₒ 𝑡 Ψ p (pairₚ (ε p , λ q → 𝑑 (there p q)) q r) 

  -- fstₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  --   → Pos (μₒ 𝑝) → Pos (fst 𝑝)
  fstₚ {zero} (𝑝 , 𝑑) p = tt
  fstₚ {suc n} (ndₒ 𝑝 ε , 𝑑) = 
    let 𝑡 = 𝑑 here
        Ψ p = μₒ (ε p , λ q → 𝑑 (there p q))
    in graftₒ-pos-elim 𝑡 Ψ _ (const here)
         (λ p q → there p (fstₚ (ε p , λ q → 𝑑 (there p q)) q))

  -- sndₚ : {n : ℕ} {o : 𝒪 n} (𝑝 : ⟦ 𝒫 ⟧ₒ o)
  --   → (p : Pos (μₒ 𝑝)) → Pos (snd 𝑝 (fstₚ 𝑝 p))
  sndₚ {zero} (𝑝 , 𝑑) p = tt
  sndₚ {suc n} (ndₒ 𝑝 ε , 𝑑) = 
    let 𝑡 = 𝑑 here
        Ψ p = μₒ (ε p , λ q → 𝑑 (there p q))
    in graftₒ-pos-elim 𝑡 Ψ _ (λ p → p)
         (λ p q → sndₚ (ε p , λ q → 𝑑 (there p q)) q)

  --
  --  Examples
  --

  obj : 𝒪 0
  obj = tt

  arrow : 𝒪 1
  arrow = tt , tt

  2-drop : 𝒪 2
  2-drop = (tt , tt) , lfₒ 

  2-globe : 𝒪 2
  2-globe = (tt , tt) , ndₒ (tt , λ _ → tt) (λ _ → lfₒ)

  2-simplex : 𝒪 2
  2-simplex = (tt , tt) , ndₒ (tt , λ _ → tt) (λ p → ndₒ (tt , λ _ → tt) (λ _ → lfₒ))
