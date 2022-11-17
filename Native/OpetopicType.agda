open import Core.Prelude
open import Native.Opetopes

module Native.OpetopicType where

  --
  --  Signature 
  --
  
  𝕆Type : (ℓ : Level) (n : ℕ)
    → Type (ℓ-suc ℓ)

  Frm : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → 𝕆 n → Type ℓ

  Web : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → {ο : 𝕆 n} (f : Frm X ο)
    → (ρ : ℙ ο) → Type ℓ

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

  Idx : ∀ {ℓ n} → 𝕆Type ℓ n → Type ℓ
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

  open Src 

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
                 (sndₒ (pd s) (λ p → pd (dec s p)) p)) 
    ⟫ 

  --
  --  Implementation 
  --
  
  𝕆Type ℓ zero = 𝟙 (ℓ-suc ℓ)
  𝕆Type ℓ (suc n) =
    Σ[ X ∈ 𝕆Type ℓ n ]
    (Idx X → Type ℓ)
  
  Frm {ℓ} {n = zero} X ο = 𝟙 ℓ
  Frm {ℓ} {n = suc n} (X , P) (ο , ρ) = 
    Σ[ f ∈ Frm X ο ]
    Σ[ s ∈ Web X f ρ ]
    Σ[ δ ∈ ((p : Pos ρ) → P (Typ ρ p , Shp X s p)) ] 
    P (ο , f)

  record CappedPd {ℓ n} (X : 𝕆Type ℓ n)
    (P : Idx X → Type ℓ)
    {i : Idx X} (t : P i) : Type ℓ where
    inductive 
    constructor ⟦_⟧
    field

      {lvs} : Src X P i
      {tr} : Tr (fst i , pd lvs)
      trnk : Web (X , P) (snd i , web lvs , dec lvs , t) tr 

  open CappedPd

  data Pd {ℓ n} (X : 𝕆Type ℓ n)
      (P : Idx X → Type ℓ)
    : (i : Idx X) (s : Src X P i) (x : P i)
    → Tr (fst i , pd s) → Type ℓ where

    lf : {i : Idx X} (t : P i)
       →  Pd X P i (ret X P t) t
            (lfₒ (fst i))  

    nd : {i : Idx X} (t : P i) (s : Src X P i)
       → (δ : (p : Pos (pd s)) → CappedPd X P (dec s p))
       → Pd X P i (join X P ⟪ web s , (λ p → lvs (δ p)) ⟫) t
           (ndₒ (pd s) (λ p → pd (lvs (δ p)) , tr (δ p)))

  Web {ℓ} {n = zero} X f ρ = 𝟙 ℓ
  Web {ℓ} {n = suc n} (X , P) {ο , ρ} (f , ω , δ , t) τ = 
    Pd X P (ο , f) ⟪ ω , δ ⟫ t τ

  Shp {n = zero} X ω p = ●
  Shp {n = suc n} (X , P) (nd t s δ) here = _ , web s , dec s , t
  Shp {n = suc n} (X , P) (nd t s δ) (there p q) = Shp (X , P) (trnk (δ p)) q

  η {n = zero} X f = ●
  η {n = suc n} (X , P) (f , ω , δ , t) =
    nd t ⟪ ω , δ ⟫ (λ p → ⟦ lf (δ p) ⟧)

  γ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} {s : Src X P i} {t : P i}
    → {τ : Tr (fst i , pd s)}
    → (m : Pd X P i s t τ)
    → (ϕ : (p : Pos (pd s)) → CappedPd X P (dec s p))
    → Pd X P i (join X P ⟪ web s , (λ p → lvs (ϕ p)) ⟫) t (γₒ τ (λ p → pd (lvs (ϕ p)) , (tr (ϕ p))))
  γ X P (lf t) ϕ = trnk (ϕ (η-posₒ _))
  γ X P (nd t s δ) ϕ = nd t s (λ p → ⟦ γ X P (trnk (δ p)) (λ q → ϕ (pairₒ (pd s) (λ r → pd (lvs (δ r))) p q)) ⟧) 

  μ {n = zero} X s ϵ = ●
  μ {n = suc n} (X , P) (lf t) ϵ = lf t
  μ {n = suc n} (X , P) (nd t s δ) ϵ =
    γ X P (ϵ here) (λ p → ⟦ μ (X , P) (trnk (δ p)) (λ q → ϵ (there p q)) ⟧)
