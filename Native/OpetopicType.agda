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
    constructor ⟪_,_,_⟫ 
    field

      pd : ℙ (fst i)
      web : Web X (snd i) pd
      dec : (p : Pos pd) → P (Typ pd p , Shp X web p)

  open Src 

  ret : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → P i → Src X P i
  ret {n = n} X P {ο , f} x =
    ⟪ ηₒ ο , η X f , cst x ⟫
    
  join : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → Src X (Src X P) i → Src X P i
  join X P ⟪ ρ , ω , δ ⟫  =
    ⟪ μₒ ρ (λ p → pd (δ p))
    , μ X ω (λ p → web (δ p)) 
    , (λ p → dec (δ (fstₒ ρ (λ p → pd (δ p)) p))
                 (sndₒ ρ (λ p → pd (δ p)) p)) 
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

  record FramedPd {ℓ n} (X : 𝕆Type ℓ n)
    (P : Idx X → Type ℓ)
    (i : Idx X) : Type ℓ where
    inductive 
    constructor ⟦_,_,_,_⟧
    field

      lvs : Src X P i
      stm : P i
      tr : Tr (fst i , pd lvs)
      trnk : Web (X , P) (snd i , web lvs , dec lvs , stm) tr 

  open FramedPd
  
  canopy : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} → Src X (FramedPd X P) i → Src X P i
  canopy {n = n} X P ⟪ ρ , ω , δ ⟫  =
    join X P ⟪ ρ , ω , (λ p → lvs (δ p)) ⟫ 

  data Pd {ℓ n} (X : 𝕆Type ℓ n)
      (P : Idx X → Type ℓ)
    : (i : Idx X) (s : Src X P i) (x : P i)
    → Tr (fst i , pd s) → Type ℓ where

    lf : {i : Idx X} (x : P i)
       →  Pd X P i (ret X P x) x
            (lfₒ (fst i))  

    nd : {i : Idx X} (x : P i)
       → (s : Src X (FramedPd X P) i)
       → Pd X P i (canopy X P s) x
           (ndₒ (pd s) (λ p → pd (lvs (dec s p)) , tr (dec s p)))

  Web {ℓ} {n = zero} X f ρ = 𝟙 ℓ
  Web {ℓ} {n = suc n} (X , P) {ο , ρ} (f , ω , δ , x) τ = 
    Pd X P (ο , f) ⟪ ρ , ω , δ ⟫  x τ

  Shp {n = zero} X ω p = ●
  Shp {n = suc n} (X , P) (nd x σ) here = _ , web σ , (λ p → stm (dec σ p)) , x
  Shp {n = suc n} (X , P) (nd x σ) (there p q) = Shp (X , P) (trnk (dec σ p)) q

  η {n = zero} X f = ●
  η {n = suc n} (X , P) {ο , ρ} (f , ω , δ , x) = nd x ⟪ ρ , ω , ufpd ⟫  

    where ufpd : (p : Pos ρ) → FramedPd X P (Typ ρ p , Shp X ω p) 
          ufpd p = ⟦ ret X P (δ p) , δ p , lfₒ (Typ ρ p) , lf (δ p) ⟧

  γ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → {i : Idx X} {s : Src X P i} {t : P i}
    → {τ : Tr (fst i , pd s)}
    → (m : Pd X P i s t τ)
    → (n : (p : Pos (pd s)) → Σ[ lvs ∈ Src X P (Typ (pd s) p , Shp X (web s) p) ]
                              Σ[ σ ∈ Tr (Typ (pd s) p , pd lvs) ] 
                              Pd X P (Typ (pd s) p , Shp X (web s) p) lvs (dec s p) σ)
    → Pd X P i (join X P ⟪ pd s , web s , (λ p → fst (n p)) ⟫) t (γₒ τ (λ p → pd (fst (n p)) , (fst (snd (n p)))))
  γ X P (lf t) n = n (η-posₒ _) .snd .snd
  γ X P (nd t s) n =
    nd t ⟪ pd s , _ , (λ p → ⟦ _ , _ , _ , γ X P (trnk (dec s p))
      (λ q → let pq = pairₒ (pd s) (λ r → pd (lvs (dec s r))) p q
             in n pq) ⟧) ⟫

  μ {n = zero} X s ϵ = ●
  μ {n = suc n} (X , P) (lf t) ϵ = lf t
  μ {n = suc n} (X , P) (nd t s) ϵ =
    γ X P (ϵ here) (λ p → _ , _ , μ (X , P) (trnk (dec s p)) (λ q → ϵ (there p q)))
