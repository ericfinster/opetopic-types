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
    → (ο : 𝕆 n) (f : Frm X ο)
    → (ρ : ℙ n ο) → Type ℓ

  Shp : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ n ο} (s : Web X ο f ρ)
    → (p : Pos n ο ρ) → Frm X (Typ n ο ρ p)

  postulate
  
    --
    --  Monadic Structure
    --

    η : ∀ {ℓ n} (X : 𝕆Type ℓ n) 
      → (P : {ο : 𝕆 n} → Frm X ο → Type ℓ)
      → (ο : 𝕆 n) (f : Frm X ο)
      → Web X ο f (ηₒ n ο) 

    μ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → (P : {ο : 𝕆 n} → Frm X ο → Type ℓ)
      → (ο : 𝕆 n) (f : Frm X ο)
      → (ρ : ℙ n ο) (s : Web X ο f ρ)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (σ : (p : Pos n ο ρ) → Web X (Typ n ο ρ p) (Shp X s p) (δ p))
      → Web X ο f (μₒ n ο ρ δ) 

  --
  --  Equations
  --

  postulate

    Shp-η : ∀ {ℓ n} (X : 𝕆Type ℓ n) 
      → (P : {ο : 𝕆 n} → Frm X ο → Type ℓ)
      → (ο : 𝕆 n) (f : Frm X ο)
      → (p : Pos n ο (ηₒ n ο))
      → Shp X (η X P ο f) p ↦ f 
    {-# REWRITE Shp-η #-}      
    
    Shp-μ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → (P : {ο : 𝕆 n} → Frm X ο → Type ℓ)
      → (ο : 𝕆 n) (f : Frm X ο)
      → (ρ : ℙ n ο) (s : Web X ο f ρ)
      → (δ : (p : Pos n ο ρ) → ℙ n (Typ n ο ρ p))
      → (σ : (p : Pos n ο ρ) → Web X (Typ n ο ρ p) (Shp X s p) (δ p))
      → (p : Pos n ο (μₒ n ο ρ δ))
      → Shp X (μ X P ο f ρ s δ σ) p ↦
        Shp X (σ (fstₒ n ο ρ δ p)) (sndₒ n ο ρ δ p)
    {-# REWRITE Shp-μ #-} 

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

      pd : ℙ n (fst i)
      web : Web X (fst i) (snd i) pd
      dec : (p : Pos n (fst i) pd)
          → P (Typ n (fst i) pd p ,
               Shp X web p)

  open Src 

  ret : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → (i : Idx X) → P i → Src X P i
  ret {n = n} X P (ο , f) x =
    ⟪ ηₒ n ο , η X (λ f → P (_ , f)) ο f , (λ _ → x) ⟫
    
  join : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → (i : Idx X) → Src X (Src X P) i → Src X P i
  join X P (ο , f) ⟪ ρ , ω , δ ⟫  =
    ⟪ μₒ _ ο ρ (λ p → pd (δ p))
    , μ X (λ f → P (_ , f)) ο f ρ ω (λ p → pd (δ p)) (λ p → web (δ p)) 
    , (λ p → dec (δ (fstₒ _ ο ρ (λ p → pd (δ p)) p)) (sndₒ _ ο ρ (λ p → pd (δ p)) p))
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
    Σ[ s ∈ Web X ο f ρ ]
    Σ[ δ ∈ ((p : Pos n ο ρ) → P (Typ n ο ρ p , Shp X s p)) ] 
    P (ο , f)

  record FramedPd {ℓ n} (X : 𝕆Type ℓ n)
    (P : Idx X → Type ℓ)
    (i : Idx X) : Type ℓ where
    inductive 
    constructor ⟦_,_,_,_⟧
    field

      lvs : Src X P i
      stm : P i
      tr : Tr n (fst i , pd lvs)
      trnk : Web (X , P) (fst i , pd lvs)
             (snd i , web lvs , dec lvs , stm) tr 

  open FramedPd
  
  canopy : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → (i : Idx X) → Src X (FramedPd X P) i → Src X P i
  canopy {n = n} X P (ο , f) ⟪ ρ , ω , δ ⟫  =
    join X P (ο , f) ⟪ ρ , ω , (λ p → lvs (δ p)) ⟫ 

  data Pd {ℓ n} (X : 𝕆Type ℓ n)
      (P : Idx X → Type ℓ)
    : (i : Idx X) (s : Src X P i) → P i
    → Tr n (fst i , pd s) → Type ℓ where

    lf : (i : Idx X) (x : P i)
       →  Pd X P i (ret X P i x) x
         (lfₒ (fst i))  

    nd : {i : Idx X} (x : P i)
       → (s : Src X (FramedPd X P) i)
       → Pd X P i (canopy X P i s) x
         (ndₒ (fst i) (pd s) (λ p → pd (lvs (dec s p)))
                             (λ p → tr (dec s p)))

  Web {ℓ} {n = zero} X ο f ρ = 𝟙 ℓ
  Web {ℓ} {n = suc n} (X , P) (ο , ρ) (f , ω , δ , x) τ = 
    Pd X P (ο , f) ⟪ ρ , ω , δ ⟫  x τ
  
  Shp {n = zero} X ω p = ●
  Shp {n = suc n} (X , P) (nd x σ) nd-hereₒ = _ , web σ , (λ p → stm (dec σ p)) , x
  Shp {n = suc n} (X , P) (nd x σ) (nd-thereₒ p q) = Shp (X , P) (trnk (dec σ p)) q

  -- η = {!!} 
  -- μ = {!!} 
