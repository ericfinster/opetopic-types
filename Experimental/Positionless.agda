--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.Positionless where

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)

  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ
  
  Src : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → Frm Xₙ → Type ℓ 

  smap : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → {Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ}
    → (σ : (f : Frm Xₙ) → Xₛₙ f → Xₛₙ' f)
    → {f : Frm Xₙ}
    → Src Xₙ Xₛₙ f → Src Xₙ Xₛₙ' f 

  η : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ}
    → (x : Xₛₙ f) → Src Xₙ Xₛₙ f 

  postulate
  
    μ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → {f : Frm Xₙ}
      → Src Xₙ (Src Xₙ Xₛₙ) f
      → Src Xₙ Xₛₙ f 

  postulate

    smap-id : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → {Xₛₙ : Frm Xₙ → Type ℓ}
      → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
      → smap Xₙ (λ f x → x) s ↦ s
    {-# REWRITE smap-id #-} 
      
    smap-∘ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → {Xₛₙ Xₛₙ' Xₛₙ'' : Frm Xₙ → Type ℓ}
      → (σ : (f : Frm Xₙ) → Xₛₙ f → Xₛₙ' f)
      → (σ' : (f : Frm Xₙ) → Xₛₙ' f → Xₛₙ'' f)
      → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
      → smap Xₙ σ' (smap Xₙ σ s) ↦ smap Xₙ (λ f x → σ' f (σ f x)) s
    {-# REWRITE smap-∘ #-}

    unit-right : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ (η Xₙ (Src Xₙ Xₛₙ) pd) ↦ pd
    {-# REWRITE unit-right #-}

    unit-left : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ (smap Xₙ (λ f x → η Xₙ Xₛₙ x) pd) ↦ pd
    {-# REWRITE unit-left #-}

    μ-assoc : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (t : Src Xₙ (Src Xₙ (Src Xₙ Xₛₙ)) f)
      → μ Xₙ Xₛₙ (smap Xₙ (λ f → μ Xₙ Xₛₙ {f}) t) ↦ μ Xₙ Xₛₙ (μ Xₙ (Src Xₙ Xₛₙ) t) 
    {-# REWRITE μ-assoc #-} 
  

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ Xₙ ∈ 𝕆Type n ℓ ]
    ((f : Frm Xₙ) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (Xₙ , Xₛₙ) = 
    Σ[ f ∈ Frm Xₙ ]
    Σ[ tgt ∈ Xₛₙ f ] 
    Src Xₙ Xₛₙ f

  {-# NO_POSITIVITY_CHECK #-}
  data Pd {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ) (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ) : Frm (Xₙ , Xₛₙ) → Type ℓ where

    lf : (f : Frm Xₙ) (tgt : Xₛₙ f)
      → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , η Xₙ Xₛₙ tgt) 

    nd : (f : Frm Xₙ) (tgt : Xₛₙ f)
    
      → (ih : Src Xₙ (λ f' →
          Σ[ tgt' ∈ Xₛₙ f' ]
          Σ[ lvs ∈ Src Xₙ Xₛₙ f' ]
          Pd Xₙ Xₛₙ Xₛₛₙ (f' , tgt' , lvs)) f)

      -- the map picks out the target of the subtrees...
      → (filler : Xₛₛₙ (f , tgt , smap Xₙ (λ _ → fst) ih))

      -- pick out the "leaves" of each subtree 
      → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ _ → fst ∘ snd) ih))

  Src {zero} X Y f = Y tt*
  Src {suc n} (Xₙ , Xₛₙ) Xₛₛₙ = Pd Xₙ Xₛₙ Xₛₛₙ

  {-# TERMINATING #-}
  smap {zero} Xₙ {Xₛₙ} {Xₛₙ'} σ s = σ tt* s
  smap {suc n} Xₙ {Xₛₙ} {Xₛₙ'} σ (lf _ tgt) = lf _ tgt
  smap {suc n} (Xₙ , Xₛₙ) {Xₛₛₙ} {Xₛₛₙ'} σ (nd f tgt ih filler) = nd f tgt ih' (σ _ filler)

    where ih' : Src Xₙ (λ f' → Σ[ τ' ∈ Xₛₙ f' ]
                               Σ[ σ' ∈ Src Xₙ Xₛₙ f' ]
                                 Pd Xₙ Xₛₙ Xₛₛₙ' (f' , τ' , σ')) f
          ih' = smap Xₙ (λ f τσρ → fst τσρ , fst (snd τσρ) , smap (Xₙ , Xₛₙ) σ (snd (snd τσρ))) ih 

  η {zero} Xₙ Xₛₙ {tt*} x = x
  η {suc n} (Xₙ , Xₛₙ) Xₛₛₙ {f , t , s} x = nd f t ih' x

    where ih' : Src Xₙ (λ f' → Σ[ τ' ∈ Xₛₙ f' ]
                               Σ[ σ' ∈ Src Xₙ Xₛₙ f' ]
                                 Pd Xₙ Xₛₙ Xₛₛₙ (f' , τ' , σ')) f
          ih' = smap Xₙ (λ f x' → x' , η Xₙ Xₛₙ x' , lf f x') s 

  -- μ = {!!} 
