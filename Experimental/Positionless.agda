{-# OPTIONS --no-positivity-check #-}
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

  Pos : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → (f : Frm Xₙ) (s : Src Xₙ Xₛₙ f)
    → Frm Xₙ → Type ℓ 

  Inhab : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → (f : Frm Xₙ) (s : Src Xₙ Xₛₙ f)
    → (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ f s f')
    → Xₛₙ f' 

  smap : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → {Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ}
    → (σ : (f : Frm Xₙ) → Xₛₙ f → Xₛₙ' f)
    → {f : Frm Xₙ}
    → Src Xₙ Xₛₙ f → Src Xₙ Xₛₙ' f 

  η : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ}
    → (x : Xₛₙ f) → Src Xₙ Xₛₙ f 

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

    η-nat : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → (σ : (f : Frm Xₙ) → Xₛₙ f → Xₛₙ' f)
      → (f : Frm Xₙ) (x : Xₛₙ f)
      → smap Xₙ σ (η Xₙ Xₛₙ x) ↦ η Xₙ Xₛₙ' (σ f x)
    {-# REWRITE η-nat #-}

    μ-nat : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → (σ : (f : Frm Xₙ) → Xₛₙ f → Xₛₙ' f)
      → (f : Frm Xₙ) (pd : Src Xₙ (Src Xₙ Xₛₙ) f)
      → smap Xₙ σ (μ Xₙ Xₛₙ pd) ↦ μ Xₙ Xₛₙ' (smap Xₙ (λ f → smap Xₙ σ) pd)
    {-# REWRITE μ-nat #-}

    unit-left : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ (η Xₙ (Src Xₙ Xₛₙ) pd) ↦ pd
    {-# REWRITE unit-left #-}

    unit-right : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ (smap Xₙ (λ f x → η Xₙ Xₛₙ x) pd) ↦ pd
    {-# REWRITE unit-right #-}

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

  module _ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ)
           (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ) where

    data Pd : Frm (Xₙ , Xₛₙ) → Type ℓ

    record SubPd (f : Frm Xₙ) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        out : Xₛₙ f
        lvs : Src Xₙ Xₛₙ f
        sub : Pd (f , out , lvs)

    open SubPd public
    
    data Pd where

      lf : (f : Frm Xₙ) (tgt : Xₛₙ f)
        → Pd (f , tgt , η Xₙ Xₛₙ tgt) 

      nd : (f : Frm Xₙ) (tgt : Xₛₙ f)
        → (ih : Src Xₙ SubPd f)
        → (filler : Xₛₛₙ (f , tgt , smap Xₙ (λ _ → out) ih))
        → Pd (f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ _ → lvs) ih))

    data NdPos : {f : Frm (Xₙ , Xₛₙ)} → Pd f → Frm (Xₙ , Xₛₙ) → Type ℓ where

       nd-here : (f : Frm Xₙ) (tgt : Xₛₙ f)
               → (ih : Src Xₙ SubPd f)
               → (filler : Xₛₛₙ (f , tgt , smap Xₙ (λ _ → out) ih))
               → NdPos (nd f tgt ih filler) (f , tgt , smap Xₙ (λ _ → out) ih)

       nd-there : (f : Frm Xₙ) (tgt : Xₛₙ f)
                → (ih : Src Xₙ SubPd f)
                → (filler : Xₛₛₙ (f , tgt , smap Xₙ (λ _ → out) ih))
                → (f' : Frm Xₙ) (p : Pos Xₙ SubPd f ih f')
                → (f'' : Frm (Xₙ , Xₛₙ))
                → NdPos (sub (Inhab Xₙ SubPd f ih f' p)) f''
                → NdPos (nd f tgt ih filler) f'' 


  Src {zero} X Y f = Y tt*
  Src {suc n} (Xₙ , Xₛₙ) Xₛₛₙ = Pd Xₙ Xₛₙ Xₛₛₙ

  Pos = {!!} 
  Inhab = {!!} 

  {-# TERMINATING #-}
  smap {zero} Xₙ {Xₛₙ} {Xₛₙ'} σ s = σ tt* s
  smap {suc n} Xₙ {Xₛₙ} {Xₛₙ'} σ (lf _ tgt) = lf _ tgt
  smap {suc n} (Xₙ , Xₛₙ) {Xₛₛₙ} {Xₛₛₙ'} σ (nd f tgt ih filler) = 
    let ih' = smap Xₙ (λ f spd → [ out spd , lvs spd , smap (Xₙ , Xₛₙ) σ (sub spd) ]) ih
    in  nd f tgt ih' (σ _ filler)

  η {zero} Xₙ Xₛₙ {tt*} x = x
  η {suc n} (Xₙ , Xₛₙ) Xₛₛₙ {f , t , s} x = 
    let ih' = smap Xₙ (λ f x' → [ x' , η Xₙ Xₛₙ x' , lf f x' ]) s 
    in nd f t ih' x

  γ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ)
    → (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ)
    → (f : Frm Xₙ) (tgt : Xₛₙ f)
    → (ih : Src Xₙ (SubPd Xₙ Xₛₙ Xₛₛₙ) f)
    → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , smap Xₙ (λ _ → out) ih)
    → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ _ → lvs) ih))

  μ {zero} Xₙ Xₛₙ pd = pd
  μ {suc n} Xₙ Xₛₙ (lf f tgt) = lf f tgt
  μ {suc n} (Xₙ , Xₛₙ) Xₛₛₙ (nd f tgt ih filler) =
    let ih' = smap Xₙ (λ f spd → [ out spd , lvs spd , μ (Xₙ , Xₛₙ) Xₛₛₙ (sub spd) ]) ih  
    in γ Xₙ Xₛₙ Xₛₛₙ f tgt ih' filler

  γ {n} Xₙ Xₛₙ Xₛₛₙ f tgt ih pd = {!!}

