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
    unit-left : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ (η Xₙ (Src Xₙ Xₛₙ) pd) ↦ pd
    {-# REWRITE unit-left #-}

    unit-right : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ (smap Xₙ (λ f → η Xₙ Xₛₙ) pd) ↦ pd
    {-# REWRITE unit-right #-}

    {-unit-right : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pdpd : Src Xₙ (Src Xₙ Xₛₙ) f)
      → η Xₙ (Src Xₙ Xₛₙ) (μ Xₙ Xₛₙ pdpd) ↦ pdpd
    {-# REWRITE unit-right #-}-} ------------------- I don't think that's really "unit-right". Not sure what it is though.

    μ-assoc : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (pd : Src Xₙ (Src Xₙ (Src Xₙ Xₛₙ)) f)
      → μ Xₙ Xₛₙ (μ Xₙ (Src Xₙ Xₛₙ) pd) ↦ μ Xₙ Xₛₙ (smap Xₙ (λ f → μ Xₙ Xₛₙ) pd) -- The two ways to compose Src∘Src∘Src → Src using μ coincide
    {-# REWRITE μ-assoc #-}

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
    




  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ Xₙ ∈ 𝕆Type n ℓ ]
    ((f : Frm Xₙ) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (Xₙ , Xₛₙ) = 
    Σ[ f ∈ Frm Xₙ ]
    Σ[ tgt ∈ Xₛₙ f ] 
    Src Xₙ Xₛₙ f

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

  smap {zero} tt* σ = σ _
  smap {suc n} Xₙ σ (lf f tgt) = lf f tgt
  smap {suc n} (Xₙ , Xₛₙ) σ (nd f tgt ih filler) = {!!}

  η {zero} Xₙ Xₛₙ {f} x = x
  η {suc n} (Xₙ , Xₛₙ) Xₛₛₙ {f} x = {!!}

  μ = {!!} 

  -- smap {zero} X {Y} {Z} σ f y = σ tt* y
  -- smap {suc n} X {Y} {Z} σ ._ (lf f x) = lf f x
  -- smap {suc n} X {Y} {Z} σ ._ (nd f s t y) = {!!} -- nd f s' t z

  --   -- And as expected, we see that we need to definitionally combine two
  --   -- functions here in order for this to typecheck....

  --   where z : Z (f , t , smap (fst X) (λ _ → fst) f s)
  --         z = σ _ y

  --         Z' : Frm (fst X) → Type _
  --         Z' f' = Σ[ τ' ∈ snd X f' ]
  --                 Σ[ σ' ∈ Src (fst X) (snd X) f' ]
  --                 Pd X Z (f' , τ' , σ')

  --         s' : Src (fst X) Z' _
  --         s' = smap (fst X) {Z = Z'} (λ f' (a , b , c) → a , b , smap X {Y} {Z} σ _ c) _ s
