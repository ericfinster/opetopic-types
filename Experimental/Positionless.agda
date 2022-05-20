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
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → Frm Xₙ → Type ℓ 

  {-# TERMINATING #-}
  Inhab : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ s f')
    → Xₛₙ f' 

  η : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (x : Xₛₙ f)
    → Src Xₙ Xₛₙ f 

  η-pos : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (x : Xₛₙ f)
    → Pos Xₙ Xₛₙ (η Xₙ Xₛₙ x) f

  μ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
    → Src Xₙ Xₛₙ' f 

  μ-pos : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
    → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ s f')
    → {f'' : Frm Xₙ} (q : Pos Xₙ Xₛₙ' (ϕ f' p) f'')
    → Pos Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) f''

  μ-fst-frm : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
    → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) f')
    → Frm Xₙ

  μ-fst : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
    → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) f')
    → Pos Xₙ Xₛₙ s (μ-fst-frm Xₙ Xₛₙ Xₛₙ' s ϕ p) 

  μ-snd : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
    → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
    → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
    → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
    → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) f')
    → Pos Xₙ Xₛₙ' (ϕ (μ-fst-frm Xₙ Xₛₙ Xₛₙ' s ϕ p) (μ-fst Xₙ Xₛₙ Xₛₙ' s ϕ p)) f'

  postulate

    Inhab-η : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → {f : Frm Xₙ} (x : Xₛₙ f)
      → (p : Pos Xₙ Xₛₙ (η Xₙ Xₛₙ x) f)
      → Inhab Xₙ Xₛₙ (η Xₙ Xₛₙ x) p ↦ x
    {-# REWRITE Inhab-η #-}

    Inhab-μ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
      → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
      → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) f')
      → Inhab Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) p ↦
        Inhab Xₙ Xₛₙ' (ϕ (μ-fst-frm Xₙ Xₛₙ Xₛₙ' s ϕ p) (μ-fst Xₙ Xₛₙ Xₛₙ' s ϕ p)) (μ-snd Xₙ Xₛₙ Xₛₙ' s ϕ p)
    {-# REWRITE Inhab-μ #-}

    μ-fst-frm-β : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
      → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
      → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ s f')
      → {f'' : Frm Xₙ} (q : Pos Xₙ Xₛₙ' (ϕ f' p) f'')
      → μ-fst-frm Xₙ Xₛₙ Xₛₙ' s ϕ (μ-pos Xₙ Xₛₙ Xₛₙ' s ϕ p q) ↦ f'
    {-# REWRITE μ-fst-frm-β #-} 
      
    μ-fst-β : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
      → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
      → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ s f')
      → {f'' : Frm Xₙ} (q : Pos Xₙ Xₛₙ' (ϕ f' p) f'')
      → μ-fst Xₙ Xₛₙ Xₛₙ' s ϕ (μ-pos Xₙ Xₛₙ Xₛₙ' s ϕ p q) ↦ p
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → {f : Frm Xₙ} (s : Src Xₙ Xₛₙ f)
      → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
      → {f' : Frm Xₙ} (p : Pos Xₙ Xₛₙ s f')
      → {f'' : Frm Xₙ} (q : Pos Xₙ Xₛₙ' (ϕ f' p) f'')
      → μ-snd Xₙ Xₛₙ Xₛₙ' s ϕ (μ-pos Xₙ Xₛₙ Xₛₙ' s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    unit-left : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (x : Xₛₙ f)
      → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ (η Xₙ Xₛₙ x) f') → Src Xₙ Xₛₙ' f')
      → μ Xₙ Xₛₙ Xₛₙ' (η Xₙ Xₛₙ x) ϕ ↦ ϕ f (η-pos Xₙ Xₛₙ x) 
    {-# REWRITE unit-left #-}
    
    unit-right : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (s : Src Xₙ Xₛₙ f)
      → μ Xₙ Xₛₙ Xₛₙ s (λ f p → η Xₙ Xₛₙ (Inhab Xₙ Xₛₙ s p)) ↦ s
    {-# REWRITE unit-right #-}
    
    μ-assoc : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
      → (Xₛₙ Xₛₙ' Xₛₙ'' : Frm Xₙ → Type ℓ)
      → (f : Frm Xₙ) (s : Src Xₙ Xₛₙ f)
      → (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ s f') → Src Xₙ Xₛₙ' f')
      → (ψ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) f') → Src Xₙ Xₛₙ'' f')
      → μ Xₙ Xₛₙ' Xₛₙ'' (μ Xₙ Xₛₙ Xₛₙ' s ϕ) ψ ↦
        μ Xₙ Xₛₙ Xₛₙ'' s (λ f' p → μ Xₙ Xₛₙ' Xₛₙ'' (ϕ f' p) (λ f'' q → ψ f'' (μ-pos Xₙ Xₛₙ Xₛₙ' s ϕ p q)))
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

    record Branch (f : Frm Xₙ) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        stm : Xₛₙ f
        lvs : Src Xₙ Xₛₙ f
        brnch : Pd (f , stm , lvs)

    open Branch public
    
    data Pd where

      lf : {f : Frm Xₙ} (tgt : Xₛₙ f)
         → Pd (f , tgt , η Xₙ Xₛₙ tgt) 

      nd : {f : Frm Xₙ} (tgt : Xₛₙ f)
         → (brs : Src Xₙ Branch f)
         → (flr : Xₛₛₙ (f , tgt , μ Xₙ Branch Xₛₙ brs (λ f p → η Xₙ Xₛₙ (stm (Inhab Xₙ Branch brs p)))))
         → Pd (f , tgt , μ Xₙ Branch Xₛₙ brs (λ f p → lvs (Inhab Xₙ Branch brs p)))

    data NdPos : {f : Frm (Xₙ , Xₛₙ)} → Pd f → Frm (Xₙ , Xₛₙ) → Type ℓ where

      nd-here : {f : Frm Xₙ} {tgt : Xₛₙ f}
              → {brs : Src Xₙ Branch f}
              → {flr : Xₛₛₙ (f , tgt , μ Xₙ Branch Xₛₙ brs (λ f p → η Xₙ Xₛₙ (stm (Inhab Xₙ Branch brs p))))}
              → NdPos (nd tgt brs flr) (f , tgt , μ Xₙ Branch Xₛₙ brs (λ f p → η Xₙ Xₛₙ (stm (Inhab Xₙ Branch brs p))))

      nd-there : {f : Frm Xₙ} {tgt : Xₛₙ f}
               → {brs : Src Xₙ Branch f}
               → {flr : Xₛₛₙ (f , tgt , μ Xₙ Branch Xₛₙ brs (λ f p → η Xₙ Xₛₙ (stm (Inhab Xₙ Branch brs p))))}
               → {f' : Frm Xₙ} (p : Pos Xₙ Branch brs f')
               → {f'' : Frm (Xₙ , Xₛₙ)} (q : NdPos (brnch (Inhab Xₙ Branch brs p)) f'')
               → NdPos (nd tgt brs flr) f''


  Src {zero} X Y f = Y tt*
  Src {suc n} (Xₙ , Xₛₙ) Xₛₛₙ = Pd Xₙ Xₛₙ Xₛₛₙ

  Pos {zero} Xₙ Xₛₙ s f = Lift Unit
  Pos {suc n} (Xₙ , Xₛₙ) Xₛₛₙ = NdPos Xₙ Xₛₙ Xₛₛₙ 

  Inhab {zero} Xₙ Xₛₙ s p = s
  Inhab {suc n} (Xₙ , Xₛₙ) Xₛₛₙ ._ (nd-here {flr = flr}) = flr
  Inhab {suc n} (Xₙ , Xₛₙ) Xₛₛₙ ._ (nd-there {brs = brs} p q) = 
    Inhab (Xₙ , Xₛₙ) Xₛₛₙ (brnch (Inhab Xₙ (Branch Xₙ Xₛₙ Xₛₛₙ) brs p)) q 

  η {zero} Xₙ Xₛₙ x = x
  η {suc n} (Xₙ , Xₛₙ) Xₛₛₙ {f , t , s} x =
    let brs = μ Xₙ Xₛₙ (Branch Xₙ Xₛₙ Xₛₛₙ) s (λ _ p → η Xₙ (Branch Xₙ Xₛₙ Xₛₛₙ) [ Inhab Xₙ Xₛₙ s p , _ , lf (Inhab Xₙ Xₛₙ s p) ])
    in nd t brs x 
  
  η-pos {zero} Xₙ Xₛₙ x = tt*
  η-pos {suc n} Xₙ Xₛₙ x = nd-here

  -- graft : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ)
  --   → (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ)
  --   → (f : Frm Xₙ) (tgt : Xₛₙ f)
  --   → (src : Src Xₙ Xₛₙ f) (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ src f) → Branch Xₙ Xₛₙ Xₛₛₙ f)
  --   → (pd : Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , src))
  --   → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , μ Xₙ Xₛₙ {!!})
  -- graft = {!!} 
  
  -- γ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ)
  --   → (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ)
  --   → (f : Frm Xₙ) (tgt : Xₛₙ f)
  --   → (ih : Src Xₙ (Branch Xₙ Xₛₙ Xₛₛₙ) f)
  --   → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , smap Xₙ (λ _ → stm) ih)
  --   → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ _ → lvs) ih))

  μ = {!!} 
  -- μ {zero} Xₙ Xₛₙ pd = pd
  -- μ {suc n} Xₙ Xₛₙ (lf tgt) = lf tgt
  -- μ {suc n} (Xₙ , Xₛₙ) Xₛₛₙ (nd f tgt ih filler) =
  --   let ih' = smap Xₙ (λ f br → [ stm br , lvs br , μ (Xₙ , Xₛₙ) Xₛₛₙ (brnch br) ]) ih  
  --   in γ Xₙ Xₛₙ Xₛₛₙ f tgt ih' filler

  μ-pos = {!!} 


  μ-fst-frm = {!!}
  μ-fst = {!!} 
  μ-snd = {!!} 
