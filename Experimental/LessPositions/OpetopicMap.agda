--
-- PositionlessMap.agda - Maps between opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.Prelude
open import Experimental.LessPositions.OpetopicType

module Experimental.LessPositions.OpetopicMap where

  _⇒_ : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ → Type ℓ
  
  Frm⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} → X ⇒ Y → Frm X → Frm Y
  
  Src⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
    → {Xₛₙ : Frm Xₙ → Type ℓ}
    → {Yₛₙ : Frm Yₙ → Type ℓ}
    → (σₙ : Xₙ ⇒ Yₙ)
    → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f ))
    → {f : Frm Xₙ}
    → Src Xₛₙ f → Src Yₛₙ (Frm⇒ σₙ f)
    
  Pos⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
    → {Xₛₙ : Frm Xₙ → Type ℓ}
    → {Yₛₙ : Frm Yₙ → Type ℓ}
    → (σₙ : Xₙ ⇒ Yₙ)
    → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f ))
    → {f : Frm Xₙ} (s : Src Xₛₙ f)
    → Pos Xₛₙ s → Pos Yₛₙ (Src⇒ Xₙ Yₙ σₙ σₛₙ s) 

  _⇒_ {zero} X Y = Lift Unit
  _⇒_ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) = Σ[ fun ∈ Xₙ ⇒ Yₙ ] ((f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ fun f))


  Frm⇒ {zero} {ℓ} {X} {Y} fun f = tt*
  Frm⇒ {suc n} {ℓ} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (funₙ , funₛₙ) (f , t , s) =
    (Frm⇒ funₙ f) , (funₛₙ _ t) , Src⇒ Xₙ Yₙ funₙ funₛₙ s

  Branch⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type (suc n) ℓ)
    → {Xₛₙ : Frm Xₙ → Type ℓ}
    → {Yₛₙ : Frm Yₙ → Type ℓ}
    → (σₙ : Xₙ ⇒ Yₙ)
    → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f ))
    → {f : Frm (fst Xₙ)}
    → Branch Xₛₙ f → Branch Yₛₙ (Frm⇒ (σₙ .fst) f)
  Branch⇒ X Y {P} {Q} (σ , σ') σ'' [ stm , lvs , br ] =
    [ σ' _ stm , Src⇒ (fst X) (fst Y) σ σ' lvs , Src⇒ X Y (σ , σ') σ'' br ]


  postulate
    η⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
      → {Xₛₙ : Frm Xₙ → Type ℓ}
      → {Yₛₙ : Frm Yₙ → Type ℓ}
      → (σₙ : Xₙ ⇒ Yₙ)
      → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f))
      → {f : Frm Xₙ} (x : Xₛₙ f)
      → Src⇒ Xₙ Yₙ σₙ σₛₙ (η Xₛₙ x) ↦ η Yₛₙ (σₛₙ f x)
    {-# REWRITE η⇒ #-}

    μ⇒' : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      (P P' : Frm X → Type ℓ)
      (Q : Frm Y → Type ℓ)
      (σ' : (f : Frm X) → P' f → Q (Frm⇒ σ f))
      {f : Frm X}
      (s : Src P f)
      (t : (p : Pos P s) → Src P' (Typ s p))
      → Src⇒ X Y {P'} {Q} σ σ' (μ P' s t) ↦ μ Q {!Src⇒ X Y σ σ' !} {!!}
    -- {-# REWRITE μ⇒ #-}

   -- (Src⇒ X Y σₙ σₛₙ (μ P brs (λ p → η P (stm (brs ⊚ p))))) !=
   -- (μ Q brs' (λ p → η Q (stm (brs' ⊚ p)))) of type (Src Q (Frm⇒ σₙ f))

    μ⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (σ' : (f : Frm X) → P f → Q (Frm⇒ σ f))
      → {f : Frm X} (s : Src P f)
      → (t : (p : Pos P s) → Src P (Typ s p))
      → Src⇒ X Y {P} {Q} σ σ' (μ P s t) ↦ Src⇒ X Y {P} {Q} σ σ' s  
    {-# REWRITE μ⇒ #-}
    
    μ'⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      (P : Frm X → Type ℓ)
      (Q : Frm Y → Type ℓ)
      (σ' : (f : Frm X) → P f → Q (Frm⇒ σ f))
      {f : Frm X}
      (s : Src (Src P) f)
      → Src⇒ X Y {Yₛₙ = Q} σ σ' (μ' {Xₛₙ = P} s) ↦ μ' {Xₛₙ = Q} (Src⇒ X Y σ (λ f → Src⇒ X Y σ σ') s)

  Src⇒ {zero} {ℓ} X Y {P} {Q} σₙ σₛₙ {f} = σₛₙ _
  Src⇒ {suc n} {ℓ} X Y {P} {Q} σₙ σₛₙ (lf tgt) = lf (snd σₙ _ tgt)
  Src⇒ {suc n} {ℓ} (X , P) (Y , Q) {P'} {Q'} (σₙ , σₛₙ) σₛₛₙ (nd {f = f} tgt brs flr) = {!!}

    where tgt' : Q (Frm⇒ σₙ f)
          tgt' = σₛₙ f tgt
          
          brs' : Src (Branch Q') (Frm⇒ σₙ f)
          brs' = Src⇒ X Y {Branch P'} {Branch Q'} σₙ (λ f → Branch⇒ (X , P) (Y , Q) {P'} {Q'} (σₙ , σₛₙ) σₛₛₙ {f = f}) brs 

          flr' : Q' (Frm⇒ (σₙ , σₛₙ) (f , tgt , μ P brs (λ p → η P (stm (brs ⊚ p)))))
          flr' = σₛₛₙ (f , tgt , μ P brs (λ p → η P (stm (brs ⊚ p)))) flr 

   -- So this is the missing equation.  Notice that it's just a map, not a full-fledged
   -- multiplication.
   
   -- (Src⇒ X Y σₙ σₛₙ (μ P brs (λ p → η P (stm (brs ⊚ p))))) !=
   -- (μ Q brs' (λ p → η Q (stm (brs' ⊚ p)))) of type (Src Q (Frm⇒ σₙ f))

  Pos⇒ = {!!} 
