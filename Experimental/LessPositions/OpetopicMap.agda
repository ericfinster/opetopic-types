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
  
  _⇒_ {zero} X Y = Lift Unit
  _⇒_ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) = Σ[ fun ∈ Xₙ ⇒ Yₙ ] ((f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ fun f))

  Branch⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type (suc n) ℓ)
    → {Xₛₙ : Frm Xₙ → Type ℓ}
    → {Yₛₙ : Frm Yₙ → Type ℓ}
    → (σₙ : Xₙ ⇒ Yₙ)
    → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f ))
    → {f : Frm (fst Xₙ)}
    → Branch Xₛₙ f → Branch Yₛₙ (Frm⇒ (σₙ .fst) f)

  Frm⇒ {zero} {ℓ} {X} {Y} fun f = tt*
  Frm⇒ {suc n} {ℓ} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (funₙ , funₛₙ) (f , t , s) =
    (Frm⇒ funₙ f) , (funₛₙ _ t) , Src⇒ Xₙ Yₙ funₙ funₛₙ s
      {-smap Yₙ funₛₙ* {!!} where
      data Xₛₙ* : Frm Yₙ → Type ℓ where
        test : {f : Frm Xₙ} (x : Xₛₙ f) → Xₛₙ* (Frm⇒ funₙ f)

      funₛₙ* : (f : Frm Yₙ) → Xₛₙ* f → Yₛₙ f
      funₛₙ* .(Frm⇒ funₙ _) (test x) = funₛₙ _ x-}

  postulate
    η⇒ : ∀ {n ℓ} (Xₙ Yₙ : 𝕆Type n ℓ)
      → {Xₛₙ : Frm Xₙ → Type ℓ}
      → {Yₛₙ : Frm Yₙ → Type ℓ}
      → (σₙ : Xₙ ⇒ Yₙ)
      → (σₛₙ : (f : Frm Xₙ) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f))
      → {f : Frm Xₙ} (x : Xₛₙ f)
      → Src⇒ Xₙ Yₙ σₙ σₛₙ (η Xₛₙ x) ↦ η Yₛₙ (σₛₙ f x)
    {-# REWRITE η⇒ #-}

    μ⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      (P P' : Frm X → Type ℓ)
      (Q Q' : Frm Y → Type ℓ)
      (σ' : (f : Frm X) → P' f → Q' (Frm⇒ σ f))
      {f : Frm X}
      (s : Src P f)
      (t : (p : Pos P s) → Src P' (Typ s p))
      → Src⇒ X Y {Xₛₙ = P'} {Yₛₙ = Q'} σ σ' (μ P' s t ) ↦ μ {P = Q} Q' (Src⇒ X Y σ {!!} s) {!!}
    --{-# REWRITE μ⇒ #-}

    μ'⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      (P : Frm X → Type ℓ)
      (Q : Frm Y → Type ℓ)
      (σ' : (f : Frm X) → P f → Q (Frm⇒ σ f))
      {f : Frm X}
      (s : Src (Src P) f)
      → Src⇒ X Y {Yₛₙ = Q} σ σ' (μ' {Xₛₙ = P} s) ↦ μ' {Xₛₙ = Q} (Src⇒ X Y σ (λ f → Src⇒ X Y σ σ') s)

    {-μ⇒ : ∀ {n ℓ} (X Y : 𝕆Type n ℓ)
      → {Xₛₙ : Frm X → Type ℓ}
      → {Yₛₙ : Frm Y → Type ℓ}
      → (σₙ : X ⇒ Y)
      → (σₛₙ : (f : Frm X) → Xₛₙ f → Yₛₙ (Frm⇒ σₙ f))
      → {f : Frm X} (x : Xₛₙ f)
      → (ih : Src (Src Xₛₙ) f)
      → Src⇒ X Y {Yₛₙ = Yₛₙ} σₙ σₛₙ (μ' {Xₛₙ = Xₛₙ} ih) ↦ μ' {Xₛₙ = Yₛₙ} (Src⇒ X Y σₙ (λ f' s → Src⇒ X Y σₙ σₛₙ s) ih)-}
--→ Src⇒ Xₙ Yₙ σₙ σₛₙ (μ Xₙ Xₛₙ (smap Xₙ (λ _ x → fst (snd x)) ih)) ↦ μ Yₙ Yₛₙ (smap Yₙ (λ f x → fst (snd x)) (Src⇒ Xₙ Yₙ σₙ {!σₛₙ!} ih))

  Branch⇒ X Y {P} {Q} (σ , σ') σ'' [ stm , lvs , br ] = [ σ' _ stm , Src⇒ (fst X) (fst Y) σ σ' lvs , Src⇒ X Y (σ , σ') σ'' br ]

  Src⇒ {zero} {ℓ} X Y {P} {Q} σₙ σₛₙ {f} = σₛₙ _
  Src⇒ {suc n} {ℓ} X Y {P} {Q} σₙ σₛₙ {.(_ , tgt , η (snd X) tgt)} (lf tgt) = lf (snd σₙ _ tgt)
  Src⇒ {suc n} {ℓ} (X , P) (Y , Q) {P'} {Q'} (σₙ , σₛₙ) σₛₛₙ {.(_ , tgt , μ P brs (λ p → lvs (brs ⊚ p)))} (nd tgt brs flr) = nd (σₛₙ _ tgt) (test brs) (σₛₛₙ {!Branch⇒!} flr) where
    test : {f : Frm X} → Src (Branch P') f → Src (Branch Q') (Frm⇒ σₙ f)
    test = Src⇒ X Y σₙ (λ f → Branch⇒ (X , P) (Y , Q) (σₙ , σₛₙ) σₛₛₙ)


  {-
  Src⇒ {zero} Xₙ Yₙ σₙ σₛₙ {f} s = σₛₙ f s
  Src⇒ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) (σₙ , σₛₙ) σₛₛₙ {.(f , tgt , η Xₙ Xₛₙ tgt)} (lf f tgt) = lf (Frm⇒ σₙ f) (σₛₙ f tgt)
  Src⇒ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) (σₙ , σₛₙ) σₛₛₙ {.(f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ z → fst ∘ snd) ih))} (nd f tgt ih filler) =
    nd (Frm⇒ σₙ f) (σₛₙ f tgt) (Src⇒ {!!} {!!} σₙ {!σₛₙ!} {!!}) {!!}
  -}
