--
--  OpetopicExt.agda - Extension of the context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicSub 
open import OpetopicType
open import OpetopicTerm

module OpetopicExt where

  Ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → 𝕆Ctx n (ℓ-max ℓ₀ ℓ₁) 

  π-ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → Ext Γ X ⇒ Γ

  tm-ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → 𝕆Term (X [ π-ext Γ X ]ty)

  Ext {zero} Γ X = lift tt
  Ext {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    Ext Γₙ Xₙ , λ f → Σ[ γ ∈ Γₛₙ (Frm⇒ (π-ext Γₙ Xₙ) f) ] Xₛₙ
      [ π-ext Γₙ Xₙ ⊙ Frm-Tm (tm-ext Γₙ Xₙ) f ] γ

  π-ext {zero} Γ X = lift tt
  π-ext {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    π-ext Γₙ Xₙ , fst

  tm-ext {zero} Γ X = lift tt
  tm-ext {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    tm-ext Γₙ Xₙ , snd

  -- postulate

  --   blorp : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
  --     → {𝑜 : 𝒪 n} (f : Frm (Ext Γ X) 𝑜)
  --     → [ π-ext Γ X ⊙ Frm-Tm (tm-ext Γ X) f ] ↦ {!!} 

  -- Yeah, ummm, we should do this for arbitrary susbtitutions
  -- and then have the identity.  I think that is probably better.
  -- ext-sub : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {X : 𝕆Type Γ ℓ₁}
  --   → 𝕆Term X → Γ ⇒ Ext Γ X

  -- postulate

  --   -- Are these really the natural equations?
  --   Frm-ext-sub : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {X : 𝕆Type Γ ℓ₁}
  --     → (x : 𝕆Term X) {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
  --     → Frm⇒ (π-ext Γ X) (Frm⇒ (ext-sub x) f) ↦ f
  --   {-# REWRITE Frm-ext-sub #-}

  --   Tm-ext-sub : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {X : 𝕆Type Γ ℓ₁}
  --     → (x : 𝕆Term X) {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
  --     → [ π-ext Γ X ⊙ Frm-Tm (tm-ext Γ X) (Frm⇒ (ext-sub x) f) ] ↦ Frm-Tm x f
  --   {-# REWRITE Tm-ext-sub #-}
    
  -- ext-sub {zero} x = lift tt
  -- ext-sub {suc n} (xₙ , xₛₙ) = ext-sub {n} xₙ , λ γ → γ , xₛₙ γ

  
  Extend : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → 𝕆Ctx n (ℓ-max ℓ₀ ℓ₁)

  FrmPr : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜) (f↓ : Frm↓ X f)
    → Frm (Extend Γ X) 𝑜

  data ExtendCell {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx (suc n) ℓ₀) (X : 𝕆Type Γ ℓ₁)
    : {𝑜 : 𝒪 n} → Frm (Extend (fst Γ) (fst X)) 𝑜 → Type (ℓ-max ℓ₀ ℓ₁) where

    pair : {𝑜 : 𝒪 n} {f : Frm (fst Γ) 𝑜} {f↓ : Frm↓ (fst X) f}
      → (γ : (snd Γ) f) (x : (snd X) f↓ γ)
      → ExtendCell Γ X (FrmPr (fst Γ) (fst X) f f↓) 

  Extend {zero} Γ X = lift tt
  Extend {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    Extend Γₙ Xₙ , ExtendCell (Γₙ , Γₛₙ) (Xₙ , Xₛₙ)

  FrmPr {zero} Γ X f f↓ = lift tt
  FrmPr {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) (f , x , c , y) (f↓ , x↓ , c↓ , y↓) =
    FrmPr Γₙ Xₙ f f↓ , pair x x↓ , {!!} , λ p → {!pair (y p) (y↓ p)!} 

  -- Grp : ∀ {n ℓ} (X : Type ℓ) → 𝕆Type (𝕋 n) ℓ
  -- Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕆Term {n} (Grp X)

  -- -- The extra units make this sloppy, but okay ...
  -- data 𝕆Id {n ℓ} (X : Type ℓ) : {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜}
  --   → Frm↓ (Grp X) f → Lift Unit → Type ℓ where
  --   op-refl : (x : X) {𝑜 : 𝒪 n} {f : Frm (𝕋 n) 𝑜} (γ : Lift Unit)
  --     → 𝕆Id X (Frm-Tm (Pt x) f) γ

  -- Grp {zero} X = lift tt
  -- Grp {suc n} X =
  --   Grp {n} X , 𝕆Id X

  -- Pt {zero} x = lift tt
  -- Pt {suc n} x = Pt {n} x , op-refl x


  -- Here's another thing you could try: define the type of *elements* of an
  -- opetopic context as it's global sections.  Define, given a context, an
  -- opetopic type in that context and an element, the fiber at that element.
  -- (This is a kind of special case of substitution).

  -- Now, recursively define *elements* of the sigma type.  So: given an
  -- element of the base, and an element of the evaluated fiber, we get
  -- a new element of the pairing guy.
