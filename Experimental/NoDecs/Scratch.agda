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
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.Scratch where

  --
  --  Utilities
  --

  -- The shape map
  Shape : ∀ {n ℓ} (X : 𝕆Type n ℓ) → X ⇒ 𝕋 {ℓ} n
  Shape {zero} X = tt*
  Shape {suc n} (X , P) = Shape X , λ _ → tt*

  SrcShape : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Src (const (Lift Unit)) (Frm⇒ (Shape X) f)
  SrcShape X P s = map-src (Shape X) P (const (Lift Unit)) s (const tt*)

  ObjType : ∀ {n ℓ} (X : 𝕆Type (suc n) ℓ) → Type ℓ
  ObjType {zero} X = snd X tt*
  ObjType {suc n} X = ObjType (fst X)
  
  InitialObj : ∀ {n ℓ} (X : 𝕆Type (suc n) ℓ) (f : Frm X) → ObjType X
  InitialObj {zero} X (_ , x , _) = x
  InitialObj {suc n} (X , _) (f , _ , _) = InitialObj X f

  --
  --  The ∞-groupoid associated to a type
  --

  Grp : ∀ {ℓ} (X : Type ℓ) → (n : ℕ) → 𝕆Type n ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕋 {ℓ} n ⇒ (Grp X n)

  data GrpCell {n ℓ} (X : Type ℓ) : Frm (Grp X n) → Type ℓ where
    reflₒ : (x : X) {f : Frm (𝕋 n)} → GrpCell X (Frm⇒ (Pt x) f)

  Grp X zero = tt*
  Grp X (suc n) = Grp X n , GrpCell X

  Pt {zero} x = tt*
  Pt {suc n} x = Pt x , λ _ → reflₒ x

  -- The canonical tree.
  GrpSrc : ∀ {n ℓ} (X : Type ℓ) (x : X)
    → {f : Frm (𝕋 {ℓ} n)} (s : Src (const Unit*) f)
    → Src (GrpCell X) (Frm⇒ (Pt x) f)
  GrpSrc {n} {ℓ} X x s = map-src {n} {ℓ} (Pt x) (const Unit*) (GrpCell X) s (λ p → reflₒ x)

  init-obj : ∀ {n ℓ} {X : Type ℓ}
    → (f : Frm (Grp X n)) (s : Src (GrpCell X) f) → X
  init-obj {zero} _ (reflₒ x) = x
  init-obj {suc n} (f , s , _) _ = init-obj f s

  to : ∀ {n ℓ} (X : Type ℓ) 
    → Σ[ f ∈ Frm (Grp X n) ] Src (GrpCell X) f
    → Σ[ f' ∈ Frm (𝕋 {ℓ} n) ] Src (const Unit*) f'
  to {n} X (f , s) = Frm⇒ (Shape (Grp X n)) f ,
    map-src (Shape (Grp X n)) (GrpCell X) (const (Lift Unit)) s (const tt*) 

  from : ∀ {n ℓ} (X : Type ℓ) (x : X)
    → Σ[ f' ∈ Frm (𝕋 {ℓ} n) ] Src (const Unit*) f'
    → Σ[ f ∈ Frm (Grp X n) ] Src (GrpCell X) f
  from X x (f' , s') = Frm⇒ (Pt x) f' , GrpSrc X x {f = f'}  s'

  from-to : ∀ {n ℓ} (X : Type ℓ) 
    → {f : Frm (Grp X n)} (s : Src (GrpCell X) f)
    → from X (init-obj f s) (to X (f , s)) ≡ (f , s)
  from-to {zero} X (reflₒ x) = refl
  from-to {suc n} X (lf (reflₒ x)) = {!!}
  from-to {suc n} X (nd tgt brs flr) = {!!}

  -- Goal: ((Frm⇒ (Pt (init-obj (Frm⇒ (Pt x) f) (η (GrpCell X) (reflₒ x))) ⊙ Shape (Grp X n) ⊙ Pt x) f
  --      , η (GrpCell X) (reflₒ (init-obj (Frm⇒ (Pt x) f) (η (GrpCell X) (reflₒ x))))
  --      , reflₒ (init-obj (Frm⇒ (Pt x) f) (η (GrpCell X) (reflₒ x))))
  --      , lf (reflₒ (init-obj (Frm⇒ (Pt x) f) (η (GrpCell X) (reflₒ x)))))
  --     ≡
  --     ((Frm⇒ (Pt x) f
  --      , η (GrpCell X) (reflₒ x)
  --      , reflₒ x)
  --      , lf (reflₒ x))

  -- Right, so we clearly need the equation
  -- 
  --   init-obj (Frm⇒ (Pt x) f) (η (GrpCell X) (reflₒ x)) ≡ x
  --
  -- which should be easy.  The other is obviously slightly stranger.
  -- But can you actually state the theorem that way? Using the maps? 

  -- Oh! But the *other* composite
  --
  --    Shape (Grp X n) ⊙ Pt x
  --
  -- is the identity because it is an endomorphism of 𝕋!  So this one
  -- just cancels for free.  And this finishes the leaf case!


