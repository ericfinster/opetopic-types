--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty 
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.Fibrancy where

  Shape : ∀ {n ℓ} (X : 𝕆Type n ℓ) → X ⇒ 𝕋 {ℓ} n
  Shape {zero} X = tt*
  Shape {suc n} (X , P) = Shape X , λ _ → tt*

  SrcShape : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → Σ[ f ∈ Frm X ] Src P f
    → Σ[ f' ∈ Frm (𝕋 {ℓ} n) ] Src (const (Lift Unit)) f'
  SrcShape X P (f , σ) = Frm⇒ (Shape X) f , map-src (Shape X) P (const (Lift Unit)) σ (const tt*)

  -- So one thing is that I claim maping over trees commutes with
  -- fibers: asking what is the fiber of a map of trees is the same as
  -- asking for a tree decorated in the fibers.  
  

  -- We'll need a bunch of lemma saying that, say, if an element is living
  -- over η in the base, then it is an η and so on..
  SrcShape-η : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (σ : Src P f)
    → map-src (Shape X) P (const (Lift Unit)) σ (const tt*) ≡ η {X = fst (𝕋 {ℓ} (suc n))} (const (Lift Unit)) tt*
    → Σ[ x ∈ P f ] σ ≡ η P x
  SrcShape-η {zero} X P f σ e = σ , refl
  SrcShape-η {suc n} X P ._ (lf tgt) e = {!!} -- trivial because lf ≠ nd 
  SrcShape-η {suc n} X P ._ (nd tgt brs flr) e = {!!}

  -- Right, so what's the best way to organize this kind of thing? 

  -- So this is a choice of an opetopic pasting diagram lying "under"
  -- the chosen pasing diagram.  And s the claim is that if we have
  -- a fibrant extention, then there is a map.  
  BlankPd : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → {f : Frm X} (σ : Src P f)
    → Type ℓ
  BlankPd {n} {ℓ} X P {f} σ =
    Src {X = 𝕋 {ℓ} (suc n)} (snd (𝕋 {ℓ} (suc (suc n))))
      (Frm⇒ (Shape X) f , map-src (Shape X) P (snd (𝕋 {ℓ} (suc n))) σ (const tt*) , tt*) 

  -- And moreover, this comes with a proof that it is in the fiber of the *next*
  -- shape map .... 
  ComposeAlong : ∀ {n ℓ}
    → (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (is-fib : is-fibrant ((X , P) , U))
    → {tf : Frm (𝕋 {ℓ} n)} (ts : Src (const (Lift Unit)) tf)
    → (pd : Src (snd (𝕋 {ℓ} (suc (suc n)))) (tf , ts , tt*))
    → (fs : fiber (SrcShape X P) (tf , ts))
    → Σ[ tgt ∈ P (fst (fst fs)) ] Src U (fst (fst fs) , snd (fst fs) , tgt)
  ComposeAlong X P U is-fib ._ (lf .tt*) ((f , σ) , e) = {!!} , {!!}
  ComposeAlong {n} {ℓ} X P U is-fib ._ (nd .tt* brs tt*) ((f , σ) , e) = {!brs!} , {!!}

    where IH : (p : Pos {X = 𝕋 {ℓ} n} (Branch (const (Lift Unit))) brs) → {!br (brs ⊚ p)!}
          IH p = {!ComposeAlong X P U is-fib _ (br (brs ⊚ p))!} 


