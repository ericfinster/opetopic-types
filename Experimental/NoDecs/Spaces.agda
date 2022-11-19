{-# OPTIONS --type-in-type #-}
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
open import Experimental.NoDecs.Universe

module Experimental.NoDecs.Spaces where

  -- The (∞,1)-category of spaces
  𝒮 : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮π : (n : ℕ) (ℓ : Level) → 𝒮 n ℓ ⇒ 𝕆U n ℓ

  𝒮 zero ℓ = tt*
  𝒮 (suc n) ℓ =  𝒮 n ℓ , λ f →
    Σ[ C ∈ OpRel (Frm⇒ (𝒮π n ℓ) f) ]
    is-fib-family C
  
  𝒮π zero ℓ = tt*
  𝒮π (suc n) ℓ = 𝒮π n ℓ , fst

  --  Okay, now the goal is to prove that this guy is fibrant.  First
  --  obstruction is that there is a universe problem: you need to
  --  know that the elements living over a given pasting diagram in
  --  the universe are small.  You could think of them as decorations,
  --  but then I think you'll need positions to be small.  (Of course,
  --  if you define the recursively, then you can even put them in
  --  the lowest universe ...)

  -- Shit.  This is serious.  Is there a way to get a small version
  -- without introducing the notion of dependent opetopic type?

  𝕆UComp : ∀ {n ℓ} (F : Frm (𝕆U n ℓ)) (S : Src OpRel F) → OpRel F
  𝕆UComp F S = Src↓ {F = F} S 

  𝕆UFill : ∀ {n ℓ} (F : Frm (𝕆U n ℓ)) (S : Src OpRel F) → OpRel {suc n} (F , S , 𝕆UComp F S)
  𝕆UFill F S ((f , s , t) , e) = {!!} 

  -- Right.  So the element held by t "is" a source over S.  It
  -- should be equal, as such an element, so s.

  -- So what's the essential lemma?  In the above, if all the
  -- relations decorating the positions of S are fibrant, then
  -- so is the composite.

  claim : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src OpRel F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} OpRel S) → is-fib-family (S ⊚ p))
    → is-fib-family (Src↓ {F = F} S)
  claim {zero} S ϕ = tt*
  claim {suc n} (lf tgt) ϕ {f , e} (s , m) = {!s!}
  claim {suc n} (nd tgt brs flr) ϕ s = {!!}

  -- Ech.  This is going to be a nightmare.

  -- is-fib-family : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)}
  --   → OpRel F → Type (ℓ-suc ℓ)
  -- is-fib-family {zero} {ℓ} {F} C = Unit*
  -- is-fib-family {suc n} {ℓ} {F , S , T} C = 
  --   {f : Frm↓ F} (s : Src↓ S f)
  --     → isContr (Σ[ t ∈ El↓ T f ] C (mkFrm↓ f s t))


  -- horn-filler : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ) {f : Frm Xₙ} → Src Xₛₙ f → Type ℓ
  -- horn-filler {n} {ℓ} {Xₙ} {Xₛₙ} Xₛₛₙ {f} s = Σ[ tgt ∈ Xₛₙ f ] Xₛₛₙ (f , s , tgt)

  -- is-fibrant : ∀ {n ℓ} → 𝕆Type (suc (suc n)) ℓ → Type ℓ
  -- is-fibrant ((Xₙ , Xₛₙ) , Xₛₛₙ) = (f : Frm Xₙ) (s : Src Xₛₙ f) → isContr (horn-filler Xₛₛₙ s)
