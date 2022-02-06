{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

open import Opetopes
open import OpetopicType
open import OpetopicMap

module Representable where

  Rep : {n : ℕ} (o : 𝒪 n) → 𝕆 ℓ-zero (S n)

  SrcInc : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → Rep (Typ ρ p) ⇒ fst (Rep (o , ρ))
  TgtInc : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → Rep o ⇒ fst (Rep (o , ρ))


  -- Hmmm. This is not quite right.  It is the top *3* fibrations
  -- which must change.

  -- So, the cells of the first are parameterized by two things
  -- 1) the positions of ρ (there will be the externals)
  -- 2) the positions of τ (this will be the internals)

  -- In the next fibration, we have exactly the positions of τ and the target.

  -- And then we have the unique next dimension.

  -- Right.  So this should actually lead to another, slight different
  -- presentation of the faces above.

  data ArrowFill : {o : 𝒪 1} → WebFrm tt (cst (⊤ ⊔ ⊤)) (fst o) (snd o) → Set where
    top : ArrowFill ⟪ tt , tt , inl tt , (λ _ → inr tt) ⟫ 

  data Pivot {n} (o : 𝒪 n) (ρ : 𝒫 o) (τ : 𝒯r o ρ) : {q : 𝒪 n} → Frm (fst (fst (Rep (o , ρ)))) q → Set where

    -- Does this make sense?  Hmmm.  But don't you want the frame to be full?
    -- So the pair should make this a complete guy.  So that looks okay.
    ext : (p : Pos ρ) (f : Frm (fst (Rep (Typ ρ p))) (Typ ρ p)) (c : snd (Rep (Typ ρ p)) f) 
      → Pivot o ρ τ (Frm⇒ (fst (SrcInc o ρ p)) f)

    int : (p : Pos τ) (f : Frm (fst (Rep (fst (𝒯rTyp τ p)))) (fst (𝒯rTyp τ p))) (c : snd (Rep (fst (𝒯rTyp τ p))) f) 
      → Pivot o ρ τ {!TgtInc o ρ !} 

  Rep {n = O} tt = tt , cst ⊤ 
  Rep {n = S O} (tt , tt) = 
    (tt , cst (⊤ ⊔ ⊤)) , ArrowFill

  Rep {n = S (S n)} ((o , ρ) , τ) = ((fst (fst (Rep (o , ρ))) , Pivot o ρ τ) , {!!}) , {!!}

  -- Rep {n = O} o = tt , cst ⊤
  -- Rep {n = S n} (o , ρ) = (fst (Rep o) , BoundaryCell o ρ) , FillingCell o ρ

  SrcInc = {!!} 
  TgtInc = {!!} 


  -- data LfBdry {n : ℕ} (m : 𝒪 n) : {o : 𝒪 (S n)}
  --   → WebFrm (fst (Rep m)) (snd (Rep m)) (fst o) (snd o) → Set where
  --   lf-tgt : LfBdry m ⟪ {!!} , {!η (fst (Rep m))!} , {!!} , {!!} ⟫ 

  
  -- Rep {n = S (S n)} ((x , .(ηₒ x)) , lfₒ .x) = (Rep x , LfBdry x) , {!!}
  -- Rep {n = S (S n)} ((o , .(μₒ ρ δ)) , ndₒ .o ρ δ ε) = {!!}

