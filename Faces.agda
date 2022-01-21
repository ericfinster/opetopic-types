{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

open import Opetopes
open import OpetopicType
open import OpetopicMap

module Faces where

  data InnerFace : {n : ℕ} → 𝒪 n → ℕ → Set where
    as-src : {n : ℕ} (o : 𝒪 n) (p : 𝒫 o) (q : 𝒫 (o , p))
      → Pos q → InnerFace ((o , p) , q) (S n)
    as-tgt : {n : ℕ} (o : 𝒪 n) (p : 𝒫 o) (q : 𝒫 (o , p))
      → Pos q → InnerFace ((o , p) , q) n
    raise-face : {n m : ℕ} (o : 𝒪 n) (p : 𝒫 o)
      → InnerFace o m → InnerFace (o , p) m 

  data Face : {n : ℕ} → 𝒪 n → ℕ → Set where
    top : {n : ℕ} (o : 𝒪 n) → Face o n
    tgt-face : {n : ℕ} (o : 𝒪 (S n)) → Face o n
    init : {n : ℕ} (o : 𝒪 (S n)) → Face o 0
    inner : {n m : ℕ} (o : 𝒪 n) → InnerFace o m → Face o m  

  -- obj : 𝒪 0
  -- obj = tt

  obj-face : Face obj 0 
  obj-face = top tt
  
  -- arrow : 𝒪 1
  -- arrow = tt , tt

  arrow-src : Face arrow 0
  arrow-src = init arrow
  
  arrow-tgt : Face arrow 0
  arrow-tgt = tgt-face arrow 

  arrow-top : Face arrow 1
  arrow-top = top arrow

  -- 2-simplex : 𝒪 2
  -- 2-simplex = (tt , tt) , ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))
  
  simplex = 2-simplex

  simp-init : Face simplex 0
  simp-init = init simplex 

  simp-mid : Face simplex 0
  simp-mid = inner simplex (as-tgt tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inl tt))

  simp-term : Face simplex 0
  simp-term = inner simplex (as-tgt tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inr (tt , inl tt))) 

  simp-fst : Face simplex 1
  simp-fst = inner simplex (as-src tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inl tt))

  simp-snd : Face simplex 1
  simp-snd = inner simplex (as-src tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inr (tt , inl tt))) 

  simp-tgt : Face simplex 1
  simp-tgt = tgt-face simplex

  simp-top : Face simplex 2
  simp-top = top simplex 

  --
  --  Representables
  --

  Rep : {n : ℕ} (o : 𝒪 n) → 𝕆 ℓ-zero (S n)

  SrcInc' : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → Rep (Typ ρ p) ⇒ fst (Rep (o , ρ))
  SrcInc' = {!!} 

  SrcInc : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → (Rep (Typ ρ p) , cst ∅) ⇒ Rep (o , ρ)
  TgtInc : {n : ℕ} (o : 𝒪 n) (ρ : 𝒫 o) (p : Pos ρ) → (Rep o , cst ∅) ⇒ Rep (o , ρ)

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

  data BoundaryCell {n} (o : 𝒪 n) (ρ : 𝒫 o) : {q : 𝒪 n} → Frm (fst (Rep o)) q → Set where
    src-cell : (p : Pos ρ) (f : Frm (Rep (Typ ρ p)) {!!})
      → BoundaryCell o ρ {!!} 

  data FillingCell {n} (o : 𝒪 n) (ρ : 𝒫 o) : {q : 𝒪 (S n)}
    → WebFrm (fst (Rep o)) (BoundaryCell o ρ) (fst q) (snd q) → Set where


  Rep {n = O} tt = tt , cst ⊤ 
  Rep {n = S O} (tt , tt) = 
    (tt , cst (⊤ ⊔ ⊤)) , ArrowFill

  Rep {n = S (S n)} ((o , ρ) , τ) = ((fst (fst (Rep (o , ρ))) , {!!}) , {!!}) , {!!}

  -- Rep {n = O} o = tt , cst ⊤
  -- Rep {n = S n} (o , ρ) = (fst (Rep o) , BoundaryCell o ρ) , FillingCell o ρ

  SrcInc = {!!} 
  TgtInc = {!!} 


  -- data LfBdry {n : ℕ} (m : 𝒪 n) : {o : 𝒪 (S n)}
  --   → WebFrm (fst (Rep m)) (snd (Rep m)) (fst o) (snd o) → Set where
  --   lf-tgt : LfBdry m ⟪ {!!} , {!η (fst (Rep m))!} , {!!} , {!!} ⟫ 

  
  -- Rep {n = S (S n)} ((x , .(ηₒ x)) , lfₒ .x) = (Rep x , LfBdry x) , {!!}
  -- Rep {n = S (S n)} ((o , .(μₒ ρ δ)) , ndₒ .o ρ δ ε) = {!!}


