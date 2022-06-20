--
--  Representables.agda - Representable Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType 

module Experimental.NoDecs.Representables where

  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Type n ℓ
  𝕋 zero = tt*
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit

  --
  --  Some opetopes 
  --
  
  𝒪 : ℕ → Type
  𝒪 n = Frm (𝕋 n) 

  obj : 𝒪 0
  obj = tt*

  arr : 𝒪 1
  arr = tt* , tt* , tt*

  drop : 𝒪 2
  drop = arr , lf tt* , tt*

  2-globe : 𝒪 2
  2-globe = arr , nd tt* [ tt* , tt* , lf tt* ] tt* , tt* 

  canopy : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π) → Src (const Unit*) π
  canopy {n} π brs = μ (id-map (𝕋 n)) (Branch (const Unit*)) (λ _ → Lift Unit) brs (λ p → lvs (brs ⊚ p))

  --
  --  The codimension 2 part of the representable
  --

  Repr₀ : (n : ℕ) → 𝒪 (suc n) → 𝕆Type n ℓ-zero
  max-frm : (n : ℕ) (π : 𝒪 (suc n)) → Frm (Repr₀ n π)

  data Face₀ : {n : ℕ} (π : 𝒪 n)
    (σ : Src (const Unit*) π)
    (τ : Pd (const Unit*) (π , σ , tt*))
    → Frm (Repr₀ n (π , σ , tt*)) → Type where
  
    lf-cell : {n : ℕ} (π : 𝒪 n)
      → Face₀ π (η (const Unit*) {f = π} tt*) (lf tt*)
          (max-frm n (π , η (const Unit*) {f = π} tt* , tt*))
          
    nd-cell-there : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
      → (p : Pos (Branch (const Unit*)) {f = π} brs)
      → Face₀ (Typ (Branch (const Unit*)) brs p) (lvs (brs ⊚ p)) (br (brs ⊚ p))
          (max-frm n (Typ (Branch (const Unit*)) brs p , lvs (brs ⊚ p) , tt*)) 
      → Face₀ π (canopy π brs) (nd tt* brs tt*)
          (max-frm n (π , canopy π brs , tt*))

    nd-cell-here : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
      → Face₀ π (canopy π brs) (nd tt* brs tt*)
          (max-frm n (π , canopy π brs , tt*))

  Repr₀ zero _ = tt*
  Repr₀ (suc n) ((π , σ , tt*) , τ , tt*) =
    Repr₀ n (π , σ , tt*) , Face₀ π σ τ 


  -- Dimension 1 
  max-frm zero π = tt*

  -- Drops (this case is generic. do it first for better computation)
  max-frm (suc n) ((π , ._ , tt*) , lf .tt* , tt*) =
    max-frm n (π , _ , tt*) ,
    (η _ {f = max-frm n (π , _ , tt*)} (lf-cell π)) ,
    (lf-cell π)

  -- Dimension 2 
  max-frm (suc zero) ((π , ._ , tt*) , nd .tt* vbr tt* , tt*) = 
    tt* , nd-cell-there tt* vbr tt* (max-frm (suc zero) (_ , br vbr , tt*) .snd .fst) ,
          nd-cell-here tt* vbr

  -- Globs on Drops
  max-frm (suc (suc n)) ((._ , ._ , tt*) , nd .tt* (lf tt*) tt* , tt*) =
    _ , lf (lf-cell _) , (nd-cell-here _ (lf tt*))

  -- Dimension ≥ 3 - root of source tree is external
  max-frm (suc (suc n)) ((._ , ._ , tt*) , nd .tt* (nd tt* hbrs [ tt* , ._ , lf .tt* ]) tt* , tt*) =
    {!!} , {!!} , {!!}
  
  -- Dimension ≥ 3 - climbing the root box
  max-frm (suc (suc n)) ((._ , ._ , tt*) , nd .tt* (nd tt* hbrs [ tt* , ._ , nd .tt* brs flr ]) tt* , tt*) = {!!}


  -- -- Dimension 2 - The output cell is always the nd-cell-here
  -- -- constructor, and for the source we recurse, inserting 
  -- -- the nd-cell-there constructor to pass up the chain.
  -- max-frm (suc zero) ((tt* , tt* , tt*) , lf .tt* , tt*) =
  --   tt* , lf-cell tt* , lf-cell tt*
  -- max-frm (suc zero) ((tt* , tt* , tt*) , nd .tt* vbr tt* , tt*) =
  --   tt* , nd-cell-there tt* vbr tt* (max-frm (suc zero) (_ , br vbr , tt*) .snd .fst) ,
  --         nd-cell-here tt* vbr

  -- -- Dimension ≥ 3 - A Drop
  -- max-frm (suc (suc n)) (((π , ρ , tt*) , ._ , tt*) , lf .tt* , tt*) =
  --   max-frm (suc n) ((π , ρ , tt*) , η (const Unit*) {f = (π , ρ , tt*)} tt* , tt*) ,
  --   η _ {f = max-frm (suc n) ((π , ρ , tt*) , η (const Unit*) {f = (π , ρ , tt*)} tt* , tt*)} (lf-cell (π , ρ , tt*)) ,
  --   lf-cell (π , ρ , tt*)

  -- -- Dimension ≥ 3 - A Glob on a Drop 
  -- max-frm (suc (suc n)) (((π , ._ , tt*) , ._ , tt*) , nd .tt* (lf .tt*) tt* , tt*) =
  --   (max-frm n (π , η (const Unit*) {f = π} tt* , tt*) , η _ {f = max-frm n (π , η (const Unit*) {f = π} tt* , tt*)} (lf-cell π) , lf-cell π) ,
  --   lf (lf-cell π) ,
  --   {!nd-cell-here (π , η (λ _ → Lift Unit) tt* , tt*) (lf tt*)!} 

  --   -- max-frm (suc n) ((π , η (const Unit*) {f = π} tt* , tt*) , lf tt* , tt*)  ,
  --   -- {!!} ,
  --   -- nd-cell-here (π , _ , tt*) (lf tt*)

  -- -- Dimension ≥ 3 - Root of desired tree has been reduced to a single node.  Append a node to the result of hbrs.
  -- max-frm (suc (suc n)) (((π , ._ , tt*) , ._ , tt*) , nd .tt* (nd .tt* hbrs [ tt* , ._ , lf .tt* ]) tt* , tt*) =
  --   {!!} , {!!} , {!!}
  
  -- -- Dimension ≥ 3 - Still climbing the base box.  Graft and continue.
  -- max-frm (suc (suc n)) (((π , ._ , tt*) , ._ , tt*) , nd .tt* (nd .tt* hbrs [ tt* , ._ , nd .tt* lclhbrs tt* ]) tt* , tt*) =
  --   {!!} , {!!} , {!!}



  -- -- Dimension 3 - A drop on an arrow
  -- max-frm (suc (suc zero)) (((tt* , tt* , tt*) , ._ , tt*) , lf .tt* , tt*) =
  --   max-frm (suc zero) 2-globe , η _ {f = max-frm (suc zero) 2-globe} (lf-cell arr) , lf-cell arr

  -- -- Dimension 3 - A globe on a drop 
  -- max-frm (suc (suc zero)) (((tt* , tt* , tt*) , ._ , tt*) , nd .tt* (lf .tt*) tt* , tt*) = {!!}

  -- -- Dimension 3 - Root is now a single box
  -- max-frm (suc (suc zero)) (((tt* , tt* , tt*) , ._ , tt*) , nd .tt* (nd .tt* [ tt* , .tt* , horiz ] [ tt* , ._ , lf .tt* ]) tt* , tt*) =
  --   max-frm 1 (arr , canopy (tt* , tt* , tt*) (nd tt* [ tt* , tt* , horiz ] [ tt* , η (snd (fst (𝕋 3))) tt* , lf tt* ]) , tt*) ,
  --   nd _ [ _ , _ , {!horiz-ih .snd .fst!} ] (nd-cell-there {!!} {!horiz-ih .snd .fst!} {!!} {!!}) ,
  --   nd-cell-here arr (nd tt* [ tt* , tt* , horiz ] [ tt* , η (snd (fst (𝕋 3))) tt* , lf tt* ])

  --   where horiz-ih : Frm (Repr₀ (suc (suc zero)) ((arr , canopy arr horiz , tt*) , nd tt* horiz tt* , tt*))
  --         horiz-ih = max-frm (suc (suc zero)) ((arr , canopy arr horiz , tt*) , nd tt* horiz tt* , tt*) 

  -- max-frm (suc (suc zero)) (((tt* , tt* , tt*) , ._ , tt*) , nd .tt* (nd .tt* [ tt* , .tt* , horiz ] [ tt* , ._ , nd .tt* hbrs tt* ]) tt* , tt*) = {!!}

  -- Dimension 3 - Non-trivial outgoing branch
  --
  --   horiz - a list containing the remaining vertical brances
  --   vert - the current vertical branch
  -- 
  -- max-frm (suc (suc zero)) (((tt* , tt* , tt*) , ._ , tt*) , nd .tt* (nd .tt* [ tt* , .tt* , horiz ] vert) tt* , tt*) =
  --   max-frm (suc zero) (arr , canopy arr (nd tt* [ tt* , tt* , horiz ] vert) , tt*) , src-pd , tgt-cell

  --   where tgt-cell : Face₀ arr (canopy arr (nd tt* [ tt* , tt* , horiz ] vert))
  --                      (nd tt* (nd tt* [ tt* , tt* , horiz ] vert) tt*)
  --                      (max-frm (suc zero) (arr , canopy arr (nd tt* [ tt* , tt* , horiz ] vert) , tt*))
  --         tgt-cell = nd-cell-here arr (nd tt* [ tt* , tt* , horiz ] vert)

  --         vert-ih : Frm (Repr₀ (suc (suc zero)) ((arr , lvs vert , tt*) , br vert , tt*))
  --         vert-ih = max-frm (suc (suc zero)) ((arr , lvs vert , tt*) , br vert , tt*)

  --         horiz-ih : Frm (Repr₀ (suc (suc zero)) ((arr , canopy arr horiz , tt*) , nd tt* horiz tt* , tt*))
  --         horiz-ih = max-frm (suc (suc zero)) ((arr , canopy arr horiz , tt*) , nd tt* horiz tt* , tt*) 

  --         vert-src : Pd (Face₀ arr (lvs vert) (br vert)) (fst vert-ih)
  --         vert-src = vert-ih .snd .fst

  --         horiz-src : Pd (Face₀ arr (canopy arr horiz) (nd tt* horiz tt*)) (fst horiz-ih)
  --         horiz-src = horiz-ih .snd .fst

  --         -- src-pd : Pd (Face₀ arr (canopy arr (nd tt* [ tt* , tt* , horiz ] vert))
  --         --                        (nd tt* (nd tt* [ tt* , tt* , horiz ] vert) tt*))
  --         --                        (max-frm 1 (arr , canopy arr (nd tt* [ tt* , tt* , horiz ] vert) , tt*))

  --         src-pd : Pd (Face₀ arr (γ (const Unit*) (lvs vert)
  --                                   (λ p → map-src tt* (const Unit*) (const Unit*) tt* (const tt*) ,
  --                                          μ (tt* , (λ q → q)) (Branch (const Unit*)) (const Unit*) horiz (λ q → lvs (PdInhab (Branch (const Unit*)) horiz q))))
  --                                (nd tt* (nd tt* [ tt* , tt* , horiz ] vert) tt*))
  --                                (max-frm 1 (arr , canopy arr (nd tt* [ tt* , tt* , horiz ] vert) , tt*))
          
  --         src-pd = {!!} 


  --
  --  Next dimension 
  --

  -- Repr₁ : (n : ℕ) (π : 𝒪 (suc n)) → Frm (Repr₀ n π) → Type

  -- data Face₁ : {n : ℕ} (π : 𝒪 n)
  --   (σ : Src (const Unit*) π)
  --   (τ : Pd (const Unit*) (π , σ , tt*))
  --   → Frm (Repr₀ n (π , σ , tt*) , Face₀ π σ τ) → Type where

  --   nd-cell : {n : ℕ} (π : 𝒪 n) (brs : Src (Branch (const Unit*)) π)
  --     → Face₁ π (canopy π brs) (nd tt* brs tt*)
  --             (max-frm n (π , canopy π brs , tt*) ,
  --             -- BUG! No, I don't think this is right.  It should
  --             -- be the *local* canopy in this case.
  --               max-frm-canopy n π brs ,
  --               (nd-cell π brs))

  --   tgt-cell : {n : ℕ} (π : 𝒪 n) (σ : Src (const Unit*) π) (τ : Pd (const Unit*) (π , σ , tt*))
  --     → Face₁ π σ τ (max-frm (suc n) ((π , σ , tt*) , τ , tt*)) 

  -- Repr₁ zero π _ = Unit ⊎ Unit
  -- Repr₁ (suc n) ((π , σ , tt*) , τ , tt*) = Face₁ π σ τ

