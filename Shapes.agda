{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module Shapes (M : 𝕄) (X₀ : Idx M → Set) where

  --
  --  TODO : SliceUnfold has be rewritten to be generic.  Use those definitions.
  --

  ShpSlc₁ : 𝕄
  ShpSlc₁ = Slice (Pb M X₀)

  module Dim₁ (X₁ : Idx ShpSlc₁ → Set) where

    arrow : {i : Idx M} (j₀ j₁ : X₀ i) → Set
    arrow {i} j₀ j₁ = X₁ ((i , j₁) , η M i , cst j₀) 

    --
    --  Some linear sequences 
    --
    
    Seq : {i : Idx M} → X₀ i → X₀ i → Set
    Seq {i} j₀ j₁ = ⟦ ShpSlc₁ ⟧ X₁ ((i , j₁) , η M i , cst j₀)

    nil-seq : {i : Idx M} {j : X₀ i} → Seq j j
    nil-seq {i} {j} = lf (i , j) , ⊥-elim

    cns-seq : {i : Idx M} {j₀ j₁ j₂ : X₀ i}
      → Seq j₀ j₁ → arrow j₁ j₂
      → Seq j₀ j₂
    cns-seq {i} {j₀} {j₁} {j₂} (s , ϕ) f = tr , dec 

      where tr : Cns ShpSlc₁ ((i , j₂) , η M i , cst j₀)
            tr = nd (η M i , cst j₁) (cst (η M i , cst j₀)) (cst s)

            dec : (p : Pos ShpSlc₁ tr) → X₁ (Typ ShpSlc₁ tr p)
            dec true = f
            dec (inr (p , q)) = ϕ q
            
    multiarrow : (i : Idx M) (c : Cns M i)
      → (x : X₀ i) (χ : (p : Pos M c) → X₀ (Typ M c p))
      → Set
    multiarrow i c x χ = X₁ ((i , x) , (c , χ)) 

    --
    --  Dimension 2
    --

    ShpSlc₂ : 𝕄
    ShpSlc₂ = Slice (Pb ShpSlc₁ X₁)
    
    module Dim₂ (X₂ : Idx ShpSlc₂ → Set) where

      null-homotopy : {i : Idx M} {j : X₀ i}
        → arrow j j → Set
      null-homotopy {i} {j} f =
        X₂ ((((i , j) , η M i , cst j) , f) ,
          nil-seq) 

      disc : {i : Idx M} {j₀ j₁ : X₀ i}
        → arrow j₀ j₁ → arrow j₀ j₁ → Set
      disc {i} {j₀} {j₁} f g =
        X₂ ((((i , j₁) , η M i , cst j₀) , g) ,
          cns-seq nil-seq f) 
      
      simplex : {i : Idx M} {j₀ j₁ j₂ : X₀ i}
        → (f : arrow j₀ j₁) (g : arrow j₁ j₂)
        → (h : arrow j₀ j₂) → Set
      simplex {i} {j₀} {j₁} {j₂} f g h =
        X₂ ((((i , j₂) , η M i , cst j₀) , h) ,
              cns-seq (cns-seq nil-seq f) g)

