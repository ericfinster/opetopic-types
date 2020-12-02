{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module Shapes (M : 𝕄) (X₀ : Idx M → Set) where

  ShpSlc₁ : 𝕄
  ShpSlc₁ = Slice (Pb M X₀)

  module Dim₁ (X₁ : Idx ShpSlc₁ → Set) where

    arrow : {i : Idx M} (j₀ j₁ : X₀ i) → Set
    arrow {i} j₀ j₁ = X₁ ((i , j₁) , η M i , cst j₀) 

    -- Oh.  These are *dotted* seqences.
    Seq : {i : Idx M} → X₀ i → X₀ i → Set
    Seq {i} j₀ j₁ = Cns ShpSlc₁ ((i , j₁) , η M i , cst j₀)
    
    seq₀ : {i : Idx M} (j : X₀ i) → Seq j j
    seq₀ {i} j = lf (i , j)

    seq₁ {i} {j₀ j₁ : X₀ i}
      → Seq j₀ j₁
    seq₁ {i} {j₀} {j₁}

    multiarrow : (i : Idx M) (c : Cns M i)
      → (x : X₀ i) (χ : (p : Pos M c) → X₀ (Typ M c p))
      → Set
    multiarrow i c x χ = X₁ ((i , x) , (c , χ)) 


    ShpSlc₂ : 𝕄
    ShpSlc₂ = Slice (Pb ShpSlc₁ X₁)
    
    module Dim₂ (X₂ : Idx ShpSlc₂ → Set) where

      simplex : {i : Idx M} {j₀ j₁ j₂ : X₀ i}
        → (f : arrow j₀ j₁) (g : arrow j₁ j₂)
        → (h : arrow j₀ j₂) → Set
      simplex {i} {j₀} {j₁} {j₂} f g h =
        X₂ ((((i , j₂) , (η M i , cst j₀)) , h) , seq₂ , dec₂) 

        where seq₂ : Cns ShpSlc₁ ((i , j₂) , (η M i , cst j₀))
              seq₂ = nd (η M i , cst j₁) (cst (η M i , cst j₀))
                        (cst (nd (η M i , cst j₀) (cst (η M i , cst j₀)) (cst (lf (i , j₀))))) 

              dec₂ : (p : Pos ShpSlc₁ seq₂) → X₁ (Typ ShpSlc₁ seq₂ p) 
              dec₂ true = g
              dec₂ (inr (p , true)) = f


