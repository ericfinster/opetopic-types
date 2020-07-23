{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb
open import OpetopicType

module MonadEqv where

  record _≃ₘ_ (M N : 𝕄) : Set where
    field

      Idx≃ : Idx M ≃ Idx N
      Cns≃ : (i : Idx M) → Cns M i ≃ Cns N (–> Idx≃ i) 
      Pos≃ : (i : Idx M) (c : Cns M i)
        → Pos M c ≃ Pos N (–> (Cns≃ i) c)

      -- Should we do this the other way and derive what we need below?
      Typ≃ : (i : Idx M) (c : Cns M i) (p : Pos N (–> (Cns≃ i) c))
        → –> Idx≃ (Typ M c (<– (Pos≃ i c) p)) == Typ N (–> (Cns≃ i) c) p

      η≃ : (i : Idx M)
        → –> (Cns≃ i) (η M i) == η N (–> Idx≃ i) 

      η-pos≃ : (i : Idx M)
        → –> (Pos≃ i (η M i)) (η-pos M i) == transport (Pos N) (! (η≃ i)) (η-pos N (–> Idx≃ i))

      -- Etc ...

      μ≃ : (i : Idx M) (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → –> (Cns≃ i) (μ M c δ) == μ N (–> (Cns≃ i) c)
          (λ p → transport (Cns N) (Typ≃ i c p) (–> (Cns≃ (Typ M c (<– (Pos≃ i c) p))) (δ (<– (Pos≃ i c) p))))

  open _≃ₘ_ public
  
  OpInv : (M N : 𝕄) (eqv : M ≃ₘ N)
    → OpetopicType M → OpetopicType N 
  Ob (OpInv M N eqv X) = (Ob X) ∘ (<– (Idx≃ eqv)) 
  Hom (OpInv M N eqv X) = {!OpInv (Slice!}
