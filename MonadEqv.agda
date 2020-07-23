{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb
open import OpetopicType

module MonadEqv where

  _≃[_]_ : {A B : Set} (P : A → Set) (e : A ≃ B) (Q : B → Set) → Set
  P ≃[ e ] Q  = (a : _) → P a ≃ Q (fst e a)  

  -- Super annoying this is large, but its because
  -- of the η-pos-elim, which quantifies over a family...
  record _≃ₘ_ (M N : 𝕄) : Set₁ where
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

      -- Yikes.  We're going to need some helpers ...
      -- η-pos-elim≃ : (i : Idx M)
      --   → (X : (p : Pos M (η M i)) → Set)
      --   → (η-pos* : X (η-pos M i))
      --   → (p : Pos M (η M i))
      --   → η-pos-elim M i X η-pos* p ==
      --       transport X {!!} (η-pos-elim N (–> Idx≃ i) (λ pn → X (<– (Pos≃ i (η M i)) (transport (Pos N) (! (η≃ i)) pn)))
      --                                                  (transport (X ∘ <– (Pos≃ i (η M i))) (η-pos≃ i)
      --                                                             (transport! X (<–-inv-l (Pos≃ i (η M i)) (η-pos M i)) η-pos*))
      --                                                             (transport (Pos N) (η≃ i) (–> (Pos≃ i (η M i)) p)))

      μ≃ : (i : Idx M) (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → –> (Cns≃ i) (μ M c δ) == μ N (–> (Cns≃ i) c)
          (λ p → transport (Cns N) (Typ≃ i c p) (–> (Cns≃ (Typ M c (<– (Pos≃ i c) p))) (δ (<– (Pos≃ i c) p))))

  open _≃ₘ_ public

  -- These are the main things that we will need ...
  postulate

    Slice≃ : {M N : 𝕄}
      → M ≃ₘ N
      → Slice M ≃ₘ Slice N 

    Pb≃ : {M N : 𝕄} (e : M ≃ₘ N)
      → {X : Idx M → Set}
      → {Y : Idx N → Set}
      → X ≃[ Idx≃ e ] Y
      → Pb M X ≃ₘ Pb N Y 

  OpInv : {M N : 𝕄} (eqv : M ≃ₘ N)
    → OpetopicType N → OpetopicType M
  Ob (OpInv eqv X) = Ob X ∘ –> (Idx≃ eqv)
  Hom (OpInv {M} {N} eqv X) = OpInv spb-eqv (Hom X)

    where spb-eqv : Slice (Pb M (Ob X ∘ –> (Idx≃ eqv))) ≃ₘ Slice (Pb N (Ob X))
          spb-eqv = Slice≃ (Pb≃ eqv (λ i → ide (Ob X (fst (Idx≃ eqv) i)))) 

  -- Equivalences of opetopic types
  record _≃ₒ_[_] {M N : 𝕄} (X : OpetopicType M) (Y : OpetopicType N) (e : M ≃ₘ N) : Set where
    coinductive
    field

      Ob≃ : Ob X ≃[ Idx≃ e ] Ob Y
      Hom≃ : Hom X ≃ₒ Hom Y [ Slice≃ (Pb≃ e Ob≃) ]
