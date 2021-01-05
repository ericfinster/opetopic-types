{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

open import lib.Relation2

module Finitary where

  is-finite : ∀ {i} → Type i → Type i
  is-finite A = Σ ℕ (λ n → Trunc ⟨-1⟩  (A ≃ Fin n))

  dec-is-prop : ∀ {i} {A : Type i}
    → is-prop A → is-prop (Dec A)
  dec-is-prop p = Dec-level p

  has-pos : (M : 𝕄) {i : Idx M} (c : Cns M i) → Type₀
  has-pos M c = Trunc ⟨-1⟩ (Pos M c) 

  has-pos-is-prop : (M : 𝕄) {i : Idx M} (c : Cns M i)
    → is-prop (has-pos M c)
  has-pos-is-prop M c = Trunc-level
  
  DecMnd : 𝕄 → Type₀
  DecMnd M = {i : Idx M} (c : Cns M i) → Dec (has-pos M c)

  is-finitary : 𝕄 → Type₀
  is-finitary M = {i : Idx M} (c : Cns M i) → is-finite (Pos M c)

  is-leaf : (M : 𝕄) {i : Idx M} {c : Cns M i}
     → Cns (Slice M) (i , c) → Type₀
  is-leaf M σ = ¬ (has-pos (Slice M) σ) 

  is-node : (M : 𝕄) {i : Idx M} {c : Cns M i}
     → Cns (Slice M) (i , c) → Type₀
  is-node M σ = has-pos (Slice M) σ

  slice-is-dec : (M : 𝕄) → DecMnd (Slice M)
  slice-is-dec M (lf i) = inr (Trunc-rec Empty-is-prop (idf ⊥))
  slice-is-dec M (nd c δ ε) = inl [ inl unit ]

  record DecPred {i} (A : Type i) : Type (lsucc i) where
    field
      P : A → Type i
      P-is-prop : (a : A) → is-prop (P a)
      P-is-dec : (a : A) → Dec (P a)

  open DecPred

  SomeOrNone : ∀ {i} (A : Type i) (D : DecPred A) → Type i
  SomeOrNone A D = Trunc ⟨-1⟩ (Σ A (P D)) ⊔ ((a : A) → ¬ (P D a))
  
  -- Need this so that we can extend to finite types
  SomeOrNone-is-prop : ∀ {i} (A : Type i) (D : DecPred A)
    → is-prop (SomeOrNone A D)
  SomeOrNone-is-prop A D = has-level-in sn-aux 

    where sn-aux : (x y : Trunc ⟨-1⟩ (Σ A (P D)) ⊔ ((a : A) → ¬ (P D a))) → has-level ⟨-2⟩ (x == y)
          sn-aux (inl p₁) (inl p₂) = equiv-preserves-level (inl=inl-equiv p₁ p₂ ⁻¹)
            ⦃ has-level-apply Trunc-level p₁ p₂ ⦄ 
          sn-aux (inl p) (inr ϕ) = ⊥-rec (Trunc-rec {B = ⊥} Empty-is-prop (λ pr → ϕ (fst pr) (snd pr)) p)
          sn-aux (inr ϕ) (inl p) = ⊥-rec (Trunc-rec {B = ⊥} Empty-is-prop (λ pr → ϕ (fst pr) (snd pr)) p)
          sn-aux (inr ϕ₁) (inr ϕ₂) = equiv-preserves-level (inr=inr-equiv ϕ₁ ϕ₂ ⁻¹)
            ⦃ has-level-apply (Π-level (λ _ → Π-level (λ _ → Empty-is-prop))) ϕ₁ ϕ₂ ⦄ 

  SomeOrNone-⊔ : ∀ {i} (A B : Type i) (D : DecPred (A ⊔ B))
    → SomeOrNone A (record { P = P D ∘ inl ; P-is-prop = P-is-prop D ∘ inl ; P-is-dec = P-is-dec D ∘ inl })
    → SomeOrNone B (record { P = P D ∘ inr ; P-is-prop = P-is-prop D ∘ inr ; P-is-dec = P-is-dec D ∘ inr })
    → SomeOrNone (A ⊔ B) D
  SomeOrNone-⊔ A B D (inl p) (inl _) = inl (Trunc-rec Trunc-level (λ pr → [ inl (fst pr) , snd pr ]) p)
  SomeOrNone-⊔ A B D (inl p) (inr _) = inl (Trunc-rec Trunc-level (λ pr → [ inl (fst pr) , snd pr ]) p)
  SomeOrNone-⊔ A B D (inr _) (inl p) = inl (Trunc-rec Trunc-level (λ pr → [ inr (fst pr) , snd pr ]) p)
  SomeOrNone-⊔ A B D (inr ϕ) (inr ψ) = inr (Coprod-elim ϕ ψ)

  SomeOrNone-Empty : (D : DecPred Empty) → SomeOrNone Empty D
  SomeOrNone-Empty D = inr ⊥-elim

  SomeOrNone-Unit : (D : DecPred Unit) → SomeOrNone Unit D
  SomeOrNone-Unit D with P-is-dec D tt
  SomeOrNone-Unit D | inl p = inl [ tt , p ]
  SomeOrNone-Unit D | inr ϕ = inr (λ _ → ϕ)
  
  -- First, show that SomeOrNone is compatible with ⊔  *CHECK*
  -- Then show it always holds on empty.  *CHECK*
  -- Then show it always holds on unit.   *CHECK*
  -- Then you get it for all Fin n
  -- Then you get it for all finite types.

  -- Oh, you can also just do this ...
  fin-disc : {n : ℕ} (D : DecPred (Fin n))
    → SomeOrNone (Fin n) D
  fin-disc {O} D = inr (λ { () }) -- Use an elim?
  fin-disc {S n} D with P-is-dec D (n , ltS)
  fin-disc {S n} D | inl p = inl [ (n , ltS) , p ]
  fin-disc {S n} D | inr ϕ with fin-disc {n}
    (record { P = P D ∘ Fin-S ;
              P-is-prop = P-is-prop D ∘ Fin-S ;
              P-is-dec = P-is-dec D ∘ Fin-S })
  fin-disc {S n} D | inr ϕ | inl p = inl (Trunc-rec Trunc-level bump p)

    where bump : Σ (Σ ℕ (_< n)) (λ x → P D (fst x , ltSR (snd x))) →
                 Trunc (S ⟨-2⟩) (Σ (Σ ℕ (_< S n)) (P D))
          bump ((d , <n) , q) = [ (d , ltSR <n) , q ]
          
  fin-disc {S n} D | inr ϕ | inr ψ = inr fin-elim

    where fin-elim : (a : Σ ℕ (_< S n)) → P D a → ⊥
          fin-elim (d , ltS) = ϕ
          fin-elim (d , ltSR l) = ψ (d , l)
          
  -- module _ (M : 𝕄) (M-fin : is-finitary M) where

  --   discrim : (i : Idx M) (c : Cns M i)
  --     → (P : Pos M c → Type₀)
  --     → (P-is-prop : (p : Pos M c) → is-prop (P p))
  --     → (P-is-dec : (p : Pos M c) → Dec (P p))
  --     → Σ (Pos M c) P ⊔ ((p : Pos M c) → ¬ (P p))
  --   discrim i c P P-is-prop P-is-dec = {!!} 

    -- This would be a proposition if you truncate.
