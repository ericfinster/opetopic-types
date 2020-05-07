{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Universe

module FiberedMonad where

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (i : Idx M) (P : Set) (τ : P → Idx M) → Set 

    η : (M : 𝕄) (i : Idx M) → Cns M i ⊤ (cst i)

    μ : (M : 𝕄) (i : Idx M)
      → (P : Set) (τ₀ : P → Idx M) (c : Cns M i P τ₀)
      → (Q : P → Set) (τ₁ : (p : P) → Q p → Idx M)
      → (d : (p : P) → Cns M (τ₀ p) (Q p) (τ₁ p))
      → Cns M i (Σₛ P Q) (uncurryₛ τ₁)

  Idxₛ : (M : 𝕄) → Set
  Idxₛ M = Σ (Idx M) (λ i → Σ Set (λ P → Σ (P → Idx M) λ τ → Cns M i P τ))

  data Cnsₛ (M : 𝕄) : Idxₛ M → (Q : Set) → (θ : Q → Idxₛ M) → Set where
    lf : (i : Idx M) → Cnsₛ M (i , ⊤ , cst i , η M i) ⊥ ⊥-elim
    nd : (i : Idx M)
      → (P : Set) (τ₀ : P → Idx M) (c : Cns M i P τ₀)
      → (Q : P → Set) (τ₁ : (p : P) → Q p → Idx M)
      → (d : (p : P) → Cns M (τ₀ p) (Q p) (τ₁ p))
      → (R : P → Set) (ζ : (p : P) → R p → Idxₛ M) 
      → (e : (p : P) → Cnsₛ M (τ₀ p , Q p , τ₁ p , d p) (R p) (ζ p))
      → Cnsₛ M (i , Σₛ P Q , uncurryₛ τ₁ , μ M i P τ₀ c Q τ₁ d) (⊤ ⊔ Σₛ P R)
        (λ { true → i , Σₛ P Q , uncurryₛ τ₁ , μ M i P τ₀ c Q τ₁ d ;
             (inr r) → uncurryₛ ζ r })


  ηₛ : (M : 𝕄) (i : Idxₛ M) → Cnsₛ M i ⊤ (cst i)
  ηₛ M (i , P , τ₀ , c) =
    let η-dec p = η M (τ₀ p)
        lf-dec p = lf (τ₀ p) 
    in {!nd i P τ₀ c (cst ⊤) _ η-dec _ _ lf-dec  !}


  -- η↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Frmₛ M} (f↓ : Frm↓ₛ M↓ f)
  --   → Tree↓ₛ M↓ f↓ (ηₛ M f) (λ { true → f↓ })
  -- η↓ₛ M↓ (f↓ , ϕ↓ , σ↓) =
  --   let η-dec↓ p = η↓ M↓ (ϕ↓ p)
  --       lf-dec↓ p = lf↓ (ϕ↓ p) 
  --   in {!nd↓ ? ? σ↓ η-dec↓ ? lf-dec↓ !}


  -- μ : (M : 𝕄) (i : Idx M)
  --   → (P : Set) (τ₀ : P → Idx M) (c : Cns M i P τ₀)
  --   → (Q : P → Set) (τ₁ : (p : P) → Q p → Idx M)
  --   → (d : (p : P) → Cns M (τ₀ p) (Q p) (τ₁ p))
  --   → Cns M i (Σₛ P Q) (uncurryₛ τ₁)

  -- So, this means the only thing left to do is to implement η and μ
  -- for the slice.  Wacky.


  postulate
  
    Slice : 𝕄 → 𝕄

    Idx-Slice : (M : 𝕄)
      → Idx (Slice M) ↦  Idxₛ M 
    {-# REWRITE Idx-Slice #-}

    Cns-Slice : (M : 𝕄) (i : Idxₛ M) (R : Set) (ζ : R → Idxₛ M)
      → Cns (Slice M) i R ζ ↦ Cnsₛ M i R ζ
    {-# REWRITE Cns-Slice #-}



