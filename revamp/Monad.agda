{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Monad where

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (i : Idx M) → Set
    Pos : (M : 𝕄) {i : Idx M}
      → Cns M i → Idx M → Set

    η : (M : 𝕄) (i : Idx M)
      → Cns M i

    η-pos : (M : 𝕄) (i : Idx M)
      → Pos M (η M i) i 

    η-pos-elim : (M : 𝕄) (i : Idx M)
      → (P : (j : Idx M) → Pos M (η M i) j → Set)
      → (d : P i (η-pos M i))
      → (j : Idx M) (p : Pos M (η M i) j) → P j p

    μ : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
      → Cns M i

    μ-pos : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
      → {j : Idx M} (p : Pos M c j)
      → {k : Idx M} (q : Pos M (δ p) k)
      → Pos M (μ M c δ) k

    μ-pos-elim : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
      → (P : (j : Idx M) (p : Pos M (μ M c δ) j) → Set)
      → (d : {j : Idx M} (p : Pos M c j)
           → {k : Idx M} (q : Pos M (δ p) k)
           → P k (μ-pos M c δ p q))
      → (j : Idx M) (p : Pos M (μ M c δ) j) → P j p 

    --
    --  Strict Laws
    --

    -- pos-elim computatinon rules
    η-pos-elim-β : (M : 𝕄) (i : Idx M)
      → (P : (j : Idx M) → Pos M (η M i) j → Set)
      → (η-pos* : P i (η-pos M i))
      → η-pos-elim M i P η-pos* i (η-pos M i) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-elim-β : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
      → (P : (j : Idx M) (p : Pos M (μ M c δ) j) → Set)
      → (μ-pos* : {j : Idx M} (p : Pos M c j)
                → {k : Idx M} (q : Pos M (δ p) k)
                → P k (μ-pos M c δ p q))
      → {j : Idx M} (p : Pos M c j)
      → {k : Idx M} (q : Pos M (δ p) k)
      → μ-pos-elim M c δ P μ-pos* k (μ-pos M c δ p q) ↦ μ-pos* p q
    {-# REWRITE μ-pos-elim-β #-}

    -- μ laws
    μ-unit-right : (M : 𝕄) (i : Idx M)
      → (c : Cns M i)
      → μ M c (λ {j} p → η M j) ↦ c
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : (M : 𝕄) (i : Idx M) 
      → (δ : {j : Idx M} (p : Pos M (η M i) j) → Cns M j)
      → μ M (η M i) δ ↦ δ (η-pos M i)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
      → (ε : {k : Idx M} (p : Pos M (μ M c δ) k) → Cns M k)
      → μ M (μ M c δ) ε ↦ μ M c (λ {j} p → μ M (δ p) (λ {k} q → ε (μ-pos M c δ p q)))
    {-# REWRITE μ-assoc #-} 

    -- Compatible rewrites for position constructors of μ ? 
    

  --
  --  Morphisms of Monads
  --

  record _→ₘ_ (M N : 𝕄) : Set where
    field

      Idx→ : Idx M → Idx N
      Cns→ : (i : Idx M) → Cns M i → Cns N (Idx→ i)
      Pos≃ : (i : Idx M) (c : Cns M i)
        → (j : Idx M) → Pos M c j ≃ Pos N (Cns→ i c) (Idx→ j)

  --
  --  Equivalences of Monads
  --

  record _≃ₘ_ (M N : 𝕄) : Set₁ where
    field

      Idx≃ : Idx M ≃ Idx N
      Cns≃ : (i : Idx M) → Cns M i ≃ Cns N (–> Idx≃ i) 
      Pos≃ : (i : Idx M) (c : Cns M i)
        → (j : Idx M) → Pos M c j ≃ Pos N (–> (Cns≃ i) c) (–> Idx≃ j)

    dec≃ : {i : Idx M} (c : Cns M i)
      → ({j : Idx M} (p : Pos M c j) → Cns M j) ≃
        ({k : Idx N} (p : Pos N (–> (Cns≃ i) c) k) → Cns N k)
    dec≃ = {!!} 
  
    field

      η≃ : (i : Idx M)
        → –> (Cns≃ i) (η M i) == η N (–> Idx≃ i) 

      η-pos≃ : (i : Idx M) 
        → –> (Pos≃ i (η M i) i) (η-pos M i) == η-pos N (–> Idx≃ i)
             [ (λ x → Pos N x (–> Idx≃ i)) ↓ η≃ i ]

      μ≃ : {i : Idx M} (c : Cns M i)
        → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
        → –> (Cns≃ i) (μ M c δ) == μ N (–> (Cns≃ i) c) (–> (dec≃ c) δ)
        
          -- (λ {j} p → transport (Cns N) (<–-inv-r Idx≃ j) (–> (Cns≃ (<– Idx≃ j))
          --            (δ (<– (Pos≃ i c (<– Idx≃ j)) (transport (Pos N (–> (Cns≃ i) c)) (! (<–-inv-r Idx≃ j)) p)))))  

      -- Here is a version which typechecks without transport.  Is this useful?
      μ≃' : {i : Idx M} (c : Cns M i)
        → (δ : {j : Idx N} (p : Pos N (–> (Cns≃ i) c) j) → Cns N j)
        → –> (Cns≃ i) (μ M c (λ {j} p → <– (Cns≃ j) (δ (–> (Pos≃ i c j) p)))) ==
          μ N (–> (Cns≃ i) c) δ

      -- I mean, the thing about it is that it won't work for *morphisms*,
      -- but only for equivalences.

