{-# OPTIONS --without-K --no-import-sorts --rewriting #-}

open import Agda.Primitive 
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

module MiniUniverse where

  -- So, the idea here is that the universe is just closed under these
  -- natural number operations, and that Σ and ⊔ compute as much as
  -- possible so that we have normal forms and whatnot.

  -- The elimination rule for each type will need to follow the
  -- rewrites for the types themselves.  Doesn't it seem like you
  -- should be able to get enough out of this to make the monad
  -- setup work in the parameterized way?
  
  postulate

    𝕌 : Type
    El : 𝕌 → Type

    -- The empty type
    𝕆 : 𝕌
    𝕆-Elim : ∀ {ℓ} (P : El 𝕆 → Type ℓ)
      → (o : El 𝕆) → P o 

    -- The successor type
    𝕊 : 𝕌 → 𝕌
    Just : {U : 𝕌} → El U → El (𝕊 U)
    None : {U : 𝕌} → El (𝕊 U)

    𝕊-Elim : ∀ {ℓ} (U : 𝕌) (P : El (𝕊 U) → Type ℓ)
      → (Just* : (u : El U) → P (Just u))
      → (None* : P None) 
      → (s : El (𝕊 U)) → P s

    -- Addition
    _⊔_ : 𝕌 → 𝕌 → 𝕌

    -- Dependent multiplication 
    Σ : (U : 𝕌) → (V : El U → 𝕌) → 𝕌 
