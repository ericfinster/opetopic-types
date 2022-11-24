{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.OpetopicTerm
open import Native.Weakening
open import Native.OpetopicMap

open import Cubical.Foundations.Everything

module Native.Universe where

  -- The universe together with it's canonical fibration
  𝕌 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n
  𝕍 : (ℓ : Level) (n : ℕ) → 𝕆Type↓ ℓ (𝕌 ℓ n)

  𝕌-cell : ∀ {ℓ n} → Idx (𝕌 ℓ n) → Type (ℓ-suc ℓ)
  𝕌-cell {ℓ} {n} i = (i↓ : Idx↓ (𝕍 ℓ n) i) → Type ℓ 

  𝕍-cell : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)}
    → 𝕌-cell i → Idx↓ (𝕍 ℓ n) i → Type ℓ
  𝕍-cell P f↓ = P f↓ 

  𝕌 ℓ zero = ○
  𝕌 ℓ (suc n) = 𝕌 ℓ n ∥ 𝕌-cell
  
  𝕍 ℓ zero = ○↓
  𝕍 ℓ (suc n) = 𝕍 ℓ n ∥↓ 𝕍-cell

  is-fibrant-cell : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)}
    → 𝕌-cell i → Type ℓ
  is-fibrant-cell {i = objₒ , ●} P = 𝟙 _
  is-fibrant-cell {ℓ} {suc n} {(ο ∣ ._) , (f ►⟦ t ∣ s ⟧)} P = 
    (f↓ : Frm↓ (𝕍  ℓ n) f) (s↓ : Src↓ (𝕍 ℓ n) 𝕍-cell s f↓)
     → isContr (Σ[ t↓ ∈ t f↓ ] (P (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)))


  --  The (∞,1)-category of spaces.
  𝕊 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n
  𝕊-fst : ∀ {ℓ n} → 𝕊 ℓ n ⇒ 𝕌 ℓ n 

  𝕊-cell : ∀ {ℓ n} → Idx (𝕊 ℓ n) → Type (ℓ-suc ℓ)
  𝕊-cell (ο , f) = Σ[ P ∈ 𝕌-cell (ο , Frm⇒ 𝕊-fst f) ]
                   is-fibrant-cell P

  𝕊 ℓ zero = ○
  𝕊 ℓ (suc n) = 𝕊 ℓ n ∥ 𝕊-cell 

  𝕊-fst {n = zero} = ■
  𝕊-fst {n = suc n} = 𝕊-fst {n = n} ► fst

