{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT

module Universe where

  -- So, my idea here is to see how far one can
  -- get in decoding, not to a polynomial, but
  -- to an opetopic type!

  data Mnd : Type₁ 

  Idx : Mnd → Type₀
  
  data Mnd where
    𝕌 : Mnd 
    pb : (M : Mnd) (X : Idx M → Type₀) → Mnd
    slc : Mnd → Mnd

  record OpType (M : Mnd) : Type₁ where
    coinductive
    field

      Ob : Idx M → Type₀
      Hom : OpType (slc (pb M Ob))

  open OpType

  ⟦_⟧ : (M : Mnd) → OpType (slc (pb 𝕌 (cst (Idx M))))

  Idx 𝕌 = ⊤
  Idx (pb M X) = Σ (Idx M) X
  Idx (slc M) = Σ (Idx M) (λ i → Ob ⟦ M ⟧ {!!})

  Ob ⟦ 𝕌 ⟧ = cst Type₀
  Hom ⟦ 𝕌 ⟧ = {!!}
  Ob ⟦ pb M X ⟧ = {!!}
  Hom ⟦ pb M X ⟧ = {!!}
  Ob ⟦ slc M ⟧ = {!!}
  Hom ⟦ slc M ⟧ = {!!}


  -- Uh, yeah, this shows how your ideas are still not quite clear.
  -- At some point, you need this notion of higher telescope.  It
  -- just has to come into play somehow.

  -- The problem is you are now confusing to points of view: the one
  -- where 

  -- postulate

  --   Σ-assoc-rw : (X : Set) (P : X → Set)
  --     → (Q : (x : X) → P x → Set)
  --     → Σ (Σ X P) (λ { (x , p) → Q x p }) ↦ Σ X (λ x → Σ (P x) (λ p → Q x p))

    
  -- -- So, here are telescopes
  -- data Tele : Type₀ → Type₁ where
  --   ε : Tele ⊤
  --   σ : (X : Type₀) (P₀ : X → Type₀)
  --       → (P₁ : (x : X) → Tele (P₀ x))
  --       → Tele (Σ X P₀)

  -- -- Their places, which are partial substitutions.
  -- TelePlc : (X : Set₀) (T : Tele X) → Set₀
  -- TelePlc .⊤ ε = ⊥
  -- TelePlc .(Σ X P₀) (σ X P₀ P₁) = ⊤ ⊔ (Σ X (λ x → TelePlc (P₀ x) (P₁ x)))

  -- -- And their types, which pull back the sequence along a
  -- -- partial substitution.
  -- TeleTyp : (X : Set₀) (T : Tele X) (t : TelePlc X T) → Set₀
  -- TeleTyp .⊤ ε ()
  -- TeleTyp .(Σ X P₀) (σ X P₀ P₁) true = X
  -- TeleTyp .(Σ X P₀) (σ X P₀ P₁) (inr (x , T)) = TeleTyp (P₀ x) (P₁ x) T
