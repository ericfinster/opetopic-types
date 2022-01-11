{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ n} (X : 𝕆 ℓ n) → 𝒪 n → Set ℓ
  Pd : ∀ {ℓ n} (X : 𝕆 ℓ n) {o : 𝒪 n} (f : Frm X o) (τ : 𝒯r o) → Set ℓ 

  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) =
    Σ (𝕆 ℓ n) (λ Xₙ →
      (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ)
  
  Frm X ● = X × X 
  Frm (Xₙ , Xₛₙ) (o ▸ τ) =
    Σ (Frm Xₙ o) (λ f →
      -- But this doesn't make sense: the dimensions are wrong ...
      Pd Xₙ f τ × Xₛₙ o f)

  -- Having a problem with the type of Pd.  What is it?  I think it's
  -- the same problem as with trying to do Frm inductively: since the
  -- n has to vary in the definition, if you make it inductive, then
  -- you will have to carry the whole data of the opetoic type in the
  -- index, and this will force the definition to have the wrong size.

  -- That's a bit annoying.

  -- I guess the alternative is this way you had already developed
  -- using identity types.  Don't really see a reason not to do this.
  -- The other option is that pasting diagrams are only for successors,
  -- and there is a special case ...

  postulate
  
    ηₜ : ∀ {ℓ n} {X : 𝕆 ℓ n}
      → {o : 𝒪 n} (f : Frm X o)
      → Pd X f (η o) 

    μₜ : ∀ {ℓ n} {X : 𝕆 ℓ n}
      → {o : 𝒪 n} (f : Frm X o) (τ : 𝒯r o)
      → (ρ : Pd X f τ)
      → {κ : (p : Pos τ) → 𝒯r (Typ τ p)}
      → (δ : (p : Pos τ) → Frm X (Typ τ p))
      → (ε : (p : Pos τ) → Pd X (δ p) (κ p))
      → Pd X f (μ τ κ) 

  Pd X f arr = ⊤
  Pd X f (lf o) = {!!}
  Pd X f (nd o τ δ ε) = {!!}


  

