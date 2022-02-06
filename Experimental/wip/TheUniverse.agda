--
--  TheUniverse.agda - The Internal Universe in Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Prelude
open import Opetopes
open import OpetopicType
open import OpetopicType2
open import OpetopicMap

module TheUniverse where

  𝒰ₒ : (ℓ : Level) (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝒱ₒ : (ℓ : Level) (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝓊 : (ℓ : Level) (n : ℕ) → 𝒱ₒ ℓ n ⇒ 𝒰ₒ ℓ n

  𝒰ₒ ℓ zero = lift tt
  𝒰ₒ ℓ (suc n) = 𝒰ₒ ℓ n , λ {o} f →
    (f' : Frm (𝒱ₒ ℓ n) o) (e : Frm⇒ (𝓊 ℓ n) f' ≡ f)
    → Type ℓ
  
  𝒱ₒ ℓ zero = lift tt
  𝒱ₒ ℓ (suc n) = 𝒱ₒ ℓ n , λ {o} f* →
    Σ ((f' : Frm (𝒱ₒ ℓ n) o) (e : Frm⇒ (𝓊 ℓ n) f' ≡ Frm⇒ (𝓊 ℓ n) f*) → Type ℓ) (λ F → F f* refl)
  
  𝓊 ℓ zero = lift tt
  𝓊 ℓ (suc n) = 𝓊 ℓ n , λ {o} {f} X → fst X

  --
  -- Σ of opetopic types
  --

  Σₒ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : X ⇒ 𝒰ₒ ℓ₁ n) → 𝕆 (ℓ-max ℓ₀ ℓ₁) n

  fstₒ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : X ⇒ 𝒰ₒ ℓ₁ n)
    → Σₒ X Y ⇒ X

  {-# TERMINATING #-} 
  sndₒ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : X ⇒ 𝒰ₒ ℓ₁ n)
    → Σₒ X Y ⇒ 𝒱ₒ ℓ₁ n

  commₒ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : X ⇒ 𝒰ₒ ℓ₁ n)
    → 𝓊 ℓ₁ n ⊚ sndₒ X Y ≡ Y ⊚ fstₒ X Y 

  Σₒ {ℓ₀} {ℓ₁} {zero} X Y = lift tt
  Σₒ {ℓ₀} {ℓ₁} {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Σₒ Xₙ Yₙ , λ φ → Σ (Xₛₙ (Frm⇒ (fstₒ Xₙ Yₙ) φ)) (λ x →
                       Yₛₙ x (Frm⇒ (sndₒ Xₙ Yₙ) φ) (λ i → Frm⇒ (commₒ Xₙ Yₙ i) φ))
  
  fstₒ {n = zero} X Y = lift tt
  fstₒ {n = suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    fstₒ Xₙ Yₙ , fst

  sndₒ {n = zero} X Y = lift tt
  sndₒ {n = suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    sndₒ Xₙ Yₙ , λ { {o} {f} (x , y) → (λ φ eq → Yₛₙ x φ (eq ∙ (λ i → Frm⇒ (commₒ Xₙ Yₙ i) f))) , {!!} }

  commₒ = {!!}

  --
  --  Can we do Π ? 
  --

  Πₒ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : X ⇒ 𝒰ₒ ℓ₁ n) → 𝕆 (ℓ-max ℓ₀ ℓ₁) n

  evₒ : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆 ℓ₀ n) (Y : X ⇒ 𝒰ₒ ℓ₁ n)
    → (Πₒ X Y) ×ₒ X ⇒ 𝒱ₒ ℓ₁ n 

  Πₒ {n = zero} X Y = lift tt
  Πₒ {n = suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Πₒ Xₙ Yₙ , λ φ → {o : 𝒪 n} {f : Frm Xₙ o} (x : Xₛₙ f) → Yₛₙ x {!Frm⇒ (evₒ Xₙ Yₙ)!} {!!}

  evₒ = {!!}
  
  --
  --  A first test: suppose I have an opetopic type.  Does this
  --  determine a point of the universe?
  --

  -- classify : ∀ {ℓ} (n : ℕ) → 𝕆 ℓ n → 𝕋 {ℓ} n ⇒ 𝒰ₒ {ℓ} n

  -- unclassify : ∀ {ℓ} (n : ℕ) (X : 𝕆 ℓ n) {o : 𝒪 n} 
  --   → (t : Frm (𝕋 n) o) (f : Frm (𝒱ₒ n) o)
  --   → (e : Frm⇒ (𝓊 n) f ≡ Frm⇒ (classify n X) t)
  --   → Frm X o 

  -- classify O _ = tt
  -- classify (S n) (Xₙ , Xₛₙ) = classify n Xₙ ,
  --   λ {o} {f} _ f' e → Xₛₙ (unclassify n Xₙ f f' e)
  
  -- unclassify O X t f e = tt
  -- unclassify (S n) (Xₙ , Xₛₙ) t f e = {!!}

  -- Yeah, so you need to see that pullbacks can be computed pointwise
  -- in trees.  But I think characterizing the identity types of frames
  -- and trees and so on will be done for a fixed n.  So I don't see
  -- that this will necessarily have any coherence problems.

  -- 𝒰ₒ' : (ℓ : Level) (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  
  -- ℯ𝓁 : (ℓ : Level) (n : ℕ) {o : 𝒪 n} (f : Frm (𝒰ₒ' ℓ n) o)
  --   → Type ℓ

  -- ℯ𝓁-cns : (ℓ : Level) (n : ℕ) {o : 𝒪 n} {ρ : 𝒫 o} 
  --   → (f : Frm (𝒰ₒ' ℓ n) o) (e : ℯ𝓁 ℓ n f)
  --   → (c : Cns (𝒰ₒ' ℓ n) f ρ) → Type ℓ

  -- ℯ𝓁-bdy : (ℓ : Level) (n : ℕ) {o : 𝒪 n} {ρ : 𝒫 o} 
  --   → (f : Frm (𝒰ₒ' ℓ n) o) (e : ℯ𝓁 ℓ n f)
  --   → (c : Cns (𝒰ₒ' ℓ n) f ρ) (σ : ℯ𝓁-cns ℓ n f e c)
  --   → (p : Pos ρ) → ℯ𝓁 ℓ n (Shp (𝒰ₒ' ℓ n) c p) 

  -- 𝒰ₒ' ℓ zero = lift tt
  -- 𝒰ₒ' ℓ (suc n) = 𝒰ₒ' ℓ n , λ {o} φ → ℯ𝓁 ℓ n φ → Type ℓ
  
  -- ℯ𝓁 ℓ zero f = Lift Unit
  -- ℯ𝓁 ℓ (suc n) {o , ρ} ⟪ f , c , τ , σ ⟫ =
  --   Σ (ℯ𝓁 ℓ n f) (λ e →
  --   Σ (ℯ𝓁-cns ℓ n f e c) (λ b → τ e × ((p : Pos ρ) → σ p (ℯ𝓁-bdy ℓ n f e c b p))))

  -- ℯ𝓁-cns ℓ zero f e c = Lift Unit
  -- ℯ𝓁-cns ℓ (suc n) ⟪ f , ._ , X , ._ ⟫ (e₀ , e₁ , l , r) (lf {o} .X) = {!!} -- r (ηₒ-pos o) ≡ l
  -- ℯ𝓁-cns ℓ (suc n) ._ (e₀ , e₁ , s , t) (nd φ ι κ δ ν ε) = {!!}
  
  -- ℯ𝓁-bdy = {!!} 
