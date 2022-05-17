{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.Shapeless where
  
  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ
  Src : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → (Y : Frm X → Type ℓ)
    → Frm X → Type ℓ 

  src-map : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → (Y Z : Frm X → Type ℓ)
    → (σ : (f : Frm X) → Y f → Z f)
    → (f : Frm X)
    → Src X Y f → Src X Z f 

  η : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → (Y : Frm X → Type ℓ)
    → (f : Frm X) (y : Y f)
    → Src X Y f 

  μ : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → (Y : Frm X → Type ℓ)
    → {f : Frm X}
    → Src X (Src X Y) f
    → Src X Y f 

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (Xₙ , Xₛₙ) = 
    Σ[ f ∈ Frm Xₙ ]
    Σ[ tgt ∈ Xₛₙ f ] 
    Src Xₙ Xₛₙ f

  -- Gotcha.  So we'll need the functorial action.  And then we just
  -- take a single argument which is the recursive guy, and we need
  -- to compute the result.

  -- Wow, so this is really interesting....

  data Pd {n ℓ} (X : 𝕆Type (suc n) ℓ) (Y : Frm X → Type ℓ) : Frm X → Type ℓ where

    lf : (f : Frm (fst X)) (x : snd X f)
      → Pd X Y (f , x , η (fst X) (snd X) f x) 

    nd : (f : Frm (fst X)) 
      → (pd : Src (fst X) (λ f'
          → Σ[ τ' ∈ snd X f' ]
            Σ[ σ' ∈ Src (fst X) (snd X) f' ]
            Pd X Y (f' , τ' , σ')) f)
      → (τ : snd X f)
      → (θ : Y (f , τ , src-map (fst X) _ _ (λ _ → fst) f pd))
      → Pd X Y (f , τ , μ (fst X) (snd X) (src-map (fst X) _ _ (λ _ → fst ∘ snd) f pd))

  Src {zero} X Y f = Y tt*
  Src {suc n} X Y = Pd X Y

  src-map = {!!} 

  η = {!!}
  μ = {!!} 




  -- data LfCns {n ℓ} (X : 𝕆Type (suc n) ℓ) {𝑜 : 𝒪 n} : Frm X (𝑜 ∣ ηₒ 𝑜) → Type ℓ where

  --   lf : {f : Frm (fst X) 𝑜} (x : (snd X) f)
  --     → LfCns X (f , x , η (fst X) f , const x) 

  -- data NdCns {n ℓ} (X : 𝕆Type (suc n) ℓ)
  --       (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
  --       (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --       (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
        
  --   : Frm X (𝑜 ∣ μₒ 𝑝 𝑞) → Type ℓ where

  --   nd : {f : Frm (fst X) 𝑜} (x : (snd X) f) (c : Cns (fst X) f 𝑝)
  --     → (y : (p : Pos 𝑝) → (snd X) (Shp (fst X) c p))
  --     → (d : (p : Pos 𝑝) → Cns (fst X) (Shp (fst X) c p) (𝑞 p))
  --     → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → (snd X) (Shp (fst X) (d p) q))
  --     → (ψ : (p : Pos 𝑝) → Cns X (Shp (fst X) c p , y p , d p , z p) (𝑟 p)) 
  --     → NdCns X 𝑜 𝑝 𝑞 𝑟 (f , x , μ (fst X) c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) 
