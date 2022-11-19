--
--  OpetopicType.agda - An Attempt at heterogeneous opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum 

open import Core.Prelude
open import Experimental.UnivElim.Opetopes

module Experimental.UnivElim.OpetopicType where

  Frm : ∀ {n} (𝑜 : 𝒪 n) → Type₁
  Frm↓ : ∀ {n} {𝑜 : 𝒪 n} (F : Frm 𝑜) → Type

  Src : ∀ {n} {𝑜 : 𝒪 n} (F : Frm 𝑜) (𝑝 : 𝒫 𝑜)  → Type₁
  Src↓ : ∀ {n} {𝑜 : 𝒪 n} (F : Frm 𝑜) (𝑝 : 𝒫 𝑜)
    → Src F 𝑝 → Frm↓ F → Type

  Tgt : ∀ {n} {𝑜 : 𝒪 n} (F : Frm 𝑜) → Type₁
  Tgt↓ : ∀ {n} {𝑜 : 𝒪 n} (F : Frm 𝑜)
    → Tgt F → Frm↓ F → Type


  η-tgt : ∀ {n} {𝑜 : 𝒪 n} {F : Frm 𝑜}
    → Src F (ηₒ 𝑜) → Tgt F

  μ-frm : ∀ {n} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))     
      → {F : Frm 𝑜} (S : Src F (μₒ 𝑝 𝑞))
      → (p : Pos 𝑝) → Frm (Typ 𝑝 p)

  μ-src : ∀ {n} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))     
      → {F : Frm 𝑜} (S : Src F (μₒ 𝑝 𝑞))
      → (p : Pos 𝑝) → Src (μ-frm 𝑝 𝑞 S p) (𝑞 p) 

  μ-collect : ∀ {n} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))     
      → {F : Frm 𝑜} (S : Src F (μₒ 𝑝 𝑞))
      → (ϕ : (p : Pos 𝑝) → Tgt (μ-frm 𝑝 𝑞 S p))
      → Src F 𝑝
      
  Frm ● = Unit*
  Frm (𝑜 ∣ 𝑝) = 
    Σ[ F ∈ Frm 𝑜 ]
    Src F 𝑝 × Tgt F 

  Src F objₒ = Type
  Src (F , S , T) lfₒ = η-tgt S ≡ T
  Src (F , S , T) (ndₒ {𝑜 = 𝑜} 𝑝 𝑞 𝑟) =
    Σ[ ϕ ∈ ((p : Pos 𝑝) → Tgt (μ-frm 𝑝 𝑞 S p)) ]
    Σ[ ψ ∈ ((p : Pos 𝑝) → Src (μ-frm 𝑝 𝑞 S p , μ-src 𝑝 𝑞 S p , ϕ p) (𝑟 p)) ]
    Tgt {𝑜 = 𝑜 ∣ 𝑝} (F , μ-collect 𝑝 𝑞 S ϕ , T)

  Tgt F = Frm↓ F → Type

  Frm↓ {𝑜 = ●} F = Unit
  Frm↓ {𝑜 = 𝑜 ∣ 𝑝} (F , S , T) =
    Σ[ f ∈ Frm↓ F ]
    Src↓ F 𝑝 S f × Tgt↓ F T f
  
  Src↓ = {!!}
  
  Tgt↓ F T = T
  
  η-tgt {zero} {●} {F} S _ = S
  η-tgt {suc n} {𝑜 ∣ 𝑝} {F , S , T} (ϕ , ψ , C) = {!!}

  -- Aha! ψ shows that ϕ is no data what so ever.
  -- So we will need a law which says that this situation
  -- reduces back to S.

  -- But this looks suspicious.  This is indeed an equation
  -- in Src's, and looks to be equivalent to a unit law.

  -- Is there any reason to suspect that this won't run away
  -- with itself when you define μ-collect?

  μ-frm = {!!}
  μ-src = {!!} 
  μ-collect = {!!} 

