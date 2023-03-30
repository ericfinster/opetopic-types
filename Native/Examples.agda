
open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType

module Native.Examples where

  arr-dec : ∀ {ℓ}
    → {P : Pos arrₒ → Type ℓ}
    → (this* : P this)
    → (p : Pos arrₒ) → P p
  arr-dec this* this = this*

  lf-dec : ∀ {ℓ n} {ο : 𝕆 n}
    → {P : Pos (lfₒ ο) → Type ℓ}
    → (p : Pos (lfₒ ο)) → P p
  lf-dec ()

  nd-dec : ∀ {ℓ n} {ο : 𝕆 n} {ρ : ℙ ο}
    → {δ : (p : Pos ρ) → Tr (Typ ρ p)}
    → {P : Pos (ndₒ ρ δ) → Type ℓ}
    → (here* : P here)
    → (there* : (p : Pos ρ) (q : Pos (snd (δ p))) → P (there p q))
    → (p : Pos (ndₒ ρ δ)) → P p
  nd-dec here* there* here = here*
  nd-dec here* there* (there p q) = there* p q


  -- Examples

  object : 𝕆 0
  object = objₒ 

  arrow : 𝕆 1
  arrow = _ ∣ arrₒ 

  drop : 𝕆 2
  drop = objₒ ∣ arrₒ ∣ lfₒ objₒ

  glob : 𝕆 2
  glob = objₒ ∣ arrₒ ∣ ndₒ arrₒ (arr-dec (ηₒ objₒ , lfₒ objₒ))

  simplex : 𝕆 2
  simplex = objₒ ∣ arrₒ ∣ ndₒ arrₒ (arr-dec (ηₒ objₒ , ndₒ arrₒ (arr-dec (ηₒ objₒ , lfₒ objₒ))))

  mickey : 𝕆 3
  mickey = simplex ∣ ndₒ (ndₒ arrₒ (arr-dec (ηₒ objₒ , ndₒ arrₒ (arr-dec (ηₒ objₒ , lfₒ objₒ)))))
    (nd-dec ({!!} , ndₒ (ndₒ arrₒ (arr-dec (ηₒ objₒ , lfₒ objₒ))) (nd-dec ({!!} , {!!}) λ _ p → {!!}))
            {!!}) 
  
  Objects : (X : 𝕆Type ℓ-zero 3) → Type ℓ-zero
  Objects (((○ ∥ X₀) ∥ X₁) ∥ X₂) = X₀ (objₒ , ●)

  Arrows : (X : 𝕆Type ℓ-zero 3) (x y : Objects X) → Type ℓ-zero
  Arrows (((○ ∥ X₀) ∥ X₁) ∥ X₂) x y = X₁ ((objₒ ∣ arrₒ) , (● ►⟦ y ∣ arrₒ , arr , arr-dec x ⟧))   


