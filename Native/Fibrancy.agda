{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Native.Opetopes
open import Native.OpetopicType
open import Native.Term 

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma

module Native.Fibrancy where

  as-frm : ∀ {ℓ n} {X : 𝕆Type ℓ n}
    → {P : Idx X → Type ℓ}
    → Σ[ i ∈ Idx X ] Σ[ s ∈ Src X P i ] (P i)
    → Idx (X , P)
  as-frm ((ο , f) , s , t) =
    (ο , pd s) , f , web s , dec s , t

  is-fibrant-rel : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type ℓ)
    → (Q : Idx (X , P) → Type ℓ)
    → Type ℓ
  is-fibrant-rel X P Q = 
    (i : Idx X) (s : Src X P i)
    → isContr (Σ[ t ∈ P i ] Q (as-frm (i , s , t)))

  is-fibrant : ∀ {ℓ n} (X : 𝕆Type ℓ n) → Type ℓ 
  is-fibrant {ℓ} {zero} X = 𝟙 ℓ
  is-fibrant {ℓ} {suc zero} X = 𝟙 ℓ
  is-fibrant {ℓ} {suc (suc n)} ((X , P) , Q) =
    is-fibrant (X , P) × is-fibrant-rel X P Q 
  
  Obj : ∀ {ℓ n} → 𝕆Type ℓ (suc n) → Type ℓ
  Obj {n = zero} (X₋₁ , X₀) = X₀ (● , ●)
  Obj {n = suc n} (Xₙ , Xₛₙ) = Obj Xₙ

  -- fib-to-term : ∀ {ℓ n} (X : 𝕆Type ℓ (suc n))
  --   → is-fibrant X 
  --   → Obj X → 𝕆Term X 
  -- fib-to-term {n = zero} X is-fib x = ● , cst x
  -- fib-to-term {n = suc n} ((X , P) , Q) (is-fib , is-fib-rel) x =
  --   fib-to-term (X , P) is-fib x , λ (ο , ρ) → need ο ρ 

  --   where ϕ : 𝕆Term X
  --         ϕ = fst (fib-to-term (X , P) is-fib x)

  --         ψ : (ο : 𝕆 n) → P (ο , TermFrm X ϕ ο)
  --         ψ = snd (fib-to-term (X , P) is-fib x)

  --         need : (ο : 𝕆 n) (ρ : ℙ ο) → Q ((ο , ρ) , TermFrm X ϕ ο , TermWeb X ϕ ρ , (λ p → ψ (Typ ρ p)) , ψ ο)
  --         need ο ρ = {!!}
          
  --         from-fib-rel : (ο : 𝕆 n) (ρ : ℙ ο) → isContr (Σ[ t ∈ P (ο , TermFrm X ϕ ο) ]
  --                                                       Q (as-frm ((ο , TermFrm X ϕ ο) ,
  --                                                         ⟪ TermWeb X ϕ ρ , (λ p → ψ (Typ ρ p)) ⟫ , t)))
  --         from-fib-rel ο ρ = is-fib-rel (ο , TermFrm X ϕ ο) ⟪ TermWeb X ϕ ρ , (λ p → ψ (Typ ρ p)) ⟫ 

  --         ψ' : (ο : 𝕆 n) (ρ : ℙ ο) → P (ο , TermFrm X ϕ ο)
  --         ψ' ο ρ = from-fib-rel ο ρ .fst .fst  

  --         have : (ο : 𝕆 n) (ρ : ℙ ο) → Q ((ο , ρ) , TermFrm X ϕ ο , TermWeb X ϕ ρ , (λ p → ψ (Typ ρ p)) , ψ' ο ρ)
  --         have ο ρ = from-fib-rel ο ρ .fst .snd

  --         done-if : (ο : 𝕆 n) (ρ : ℙ ο) → ψ ο ≡ ψ' ο ρ
  --         done-if ο ρ = {!!} 

  
