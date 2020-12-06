{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module SliceMonad where

  --
  --  Slice Monad Definition
  --

  Idxₛ : (M : 𝕄) → Set
  Idxₛ M = Σ (Idx M) (Cns M)
  
  data Cnsₛ (M : 𝕄) : Idxₛ M → Set where

    lf : (i : Idx M) → Cnsₛ M (i , η M i)

    nd : {i : Idx M} (c : Cns M i) 
      → (δ : {j : Idx M} (p : Pos M c j) → Cns M j )
      → (ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p))
      → Cnsₛ M (i , μ M c δ)

  data Posₛ (M : 𝕄) : {i : Idxₛ M} (c : Cnsₛ M i) → Idxₛ M → Set where
  
    nd-here : {i : Idx M} {c : Cns M i}
      → {δ : {j : Idx M} (p : Pos M c j) → Cns M j}
      → {ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p)}
      → Posₛ M (nd c δ ε) (i , c)
      
    nd-there : {i : Idx M} {c : Cns M i}
      → {δ : {j : Idx M} (p : Pos M c j) → Cns M j}
      → {ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p)}
      → {j : Idx M} {k : Idx M} {d : Cns M k}
      → (p : Pos M c j) (q : Posₛ M (ε p) (k , d))
      → Posₛ M (nd c δ ε) (k , d)

  --
  --  Grafting Definition
  --
  
  γ : (M : 𝕄) {i : Idx M} {c : Cns M i}
    → (ρ : Cnsₛ M (i , c))
    → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
    → (ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p))
    → Cnsₛ M (i , μ M c δ)

  γ-pos-inl : (M : 𝕄) {i : Idx M} {c : Cns M i}
    → (ρ : Cnsₛ M (i , c))
    → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
    → (ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p))
    → {k : Idxₛ M} (P : Posₛ M ρ k)
    → Posₛ M (γ M ρ δ ε) k 

  γ-pos-inr : (M : 𝕄) {i : Idx M} {c : Cns M i}
    → (ρ : Cnsₛ M (i , c))
    → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
    → (ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p))
    → {j : Idx M} (p : Pos M c j)
    → {k : Idxₛ M} (q : Posₛ M (ε p) k)
    → Posₛ M (γ M ρ δ ε) k 

  γ-pos-elim : (M : 𝕄) {i : Idx M} {c : Cns M i}
    → (ρ : Cnsₛ M (i , c))
    → (δ : {j : Idx M} (p : Pos M c j) → Cns M j)
    → (ε : {j : Idx M} (p : Pos M c j) → Cnsₛ M (j , δ p))
    → (P : {k : Idxₛ M} → Posₛ M (γ M ρ δ ε) k → Set)
    → (inl* : {k : Idxₛ M} (p : Posₛ M ρ k)
            → P (γ-pos-inl M ρ δ ε p))
    → (inr* : {j : Idx M} (p : Pos M c j)
            → {k : Idxₛ M} (q : Posₛ M (ε p) k)
            → P (γ-pos-inr M ρ δ ε p q))
    → {k : Idxₛ M} (p : Posₛ M (γ M ρ δ ε) k) → P p 

  --
  --  Slice Implementation
  --

  ηₛ : (M : 𝕄) → (i : Idxₛ M) → Cnsₛ M i
  ηₛ M (i , c) = 
    let η-dec {j} p = η M j
        lf-dec {j} p = lf j 
    in nd c η-dec lf-dec 

  μₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
    → (δ : {j : Idxₛ M} (p : Posₛ M c j) → Cnsₛ M j)
    → Cnsₛ M i
  μₛ M (lf τ) κ = lf τ
  μₛ M (nd c δ ε) κ = 
    γ M (κ nd-here) δ
    (λ {j} p → μₛ M (ε p) (λ {k} q → κ {k} (nd-there p q)))

  --
  --  Grafting Implementation
  --

  γ = {!!} 
  γ-pos-inl = {!!} 
  γ-pos-inr = {!!} 
  γ-pos-elim = {!!} 

