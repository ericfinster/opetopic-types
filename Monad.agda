{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Monad where

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (i : Idx M) → Set

    Pos : (M : 𝕄) {i : Idx M}
      → Cns M i → Set

    Typ : (M : 𝕄) {i : Idx M}
      → (c : Cns M i) (p : Pos M c)
      → Idx M 

    η : (M : 𝕄) (i : Idx M)
      → Cns M i

    η-pos : (M : 𝕄) (i : Idx M)
      → Pos M (η M i)

    η-pos-elim : (M : 𝕄) (i : Idx M)
      → (X : (p : Pos M (η M i)) → Set)
      → (η-pos* : X (η-pos M i))
      → (p : Pos M (η M i)) → X p

    μ : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → Cns M i

    μ-pos : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → Pos M (μ M c δ)

    μ-pos-fst : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → Pos M (μ M c δ) → Pos M c

    μ-pos-snd : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M (μ M c δ))
      → Pos M (δ (μ-pos-fst M c δ p))
      
    --
    --  Stict laws
    --

    -- Typ/Inh laws
    η-pos-typ : (M : 𝕄) (i : Idx M)
      → (p : Pos M (η M i))
      → Typ M (η M i) p ↦ i
    {-# REWRITE η-pos-typ #-}

    η-pos-elim-β : (M : 𝕄) (i : Idx M)
      → (X : (p : Pos M (η M i)) → Set)
      → (η-pos* : X (η-pos M i))
      → η-pos-elim M i X η-pos* (η-pos M i) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-typ : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M (μ M c δ))
      → Typ M (μ M c δ) p ↦ Typ M (δ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-fst-β : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → μ-pos-fst M c δ (μ-pos M c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → μ-pos-snd M c δ (μ-pos M c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}
    
    μ-pos-η : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M (μ M c δ))
      → μ-pos M c δ (μ-pos-fst M c δ p) (μ-pos-snd M c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}
    
    -- μ laws
    μ-unit-right : (M : 𝕄) (i : Idx M)
      → (c : Cns M i)
      → μ M c (λ p → η M (Typ M c p)) ↦ c
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : (M : 𝕄) (i : Idx M) 
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → μ M (η M i) δ ↦ δ (η-pos M i)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → μ M (μ M c δ) ε ↦ μ M c (λ p → μ M (δ p) (λ q → ε (μ-pos M c δ p q)))
    {-# REWRITE μ-assoc #-}

    -- μ pos compatibilities
    μ-pos-unit-right : (M : 𝕄) (i : Idx M)
      → (c : Cns M i)
      → (p : Pos M c) (q : Pos M (η M (Typ M c p)))
      → μ-pos M c (λ p → η M (Typ M c p)) p q ↦ p 
    {-# REWRITE μ-pos-unit-right #-}

    μ-pos-unit-left : (M : 𝕄) (i : Idx M) 
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → (p : Pos M (η M i)) (q : Pos M (δ p))
      → μ-pos M (η M i) δ p q ↦ η-pos-elim M i (λ p → Pos M (δ p) → Pos M (δ (η-pos M i))) (λ p → p) p q 
    {-# REWRITE μ-pos-unit-left #-} 

    μ-pos-assoc : (M : 𝕄) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → (p : Pos M (μ M c δ)) (q : Pos M (ε p))
      → μ-pos M (μ M c δ) ε p q ↦ μ-pos M c
              (λ p → μ M (δ p) (λ q → ε (μ-pos M c δ p q))) (μ-pos-fst M c δ p)
              (μ-pos M (δ (μ-pos-fst M c δ p)) (λ q → ε (μ-pos M c δ (μ-pos-fst M c δ p) q)) (μ-pos-snd M c δ p) q) 
    {-# REWRITE μ-pos-assoc #-}

    μ-pos-fst-unit-right : (M : 𝕄) {i : Idx M}
      → (c : Cns M i) (p : Pos M c)
      → μ-pos-fst M c (λ p → η M (Typ M c p)) p ↦ p 
    {-# REWRITE μ-pos-fst-unit-right #-}

    -- Hmmm.  This doesn't make much sense ...
    -- Really the expression we are rewriting
    -- here should be ill-typed
    μ-pos-fst-unit-left : (M : 𝕄) (i : Idx M) 
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → (p : Pos M (δ (η-pos M i)))
      → μ-pos-fst M (η M i) δ p ↦ η-pos M i
    {-# REWRITE μ-pos-fst-unit-left #-}

    -- μ-pos-fst-assoc : (M : 𝕄) {i : Idx M} (c : Cns M i)
    --   → (δ : (p : Pos M c) → Cns M (Typ M c p))
    --   → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
    --   → μ-pos-fst M (μ M c δ) ε {!!} ↦ {!!}

  Idxₛ : (M : 𝕄) → Set
  Idxₛ M = Σ (Idx M) (Cns M)
  
  data Pd (M : 𝕄) : Idxₛ M → Set where

    lf : (i : Idx M) → Pd M (i , η M i)

    nd : {i : Idx M} (c : Cns M i) 
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M c) → Pd M (Typ M c p , δ p))
      → Pd M (i , μ M c δ)

  Cnsₛ : (M : 𝕄) → Idxₛ M → Set
  Cnsₛ M = Pd M

  Posₛ : (M : 𝕄) {i : Idxₛ M}
    → (c : Cnsₛ M i) → Set
  Posₛ M (lf τ) = ⊥
  Posₛ M (nd c δ ε) = ⊤ ⊔ (Σ (Pos M c) (λ p → Posₛ M (ε p)))

  Typₛ : (M : 𝕄) {i : Idxₛ M}
    → (c : Cnsₛ M i) (p : Posₛ M c)
    → Idxₛ M
  Typₛ M (nd c δ ε) (inl unit) = _ , c 
  Typₛ M (nd c δ ε) (inr (p , q)) = Typₛ M (ε p) q

  --
  --  Free monad signature
  --
  
  γ : (M : 𝕄) {i : Idx M} {c : Cns M i}
    → (ρ : Cnsₛ M (i , c))
    → (δ : (p : Pos M c) → Cns M (Typ M c p))
    → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
    → Cnsₛ M (i , μ M c δ)

  γ-pos-inl : (M : 𝕄) {i : Idx M} {c : Cns M i} 
    → (ρ : Cnsₛ M (i , c))
    → (δ : (p : Pos M c) → Cns M (Typ M c p))
    → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
    → Posₛ M ρ → Posₛ M (γ M ρ δ ε)
  
  γ-pos-inr : (M : 𝕄) {i : Idx M} {c : Cns M i} 
    → (ρ : Cnsₛ M (i , c))
    → (δ : (p : Pos M c) → Cns M (Typ M c p))
    → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
    → (p : Pos M c) (q : Posₛ M (ε p))
    → Posₛ M (γ M ρ δ ε)

  γ-pos-elim : (M : 𝕄) {i : Idx M} {c : Cns M i} 
    → (ρ : Cnsₛ M (i , c))
    → (δ : (p : Pos M c) → Cns M (Typ M c p))
    → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
    → (X : Posₛ M (γ M ρ δ ε) → Set)
    → (inl* : (p : Posₛ M ρ) → X (γ-pos-inl M ρ δ ε p))
    → (inr* : (p : Pos M c) (q : Posₛ M (ε p)) → X (γ-pos-inr M ρ δ ε p q))
    → (p : Posₛ M (γ M ρ δ ε)) → X p

  --
  --  Free monad laws
  --
  
  postulate
  
    -- γ elim comp rules
    γ-pos-elim-inl-β : (M : 𝕄) {i : Idx M} {c : Cns M i} 
      → (ρ : Cnsₛ M (i , c))
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
      → (X : Posₛ M (γ M ρ δ ε) → Set)
      → (inl* : (p : Posₛ M ρ) → X (γ-pos-inl M ρ δ ε p))
      → (inr* : (p : Pos M c) (q : Posₛ M (ε p)) → X (γ-pos-inr M ρ δ ε p q))
      → (p : Posₛ M ρ)
      → γ-pos-elim M ρ δ ε X inl* inr* (γ-pos-inl M ρ δ ε p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : (M : 𝕄) {i : Idx M} {c : Cns M i} 
      → (ρ : Cnsₛ M (i , c))
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
      → (X : Posₛ M (γ M ρ δ ε) → Set)
      → (inl* : (p : Posₛ M ρ) → X (γ-pos-inl M ρ δ ε p))
      → (inr* : (p : Pos M c) (q : Posₛ M (ε p)) → X (γ-pos-inr M ρ δ ε p q))
      → (p : Pos M c) (q : Posₛ M (ε p))
      → γ-pos-elim M ρ δ ε X inl* inr* (γ-pos-inr M ρ δ ε p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}

    -- We don't seem to need the associativity, unit and
    -- distributivity laws for γ to finish type checking.  But it
    -- seems likely that we will need them later when actually working
    -- with these objects ....

  --
  --  Slice implementation 
  --

  ηₛ : (M : 𝕄) → (i : Idxₛ M) → Cnsₛ M i
  ηₛ M (i , c) =
    let η-dec p = η M (Typ M c p)
        lf-dec p = lf (Typ M c p)
    in nd c η-dec lf-dec

  η-posₛ : (M : 𝕄) (i : Idxₛ M)
    → Posₛ M (ηₛ M i)
  η-posₛ M i = inl unit
  
  η-pos-elimₛ : (M : 𝕄) (i : Idxₛ M)
    → (X : (p : Posₛ M (ηₛ M i)) → Set)
    → (η-pos* : X (η-posₛ M i))
    → (p : Posₛ M (ηₛ M i)) → X p
  η-pos-elimₛ M i X η-pos* (inl unit) = η-pos*

  μₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
    → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
    → Cnsₛ M i
  μₛ M (lf τ) κ = lf τ
  μₛ M (nd c δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p) 
    in γ M w δ ψ

  μ-posₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
    → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
    → (p : Posₛ M c) (q : Posₛ M (δ p))
    → Posₛ M (μₛ M c δ)
  μ-posₛ M (nd c δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
    in γ-pos-inl M w δ ψ r
  μ-posₛ M (nd c δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
    in γ-pos-inr M w δ ψ p (μ-posₛ M (ε p) (κ↑ p) q r)

  μ-pos-fstₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
    → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
    → Posₛ M (μₛ M c δ) → Posₛ M c
  μ-pos-fstₛ M (nd c δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Pos M c) (λ p → Posₛ M (ε p))
        inl* p = inl unit
        inr* p q = inr (p , μ-pos-fstₛ M (ε p) (κ↑ p) q)
    in γ-pos-elim M w δ ψ X inl* inr* p

  μ-pos-sndₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
    → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
    → (p : Posₛ M (μₛ M c δ))
    → Posₛ M (δ (μ-pos-fstₛ M c δ p))
  μ-pos-sndₛ M (nd c δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
        X p = Posₛ M (κ (μ-pos-fstₛ M (nd c δ ε) κ p))
        inl* p = p
        inr* p q = μ-pos-sndₛ M (ε p) (κ↑ p) q
    in γ-pos-elim M w δ ψ X inl* inr* p
    
  --
  --  Free monad implementation 
  --

  γ M (lf i) ϕ ψ = ψ (η-pos M i)
  γ M (nd c δ ε) ϕ ψ = 
    let ϕ↑ p q = ϕ (μ-pos M c δ p q)
        ψ↑ p q = ψ (μ-pos M c δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
    in nd c δ↑ ε↑

  γ-pos-inl M (nd c δ ε) ϕ ψ (inl unit) = inl unit
  γ-pos-inl M (nd c δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos M c δ p q)
        ψ↑ p q = ψ (μ-pos M c δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γ-pos-inl M (ε p) (ϕ↑ p) (ψ↑ p) q)

  γ-pos-inr M (lf i) ϕ ψ p q = 
    η-pos-elim M i (λ p → Posₛ M (ψ p) → Posₛ M (ψ (η-pos M i))) (λ p → p) p q
  γ-pos-inr M (nd c δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μ-pos M c δ p q)
        ψ↑ p q = ψ (μ-pos M c δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μ-pos-fst M c δ p
        p₁ = μ-pos-snd M c δ p
    in inr (p₀ , γ-pos-inr M (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q)

  γ-pos-elim M (lf i) ϕ ψ X inl* inr* p = inr* (η-pos M i) p
  γ-pos-elim M (nd c δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γ-pos-elim M (nd c δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos M c δ p q)
        ψ↑ p q = ψ (μ-pos M c δ p q)
        δ↑ p = μ M (δ p) (ϕ↑ p)
        ε↑ p = γ M (ε p) (ϕ↑ p) (ψ↑ p)
        X↑ p q = X (inr (p , q))
        inl*↑ p q = inl* (inr (p , q))
        inr*↑ p q r = inr* (μ-pos M c δ p q) r
    in γ-pos-elim M (ε p) (ϕ↑ p) (ψ↑ p) (X↑ p) (inl*↑ p) (inr*↑ p) q

  --
  --  The slice construction
  --

  postulate

    Slice : 𝕄 → 𝕄

    Idx-Slice : (M : 𝕄) 
      → Idx (Slice M) ↦ Idxₛ M
    {-# REWRITE Idx-Slice #-}
    
    Cns-Slice : (M : 𝕄) 
      → Cns (Slice M) ↦ Cnsₛ M 
    {-# REWRITE Cns-Slice #-}

    Pos-Slice : (M : 𝕄) 
      → {i : Idx (Slice M)}
      → (c : Cns (Slice M) i)
      → Pos (Slice M) c ↦ Posₛ M c
    {-# REWRITE Pos-Slice #-}

    Typ-Slice : (M : 𝕄) 
      → {i : Idx (Slice M)}
      → (c : Cns (Slice M) i) (p : Pos (Slice M) c)
      → Typ (Slice M) c p ↦ Typₛ M c p
    {-# REWRITE Typ-Slice #-}

    η-Slice : (M : 𝕄) 
      → (i : Idx (Slice M))
      → η (Slice M) i ↦ ηₛ M i
    {-# REWRITE η-Slice #-}

    η-pos-Slice : (M : 𝕄) 
      → (i : Idx (Slice M))
      → η-pos (Slice M) i ↦ η-posₛ M i
    {-# REWRITE η-pos-Slice #-}

    η-pos-elim-Slice : (M : 𝕄) 
      → (i : Idx (Slice M))
      → (X : (p : Pos (Slice M) (η (Slice M) i)) → Set)
      → (η-pos* : X (η-pos (Slice M) i))
      → (p : Pos (Slice M) (η (Slice M) i))
      → η-pos-elim (Slice M) i X η-pos* p ↦ η-pos-elimₛ M i X η-pos* p 
    {-# REWRITE η-pos-elim-Slice #-}

    μ-Slice : (M : 𝕄) 
      → {i : Idx (Slice M)} (c : Cns (Slice M) i)
      → (δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p))
      → μ (Slice M) c δ ↦ μₛ M c δ
    {-# REWRITE μ-Slice #-}

    μ-pos-Slice : (M : 𝕄) 
      → {i : Idx (Slice M)} (c : Cns (Slice M) i)
      → (δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p))
      → (p : Pos (Slice M) c) (q : Pos (Slice M) (δ p))
      → μ-pos (Slice M) c δ p q ↦ μ-posₛ M c δ p q
    {-# REWRITE μ-pos-Slice #-}

    μ-pos-fst-Slice : (M : 𝕄) 
      → {i : Idx (Slice M)} (c : Cns (Slice M) i)
      → (δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p))
      → (p : Pos (Slice M) (μ (Slice M) c δ))
      → μ-pos-fst (Slice M) c δ p ↦ μ-pos-fstₛ M c δ p
    {-# REWRITE μ-pos-fst-Slice #-}
    
    μ-pos-snd-Slice : (M : 𝕄) 
      → {i : Idx (Slice M)} (c : Cns (Slice M) i)
      → (δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p))
      → (p : Pos (Slice M) (μ (Slice M) c δ))
      → μ-pos-snd (Slice M) c δ p ↦ μ-pos-sndₛ M c δ p
    {-# REWRITE μ-pos-snd-Slice #-}

  -- μ-pos-fst-βₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
  --   → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
  --   → (p : Posₛ M c) (q : Posₛ M (δ p))
  --   → μ-pos-fstₛ M c δ (μ-posₛ M c δ p q) == p
  -- μ-pos-fst-βₛ M c δ p q = {!μ-pos-fstₛ M c δ (μ-posₛ M c δ p q)!}


    -- μ-pos-fst-β : (M : 𝕄) {i : Idx M} (c : Cns M i)
    --   → (δ : (p : Pos M c) → Cns M (Typ M c p))
    --   → (p : Pos M c) (q : Pos M (δ p))
    --   → μ-pos-fst M c δ (μ-pos M c δ p q) ↦ p
    -- {-# REWRITE μ-pos-fst-β #-}
