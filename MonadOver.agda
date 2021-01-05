{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module MonadOver where

  postulate

    𝕄↓ : (M : 𝕄) → Set

    Idx↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Idx M → Set 
    Cns↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} (i↓ : Idx↓ M↓ i)
      → Cns M i → Set 

    Typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} {c : Cns M i} 
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (p : Pos M c) → Idx↓ M↓ (Typ M c p)

    η↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} (i↓ : Idx↓ M↓ i)
      → Cns↓ M↓ i↓ (η M i)

    μ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → Cns↓ M↓ i↓ (μ M c δ)

    -- typ↓ laws 
    η-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} (i↓ : Idx↓ M↓ i)
      → (p : Pos M (η M i))
      → Typ↓ M↓ (η↓ M↓ i↓) p ↦ i↓
    {-# REWRITE η-pos-typ↓ #-}

    μ-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → (i↓ : Idx↓ M↓ i) (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → (p : Pos M (μ M c δ))
      → Typ↓ M↓ (μ↓ M↓ c↓ δ↓) p ↦ Typ↓ M↓ (δ↓ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p) 
    {-# REWRITE μ-pos-typ↓ #-}
    
    -- μ↓ laws
    μ-unit-right↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} {c : Cns M i}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → μ↓ M↓ c↓ (λ p → η↓ M↓ (Typ↓ M↓ c↓ p)) ↦ c↓
    {-# REWRITE μ-unit-right↓ #-}

    μ-unit-left↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} {i↓ : Idx↓ M↓ i}
      → {δ : (p : Pos M (η M i)) → Cns M i}
      → (δ↓ : (p : Pos M (η M i)) → Cns↓ M↓ i↓ (δ p))
      → μ↓ M↓ (η↓ M↓ i↓) δ↓ ↦ δ↓ (η-pos M i) 
    {-# REWRITE μ-unit-left↓ #-}
    
    μ-assoc↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p)}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → (ε↓ : (p : Pos M (μ M c δ)) → Cns↓ M↓ (Typ↓ M↓ (μ↓ M↓ c↓ δ↓) p) (ε p))
      → μ↓ M↓ (μ↓ M↓ c↓ δ↓) ε↓ ↦ μ↓ M↓ c↓ (λ p → μ↓ M↓ (δ↓ p) (λ q → ε↓ (μ-pos M c δ p q)))
    {-# REWRITE μ-assoc↓ #-} 

    --
    --  Extension of colors
    --
    
    Ext : (M : 𝕄) (F↓ : Idx M → Set) → 𝕄↓ M

    Idx↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → Idx↓ (Ext M F↓) ↦ F↓
    {-# REWRITE Idx↓-Ext #-}

    Cns↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → {i : Idx M} (c : Cns M i) 
      → (i↓ : F↓ i)
      → Cns↓ (Ext M F↓) i↓ c ↦ ((p : Pos M c) → F↓ (Typ M c p) )
    {-# REWRITE Cns↓-Ext #-}
    
    Typ↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → {i : Idx M} (c : Cns M i) 
      → (i↓ : F↓ i) (c↓ : Cns↓ (Ext M F↓) i↓ c)
      → (p : Pos M c)
      → Typ↓ (Ext M F↓) {c = c} {i↓ = i↓} c↓ p ↦ c↓ p 
    {-# REWRITE Typ↓-Ext #-}

    η↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → {i : Idx M} (i↓ : Idx↓ (Ext M F↓) i)
      → η↓ (Ext M F↓) i↓ ↦ (λ _ → i↓)
    {-# REWRITE η↓-Ext #-}
    
    μ↓-Ext : {M : 𝕄} (F↓ : Idx M → Set)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {i↓ : Idx↓ (Ext M F↓) i} (c↓ : Cns↓ (Ext M F↓) i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ (Ext M F↓) (Typ↓ (Ext M F↓) {i↓ = i↓} c↓ p) (δ p))
      → μ↓ (Ext M F↓) {i↓ = i↓} c↓ δ↓ ↦ (λ p → δ↓ (μ-pos-fst M c δ p) (μ-pos-snd M c δ p))
    {-# REWRITE μ↓-Ext #-}
  
  --
  -- Slice↓
  --

  Idx↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → Idx (Slice M) → Set
  Idx↓ₛ M↓ (i , c) = Σ (Idx↓ M↓ i) (λ i↓ → Cns↓ M↓ i↓ c)

  data Pd↓ {M : 𝕄} (M↓ : 𝕄↓ M) : {i : Idxₛ M} → Idx↓ₛ M↓ i → Cnsₛ M i → Set where

    lf↓ : {i : Idx M} (i↓ : Idx↓ M↓ i)
      → Pd↓ M↓ (i↓ , η↓ M↓ i↓) (lf i) 
    
    nd↓ : {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {ε : (p : Pos M c) → Pd M (Typ M c p , δ p)}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → (ε↓ : (p : Pos M c) → Pd↓ M↓ (Typ↓ M↓ c↓ p , δ↓ p) (ε p))
      → Pd↓ M↓ (i↓ , μ↓ M↓ c↓ δ↓) (nd c δ ε) 

  Cns↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {i : Idx (Slice M)} (i↓ : Idx↓ₛ M↓ i)
    → Cns (Slice M) i → Set 
  Cns↓ₛ M↓ (i↓ , c↓) c = Pd↓ M↓ (i↓ , c↓) c 
  
  Typ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {i : Idx (Slice M)} {c : Cns (Slice M) i} 
    → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
    → (p : Pos (Slice M) c) → Idx↓ₛ M↓ (Typ (Slice M) c p)
  Typ↓ₛ M↓ (nd↓ {i↓ = i↓} c↓ δ↓ ε↓) (inl unit) = i↓ , c↓
  Typ↓ₛ M↓ (nd↓ c↓ δ↓ ε↓) (inr (p , q)) = Typ↓ₛ M↓ (ε↓ p) q

  γ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {i : Idx M} {c : Cns M i} {ρ : Cnsₛ M (i , c)}
    → {δ : (p : Pos M c) → Cns M (Typ M c p)}
    → {ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p)}
    → {i↓ : Idx↓ M↓ i} {c↓ : Cns↓ M↓ i↓ c}
    → (ρ↓ : Cns↓ₛ M↓ (i↓ , c↓) ρ)
    → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
    → (ε↓ : (p : Pos M c) → Cns↓ₛ M↓ (Typ↓ M↓ c↓ p , δ↓ p) (ε p))
    → Cns↓ₛ M↓ (i↓ , μ↓ M↓ c↓ δ↓) (γ M ρ δ ε) 
  
  η↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {i : Idx (Slice M)} (i↓ : Idx↓ₛ M↓ i)
    → Cns↓ₛ M↓ i↓ (η (Slice M) i)
  η↓ₛ M↓ (i↓ , c↓) =
    let η-dec↓ p = η↓ M↓ (Typ↓ M↓ c↓ p)
        lf-dec↓ p = lf↓ (Typ↓ M↓ c↓ p)
    in nd↓ c↓ η-dec↓ lf-dec↓

  μ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {i : Idx (Slice M)} {c : Cns (Slice M) i}
    → {δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p)}
    → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
    → (δ↓ : (p : Pos (Slice M) c) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {i↓ = i↓} c↓ p) (δ p))
    → Cns↓ₛ M↓ i↓ (μ (Slice M) c δ)
  μ↓ₛ M↓ (lf↓ i↓) κ↓ = lf↓ i↓
  μ↓ₛ M↓ (nd↓ c↓ δ↓ ε↓) κ↓ = 
    let w↓ = κ↓ (inl unit)
        κ↓↑ p q = κ↓ (inr (p , q))
        ψ↓ p = μ↓ₛ M↓ (ε↓ p) (κ↓↑ p) 
    in γ↓ M↓ w↓ δ↓ ψ↓
  
  γ↓ {M = M} M↓ (lf↓ {i = i} i↓) ϕ↓ ψ↓ = ψ↓ (η-pos M i)
  γ↓ {M = M} M↓ (nd↓ {c = c} {δ = δ} c↓ δ↓ ε↓) ϕ↓ ψ↓ =
    let ϕ↓↑ p q = ϕ↓ (μ-pos M c δ p q)
        ψ↓↑ p q = ψ↓ (μ-pos M c δ p q)
        δ↓↑ p = μ↓ M↓ (δ↓ p) (ϕ↓↑ p)
        ε↓↑ p = γ↓ M↓ (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
    in nd↓ c↓ δ↓↑ ε↓↑

  postulate

    Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → 𝕄↓ (Slice M)

    Idx↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → Idx↓ (Slice↓ M↓) ↦ Idx↓ₛ M↓
    {-# REWRITE Idx↓-Slice↓ #-}
    
    Cns↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx (Slice M)} (i↓ : Idx↓ (Slice↓ M↓) i)
      → Cns↓ (Slice↓ M↓) i↓ ↦ Cns↓ₛ M↓ i↓
    {-# REWRITE Cns↓-Slice↓ #-}

    Typ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx (Slice M)} {c : Cns (Slice M) i} 
      → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
      → (p : Pos (Slice M) c)
      → Typ↓ (Slice↓ M↓) c↓ p ↦ Typ↓ₛ M↓ c↓ p
    {-# REWRITE Typ↓-Slice↓ #-}

    η↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx (Slice M)} (i↓ : Idx↓ₛ M↓ i)
      → η↓ (Slice↓ M↓) i↓ ↦ η↓ₛ M↓ i↓
    {-# REWRITE η↓-Slice↓ #-}

    μ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idx (Slice M)} {c : Cns (Slice M) i}
      → {δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p)}
      → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
      → (δ↓ : (p : Pos (Slice M) c) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {i↓ = i↓} c↓ p) (δ p))
      → μ↓ (Slice↓ M↓) c↓ δ↓ ↦ μ↓ₛ M↓ c↓ δ↓
    {-# REWRITE μ↓-Slice↓ #-}

  --
  --  Pb↓ 
  --

  module _ {M : 𝕄} (M↓ : 𝕄↓ M)
    (X : Idx M → Set) 
    (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set) where

    Idx↓ₚ : Idx (Pb M X) → Set
    Idx↓ₚ (i , x) = Σ (Idx↓ M↓ i) (λ j → Y i j x)

    Cns↓ₚ : {i : Idx (Pb M X)} (j : Idx↓ₚ i) (c : Cns (Pb M X) i) → Set
    Cns↓ₚ (j , y) (c , ν) = Σ (Cns↓ M↓ j c) (λ d →
      (p : Pos M c) → Y (Typ M c p) (Typ↓ M↓ d p) (ν p))

    Typ↓ₚ : {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {j : Idx↓ₚ i} (d : Cns↓ₚ j c)
      → (p : Pos (Pb M X) {i = i} c) → Idx↓ₚ (Typ (Pb M X) {i = i} c p)
    Typ↓ₚ (d , κ) p = Typ↓ M↓ d p , κ p 

    η↓ₚ : {i : Idx (Pb M X)} 
      → (j : Idx↓ₚ i) → Cns↓ₚ j (η (Pb M X) i)
    η↓ₚ (j , y) = η↓ M↓ j , λ _ → y

    μ↓ₚ : {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p)}
      → {j : Idx↓ₚ i} (d : Cns↓ₚ j c)
      → (δ↓ : (p : Pos (Pb M X) {i = i} c) → Cns↓ₚ (Typ↓ₚ {j = j} d p) (δ p))
      → Cns↓ₚ j (μ (Pb M X) {i = i} c δ)
    μ↓ₚ {i , x} {c , ν} {δ} {j = j , y} (d , κ) δ↓ =
      let δ' p = fst (δ p)
          ν' p = snd (δ (μ-pos-fst M c δ' p)) (μ-pos-snd M c δ' p)
          δ↓' p = fst (δ↓ p)
          κ' p = snd (δ↓ (μ-pos-fst M c δ' p)) (μ-pos-snd M c δ' p)  
      in μ↓ M↓ {δ = δ'} d δ↓' , κ'

  postulate

    Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → 𝕄↓ (Pb M X) 

    Idx↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → (i : Idx M) (x : X i)
      → Idx↓ (Pb↓ M↓ X Y) (i , x) ↦ Idx↓ₚ M↓ X Y (i , x)
    {-# REWRITE Idx↓-Pb↓ #-}

    Cns↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → (i : Idx (Pb M X)) (j : Idx↓ₚ M↓ X Y i)
      → (c : Cns (Pb M X) i)
      → Cns↓ (Pb↓ M↓ X Y) j c ↦ Cns↓ₚ M↓ X Y j c
    {-# REWRITE Cns↓-Pb↓ #-}

    Typ↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {j : Idx↓ₚ M↓ X Y i} (d : Cns↓ₚ M↓ X Y j c)
      → (p : Pos (Pb M X) {i = i} c) → Idx↓ₚ M↓ X Y (Typ (Pb M X) {i = i} c p)
      → Typ↓ (Pb↓ M↓ X Y) {i↓ = j} d p ↦ Typ↓ₚ M↓ X Y {j = j} d p 
    {-# REWRITE Typ↓-Pb↓ #-}

    η↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → {i : Idx (Pb M X)}
      → (j : Idx↓ₚ M↓ X Y i) 
      → η↓ (Pb↓ M↓ X Y) j ↦ η↓ₚ M↓ X Y j 
    {-# REWRITE η↓-Pb↓ #-}

    μ↓-Pb↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p)}
      → {j : Idx↓ₚ M↓ X Y i} (d : Cns↓ₚ M↓ X Y j c)
      → (δ↓ : (p : Pos (Pb M X) {i = i} c) → Cns↓ₚ M↓ X Y (Typ↓ₚ M↓ X Y {j = j} d p) (δ p))
      → μ↓ (Pb↓ M↓ X Y) {i↓ = j} d δ↓  ↦ μ↓ₚ M↓ X Y {j = j} d δ↓ 
    {-# REWRITE μ↓-Pb↓ #-}

  --
  --  Algebricity of an extension 
  --

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    -- NOTE: I think switching the "typ" entry to be a function would
    -- probably save a bunch of extra annoying funext problems later
    -- on.   Is there a reason you opted for this?
    record alg-comp (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) : Set where
      constructor ⟦_∣_∣_⟧
      field
        idx : Idx↓ M↓ i 
        cns : Cns↓ M↓ idx c
        typ : Typ↓ M↓ cns == ν

    is-algebraic : Set
    is-algebraic = (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (alg-comp i c ν) 
    
    open alg-comp public

    alg-comp-= : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j j' : Idx↓ M↓ i} (m : j == j')
      → {d : Cns↓ M↓ j c} {d' : Cns↓ M↓ j' c}
      → (n : d == d' [ (λ x → Cns↓ M↓ x c) ↓ m ])
      → {r : Typ↓ M↓ d == ν} {r' : Typ↓ M↓ d' == ν}
      → (ϕ : (p : Pos M c) → app= r p == ap (λ x → Typ↓ M↓ (snd x) p) (pair= m n) ∙ app= r' p)
      → ⟦ j ∣ d ∣ r ⟧ == ⟦ j' ∣ d' ∣ r' ⟧
    alg-comp-= i c ν {j = j} idp {d = d} idp {r} {r'} ϕ =
      ap (λ x → ⟦ j ∣ d ∣ x ⟧) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r'))

    alg-comp-Σ-eqv : (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → alg-comp i c ν ≃ Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))
    alg-comp-Σ-eqv i c ν = equiv to from to-from from-to 

      where to : alg-comp i c ν → Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))
            to ⟦ j ∣ d ∣ t ⟧ = j , d , t

            from : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν)) → alg-comp i c ν
            from (j , d , t) = ⟦ j ∣ d ∣ t ⟧ 

            to-from : (β : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))) → to (from β) == β
            to-from (j , d , t) = idp

            from-to : (α : alg-comp i c ν) → from (to α) == α
            from-to ⟦ j ∣ d ∣ t ⟧ = idp
