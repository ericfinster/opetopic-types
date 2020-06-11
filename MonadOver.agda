{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module MonadOver where

  postulate

    𝕄↓ : (M : 𝕄) → Set

    Idx↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Idx M → Set 
    Cns↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → Cns M f → Set 

    Typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f} 
      → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
      → (p : Pos M σ) → Idx↓ M↓ (Typ M σ p)

    η↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → Cns↓ M↓ f↓ (η M f)

    μ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f}
      → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
      → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → Cns↓ M↓ f↓ (μ M σ δ)

    -- typ↓ laws 
    η-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → (p : Pos M (η M f))
      → Typ↓ M↓ (η↓ M↓ f↓) p ↦ f↓
    {-# REWRITE η-pos-typ↓ #-}

    μ-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f}
      → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
      → (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → (p : Pos M (μ M σ δ))
      → Typ↓ M↓ (μ↓ M↓ σ↓ δ↓) p ↦ Typ↓ M↓ (δ↓ (μ-pos-fst M σ δ p)) (μ-pos-snd M σ δ p) 
    {-# REWRITE μ-pos-typ↓ #-}
    
    -- μ↓ laws
    μ-unit-right↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f}
      → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
      → μ↓ M↓ σ↓ (λ p → η↓ M↓ (Typ↓ M↓ σ↓ p)) ↦ σ↓
    {-# REWRITE μ-unit-right↓ #-}

    μ-unit-left↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {f↓ : Idx↓ M↓ f}
      → {δ : (p : Pos M (η M f)) → Cns M f}
      → (δ↓ : (p : Pos M (η M f)) → Cns↓ M↓ f↓ (δ p))
      → μ↓ M↓ (η↓ M↓ f↓) δ↓ ↦ δ↓ (η-pos M f) 
    {-# REWRITE μ-unit-left↓ #-}
    
    μ-assoc↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f}
      → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
      → {ε : (p : Pos M (μ M σ δ)) → Cns M (Typ M (μ M σ δ) p)}
      → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos M (μ M σ δ)) → Cns↓ M↓ (Typ↓ M↓ (μ↓ M↓ σ↓ δ↓) p) (ε p))
      → μ↓ M↓ (μ↓ M↓ σ↓ δ↓) ε↓ ↦ μ↓ M↓ σ↓ (λ p → μ↓ M↓ (δ↓ p) (λ q → ε↓ (μ-pos M σ δ p q)))
    {-# REWRITE μ-assoc↓ #-} 

    --
    --  Extension of colors
    --
    
    Ext : (M : 𝕄) (F↓ : Idx M → Set) → 𝕄↓ M

    Idx↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → Idx↓ (Ext M F↓) ↦ F↓
    {-# REWRITE Idx↓-Ext #-}

    Cns↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → {f : Idx M} (σ : Cns M f) 
      → (f↓ : F↓ f)
      → Cns↓ (Ext M F↓) f↓ σ ↦ ((p : Pos M σ) → F↓ (Typ M σ p) )
    {-# REWRITE Cns↓-Ext #-}
    
    Typ↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → {f : Idx M} (σ : Cns M f) 
      → (f↓ : F↓ f) (σ↓ : Cns↓ (Ext M F↓) f↓ σ)
      → (p : Pos M σ)
      → Typ↓ (Ext M F↓) {σ = σ} {f↓ = f↓} σ↓ p ↦ σ↓ p 
    {-# REWRITE Typ↓-Ext #-}

    η↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
      → {f : Idx M} (f↓ : Idx↓ (Ext M F↓) f)
      → η↓ (Ext M F↓) f↓ ↦ (λ _ → f↓)
    {-# REWRITE η↓-Ext #-}
    
    μ↓-Ext : {M : 𝕄} (F↓ : Idx M → Set)
      → {f : Idx M} {σ : Cns M f}
      → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
      → {f↓ : Idx↓ (Ext M F↓) f} (σ↓ : Cns↓ (Ext M F↓) f↓ σ)
      → (δ↓ : (p : Pos M σ) → Cns↓ (Ext M F↓) (Typ↓ (Ext M F↓) {f↓ = f↓} σ↓ p) (δ p))
      → μ↓ (Ext M F↓) {f↓ = f↓} σ↓ δ↓ ↦ (λ p → δ↓ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p))
    {-# REWRITE μ↓-Ext #-}
  
  --
  -- Slice↓
  --

  Idx↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → Idx (Slice M) → Set
  Idx↓ₛ M↓ (f , σ) = Σ (Idx↓ M↓ f) (λ f↓ → Cns↓ M↓ f↓ σ)

  data Pd↓ {M : 𝕄} (M↓ : 𝕄↓ M) : {f : Idxₛ M} → Idx↓ₛ M↓ f → Cnsₛ M f → Set where

    lf↓ : {f : Idx M} (f↓ : Idx↓ M↓ f)
      → Pd↓ M↓ (f↓ , η↓ M↓ f↓) (lf f) 
    
    nd↓ : {f : Idx M} {σ : Cns M f}
      → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
      → {ε : (p : Pos M σ) → Pd M (Typ M σ p , δ p)}
      → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos M σ) → Pd↓ M↓ (Typ↓ M↓ σ↓ p , δ↓ p) (ε p))
      → Pd↓ M↓ (f↓ , μ↓ M↓ σ↓ δ↓) (nd σ δ ε) 

  Cns↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idx (Slice M)} (f↓ : Idx↓ₛ M↓ f)
    → Cns (Slice M) f → Set 
  Cns↓ₛ M↓ (f↓ , σ↓) σ = Pd↓ M↓ (f↓ , σ↓) σ 
  
  Typ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idx (Slice M)} {σ : Cns (Slice M) f} 
    → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
    → (p : Pos (Slice M) σ) → Idx↓ₛ M↓ (Typ (Slice M) σ p)
  Typ↓ₛ M↓ (nd↓ {f↓ = f↓} σ↓ δ↓ ε↓) (inl unit) = f↓ , σ↓
  Typ↓ₛ M↓ (nd↓ σ↓ δ↓ ε↓) (inr (p , q)) = Typ↓ₛ M↓ (ε↓ p) q

  γ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idx M} {σ : Cns M f} {ρ : Cnsₛ M (f , σ)}
    → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
    → {ε : (p : Pos M σ) → Cnsₛ M (Typ M σ p , δ p)}
    → {f↓ : Idx↓ M↓ f} {σ↓ : Cns↓ M↓ f↓ σ}
    → (ρ↓ : Cns↓ₛ M↓ (f↓ , σ↓) ρ)
    → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
    → (ε↓ : (p : Pos M σ) → Cns↓ₛ M↓ (Typ↓ M↓ σ↓ p , δ↓ p) (ε p))
    → Cns↓ₛ M↓ (f↓ , μ↓ M↓ σ↓ δ↓) (γ M ρ δ ε) 
  
  η↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idx (Slice M)} (f↓ : Idx↓ₛ M↓ f)
    → Cns↓ₛ M↓ f↓ (η (Slice M) f)
  η↓ₛ M↓ (f↓ , σ↓) =
    let η-dec↓ p = η↓ M↓ (Typ↓ M↓ σ↓ p)
        lf-dec↓ p = lf↓ (Typ↓ M↓ σ↓ p)
    in nd↓ σ↓ η-dec↓ lf-dec↓

  μ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idx (Slice M)} {σ : Cns (Slice M) f}
    → {δ : (p : Pos (Slice M) σ) → Cns (Slice M) (Typ (Slice M) σ p)}
    → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
    → (δ↓ : (p : Pos (Slice M) σ) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {f↓ = f↓} σ↓ p) (δ p))
    → Cns↓ₛ M↓ f↓ (μ (Slice M) σ δ)
  μ↓ₛ M↓ (lf↓ f↓) κ↓ = lf↓ f↓
  μ↓ₛ M↓ (nd↓ σ↓ δ↓ ε↓) κ↓ = 
    let w↓ = κ↓ (inl unit)
        κ↓↑ p q = κ↓ (inr (p , q))
        ψ↓ p = μ↓ₛ M↓ (ε↓ p) (κ↓↑ p) 
    in γ↓ M↓ w↓ δ↓ ψ↓
  
  γ↓ {M = M} M↓ (lf↓ {f = f} f↓) ϕ↓ ψ↓ = ψ↓ (η-pos M f)
  γ↓ {M = M} M↓ (nd↓ {σ = σ} {δ = δ} σ↓ δ↓ ε↓) ϕ↓ ψ↓ =
    let ϕ↓↑ p q = ϕ↓ (μ-pos M σ δ p q)
        ψ↓↑ p q = ψ↓ (μ-pos M σ δ p q)
        δ↓↑ p = μ↓ M↓ (δ↓ p) (ϕ↓↑ p)
        ε↓↑ p = γ↓ M↓ (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
    in nd↓ σ↓ δ↓↑ ε↓↑

  postulate

    Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → 𝕄↓ (Slice M)

    Idx↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → Idx↓ (Slice↓ M↓) ↦ Idx↓ₛ M↓
    {-# REWRITE Idx↓-Slice↓ #-}
    
    Cns↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx (Slice M)} (f↓ : Idx↓ (Slice↓ M↓) f)
      → Cns↓ (Slice↓ M↓) f↓ ↦ Cns↓ₛ M↓ f↓
    {-# REWRITE Cns↓-Slice↓ #-}

    Typ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx (Slice M)} {σ : Cns (Slice M) f} 
      → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
      → (p : Pos (Slice M) σ)
      → Typ↓ (Slice↓ M↓) σ↓ p ↦ Typ↓ₛ M↓ σ↓ p
    {-# REWRITE Typ↓-Slice↓ #-}

    η↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx (Slice M)} (f↓ : Idx↓ₛ M↓ f)
      → η↓ (Slice↓ M↓) f↓ ↦ η↓ₛ M↓ f↓
    {-# REWRITE η↓-Slice↓ #-}

    μ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx (Slice M)} {σ : Cns (Slice M) f}
      → {δ : (p : Pos (Slice M) σ) → Cns (Slice M) (Typ (Slice M) σ p)}
      → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
      → (δ↓ : (p : Pos (Slice M) σ) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {f↓ = f↓} σ↓ p) (δ p))
      → μ↓ (Slice↓ M↓) σ↓ δ↓ ↦ μ↓ₛ M↓ σ↓ δ↓
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
      → (p : Pos (Pb M X) {f = i} c) → Idx↓ₚ (Typ (Pb M X) {f = i} c p)
    Typ↓ₚ (d , κ) p = Typ↓ M↓ d p , κ p 

    η↓ₚ : {i : Idx (Pb M X)} 
      → (j : Idx↓ₚ i) → Cns↓ₚ j (η (Pb M X) i)
    η↓ₚ (j , y) = η↓ M↓ j , λ _ → y

    μ↓ₚ : {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {δ : (p : Pos (Pb M X) {f = i} c) → Cns (Pb M X) (Typ (Pb M X) {f = i} c p)}
      → {j : Idx↓ₚ i} (d : Cns↓ₚ j c)
      → (δ↓ : (p : Pos (Pb M X) {f = i} c) → Cns↓ₚ (Typ↓ₚ {j = j} d p) (δ p))
      → Cns↓ₚ j (μ (Pb M X) {f = i} c δ)
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
      → (p : Pos (Pb M X) {f = i} c) → Idx↓ₚ M↓ X Y (Typ (Pb M X) {f = i} c p)
      → Typ↓ (Pb↓ M↓ X Y) {f↓ = j} d p ↦ Typ↓ₚ M↓ X Y {j = j} d p 
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
      → {δ : (p : Pos (Pb M X) {f = i} c) → Cns (Pb M X) (Typ (Pb M X) {f = i} c p)}
      → {j : Idx↓ₚ M↓ X Y i} (d : Cns↓ₚ M↓ X Y j c)
      → (δ↓ : (p : Pos (Pb M X) {f = i} c) → Cns↓ₚ M↓ X Y (Typ↓ₚ M↓ X Y {j = j} d p) (δ p))
      → μ↓ (Pb↓ M↓ X Y) {f↓ = j} d δ↓  ↦ μ↓ₚ M↓ X Y {j = j} d δ↓ 
    {-# REWRITE μ↓-Pb↓ #-}
