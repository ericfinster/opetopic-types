module Core.Minimized where

  open import Agda.Primitive public
    using    ( Level )
    renaming ( lzero to ℓ-zero
             ; lsuc  to ℓ-suc
             ; _⊔_   to ℓ-max
             ; Set   to Type
             ; Setω  to Typeω )
  open import Agda.Builtin.Sigma public

  infix 10 _↦_
  
  postulate  
    _↦_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ

  {-# BUILTIN REWRITE _↦_ #-}

  open import Agda.Builtin.Nat public
    using (zero; suc)
    renaming (Nat to ℕ)

  record 𝟙 (ℓ : Level) : Type ℓ where
    instance constructor ● 

  --
  --  Opetopic Types
  --

  postulate
  
    𝕆Type : (n : ℕ) (ℓ : Level)
      → Type (ℓ-suc ℓ)

    Frm : (n : ℕ) (ℓ : Level)
      → 𝕆Type n ℓ → Type ℓ 

  Pd : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → Frm n ℓ X → Type ℓ
  Pd n ℓ X P f = 𝟙 ℓ 

  postulate
  
    Pos : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → Type ℓ 

    Typ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (p : Pos n ℓ X P f ρ) → Frm n ℓ X 

    Ihb : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (p : Pos n ℓ X P f ρ)
      → P (Typ n ℓ X P f ρ p)

    --
    --  Monadic Structure
    --

    ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → Pd n ℓ X Q f

    η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → Pd n ℓ X P f 

    μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → Pd n ℓ X P f 

    --
    --  Problematic rewrites ...
    --

    ν-id : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → ν n ℓ X P P f ρ (Ihb n ℓ X P f ρ) ↦ ρ
    {-# REWRITE ν-id #-}

    μ-unit-r : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → μ n ℓ X P f (ν n ℓ X P (Pd n ℓ X P) f ρ
          (λ p → η n ℓ X P (Typ n ℓ X P f ρ p) (Ihb n ℓ X P f ρ p))) ↦ ρ
    {-# REWRITE μ-unit-r #-}

