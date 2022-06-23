{-# OPTIONS --opetopic-types #-}

module Native.Opetopes where

  open import Agda.Primitive public
    using    ( Level )
    renaming ( lzero to ℓ-zero
             ; lsuc  to ℓ-suc
             ; _⊔_   to ℓ-max
             ; Set   to Type
             ; Setω  to Typeω )

  open import Agda.Builtin.Nat public
    using (zero; suc)
    renaming (Nat to ℕ)

  open import Agda.Builtin.Sigma public

  -- Σ-types
  infix 2 Σ-syntax

  Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  --
  --  Universe Polymorphic Unit Type
  -- 
  
  record ● {ℓ} : Type ℓ where
    constructor ∙

  {-# BUILTIN POLYUNIT ● #-}
  
  --
  --  Opetopic Types 
  --

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  postulate
    
    Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → Frm X → Type ℓ

  𝕆Type zero ℓ = ●
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    (Frm X → Type ℓ)

  Frm {zero} X = ●
  Frm {suc n} (X , P) =
    Σ[ f ∈ Frm X ]
    Σ[ src ∈ Src P f ]
    P f

  {-# BUILTIN OPETOPICTYPE 𝕆Type #-}
  {-# BUILTIN FRM Frm #-}

  postulate

    Pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ

    Typ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s) → Frm X 

    Inhab : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s)
      → P (Typ P s p)  

  {-# BUILTIN SRC Src #-}
  {-# BUILTIN POS Pos #-}
  {-# BUILTIN TYP Typ #-}
  {-# BUILTIN INHAB Inhab #-}

  --
  --  Maps of Opetopic Types
  --

  _⇒_ : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ → Type ℓ
  id-map : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ X
  
  postulate

    Frm⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (σ : X ⇒ Y)
      → Frm X → Frm Y

  {-# BUILTIN OPETOPICMAP _⇒_ #-}
  {-# BUILTIN FRMMAP Frm⇒ #-}
  {-# BUILTIN IDMAP id-map #-}

  _⇒_ {zero} X Y = ●
  _⇒_ {suc n} (X , P) (Y , Q) =
    Σ[ σ ∈ X ⇒ Y ]
    ({f : Frm X} → P f → Q (Frm⇒ σ f))

  id-map {zero} X = ∙
  id-map {suc n} (X , P) = id-map X , λ p → p

  postulate
  
    _⊙_ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → Y ⇒ Z → X ⇒ Y → X ⇒ Z

  {-# BUILTIN MAPCOMP _⊙_ #-}

  --
  --  Monadic Signature
  --

  postulate
  
    η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Pos P (η P x)

    μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → Src Q (Frm⇒ σ f)

    μ-pos : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → Pos Q (μ σ P Q s ϕ) 

    μ-fst : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Pos P s  

    μ-snd : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Pos Q (ϕ (μ-fst σ P Q s ϕ p))
 
  {-# BUILTIN UNT η #-} 
  {-# BUILTIN UNTPOS η-pos #-} 

  {-# BUILTIN SUBST μ #-}
  {-# BUILTIN SUBSTPOS μ-pos #-}
  {-# BUILTIN SUBSTFST μ-fst #-}
  {-# BUILTIN SUBSTSND μ-snd #-}

  --
  --  Trees and Their Positions
  --

  module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
           (U : Frm (X , P) → Type ℓ) where

    data Tr : Frm (X , P) → Type ℓ

    {-# NO_POSITIVITY_CHECK #-}
    record Branch (f : Frm X) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        stm : P f
        lvs : Src P f
        br : Tr (f , lvs , stm)

    open Branch public
    
    data Tr where

      lf : {f : Frm X} (tgt : P f)
         → Tr (f , η P tgt , tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , μ (id-map X) Branch P brs (λ p → η P (stm (Inhab Branch brs p))) , tgt)) 
         → Tr (f , μ (id-map X) Branch P  brs (λ p → lvs (Inhab Branch brs p)) , tgt)

  --
  --  Testing
  --

  data _≡_ {i} {A : Type i} (a : A) : A → Type i where
    refl : a ≡ a

  {-# BUILTIN EQUALITY _≡_ #-}

  Frm⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
    → Frm⇒ (id-map X) f ≡ f
  Frm⇒-id X f = refl 

  Frm⇒-⊙ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
    → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
    → Frm⇒ (τ ⊙ σ) f ≡ Frm⇒ τ (Frm⇒ σ f)
  Frm⇒-⊙ σ τ f = refl 

