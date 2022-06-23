
module Native.InductiveOpetopicTypes where

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

  infix 10 _↦_
  postulate  
    _↦_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ

  {-# BUILTIN REWRITE _↦_ #-}

  -- Σ-types
  infix 2 Σ-syntax

  Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  record ● {ℓ} : Type ℓ where
    constructor ∙

  --
  --  Opetopic Types 
  --
  
  data 𝕆Type (ℓ : Level) : Type (ℓ-suc ℓ) 

  Frm : ∀ {ℓ} → 𝕆Type ℓ → Type ℓ

  postulate

    Src : ∀ {ℓ} {X : 𝕆Type ℓ} (P : Frm X → Type ℓ)
      → Frm X → Type ℓ 

    Pos : ∀ {ℓ} {X : 𝕆Type ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ

    Typ : ∀ {ℓ} {X : 𝕆Type ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s) → Frm X 

    _⊚_ : ∀ {ℓ} {X : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s)
      → P (Typ P s p)  
  
  data 𝕆Type ℓ where
    ■ : 𝕆Type ℓ
    _▸_ : (X : 𝕆Type ℓ) (P : Frm X → Type ℓ) → 𝕆Type ℓ 

  Frm ■ = ●
  Frm (X ▸ P) =
    Σ[ frm ∈ Frm X ]
    Σ[ src ∈ Src P frm ]
    P frm

  infixl 50 _⊙_

  postulate

    _⇒_ : ∀ {ℓ} → 𝕆Type ℓ → 𝕆Type ℓ → Type ℓ
    
    id-map : ∀ {ℓ} → (X : 𝕆Type ℓ) → X ⇒ X

    Frm⇒ : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → (σ : X ⇒ Y)
      → Frm X → Frm Y

    _⊙_ : ∀ {ℓ} {X Y Z : 𝕆Type ℓ}
      → Y ⇒ Z → X ⇒ Y → X ⇒ Z

  postulate
  
    η : ∀ {ℓ} {X : 𝕆Type ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    η-pos : ∀ {ℓ} {X : 𝕆Type ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Pos P (η P x)

    η-pos-elim : ∀ {ℓ ℓ'} {X : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → (p : Pos P (η P x)) → Q p

    μ : ∀ {ℓ} {X Y : 𝕆Type ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → Src Q (Frm⇒ σ f)

    μ-pos : ∀ {ℓ} {X Y : 𝕆Type ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → Pos Q (μ σ P Q s ϕ) 

    μ-fst : ∀ {ℓ} {X Y : 𝕆Type ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Pos P s  

    μ-snd : ∀ {ℓ} {X Y : 𝕆Type ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Pos Q (ϕ (μ-fst σ P Q s ϕ p))


  --
  --  Equational Structure
  --
  
  postulate

    --
    --  Laws for maps
    -- 
  
    Frm⇒-id : ∀ {ℓ} (X : 𝕆Type ℓ) (f : Frm X)
      → Frm⇒ (id-map X) f ↦ f
    {-# REWRITE Frm⇒-id #-}

    Frm⇒-⊙ : ∀ {ℓ} {X Y Z : 𝕆Type ℓ}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
      → Frm⇒ (τ ⊙ σ) f ↦ Frm⇒ τ (Frm⇒ σ f)
    {-# REWRITE Frm⇒-⊙ #-}

    map-unit-l : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → (σ : X ⇒ Y)
      → id-map Y ⊙ σ ↦ σ
    {-# REWRITE map-unit-l #-}

    map-unit-r : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → (σ : X ⇒ Y)
      → σ ⊙ id-map X ↦ σ
    {-# REWRITE map-unit-r #-}

    map-assoc : ∀ {ℓ} {X Y Z W : 𝕆Type ℓ}
      → (ρ : X ⇒ Y) (σ : Y ⇒ Z) (τ : Z ⇒ W)
      → τ ⊙ (σ ⊙ ρ) ↦ τ ⊙ σ ⊙ ρ
    {-# REWRITE map-assoc #-} 

    --
    --  Laws for positions types and inhabitants
    --
    
    -- Typing and Inhabitants of μ and η
    Typ-η : ∀ {ℓ} {X : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → Typ P (η P x) p ↦ f
    {-# REWRITE Typ-η #-}

    Typ-μ : ∀ {ℓ} {X Y : 𝕆Type ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Typ Q (μ σ P Q s ϕ) p ↦ Typ Q (ϕ (μ-fst σ P Q s ϕ p)) (μ-snd σ P Q s ϕ p)
    {-# REWRITE Typ-μ #-}

    -- BUG! Why do we need this ?!?
    Typ-μ-idmap : ∀ {ℓ} {X : 𝕆Type ℓ} 
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
      → (p : Pos Q (μ (id-map X) P Q s ϕ))
      → Typ Q (μ (id-map X) P Q s ϕ) p ↦ Typ Q (ϕ (μ-fst (id-map X) P Q s ϕ p)) (μ-snd (id-map X) P Q s ϕ p)
    {-# REWRITE Typ-μ-idmap #-}

    ⊚-η : ∀ {ℓ} {X : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → η P x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    ⊚-μ : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → μ σ P Q s ϕ ⊚ p ↦ ϕ (μ-fst σ P Q s ϕ p) ⊚ μ-snd σ P Q s ϕ p
    {-# REWRITE ⊚-μ #-}

    -- BUG!  Same as above.
    ⊚-μ-idmap : ∀ {ℓ} {X : 𝕆Type ℓ}
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
      → (p : Pos Q (μ (id-map X) P Q s ϕ))
      → μ (id-map X) P Q s ϕ ⊚ p ↦ (ϕ (μ-fst (id-map X) P Q s ϕ p) ⊚ μ-snd (id-map X) P Q s ϕ p) 
    {-# REWRITE ⊚-μ-idmap #-}

    --
    -- Laws for positions
    --
    
    η-pos-elim-β : ∀ {ℓ ℓ'} {X : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → η-pos-elim x Q q (η-pos P x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

    μ-fst-β : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-fst σ P Q s ϕ (μ-pos σ P Q s ϕ p q) ↦ p 
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-snd σ P Q s ϕ (μ-pos σ P Q s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : ∀ {ℓ} {X Y : 𝕆Type ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → μ-pos σ P Q s ϕ (μ-fst σ P Q s ϕ p) (μ-snd σ P Q s ϕ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    -- Extra law needed due to lack of η-expansiofor positions
    map-η : ∀ {ℓ} {X Y : 𝕆Type ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s (λ p → η Q (ϕ p))))
      → μ-pos σ P Q s (λ p → η Q (ϕ p)) (μ-fst σ P Q s (λ p → η Q (ϕ p)) p)
         (η-pos Q (ϕ (μ-fst σ P Q s (λ p → η Q (ϕ p)) p))) ↦ p
    {-# REWRITE map-η #-}

    -- BUG! id-map versioof above
    map-η-idmap : ∀ {ℓ} {X : 𝕆Type ℓ} 
      → (P : Frm X → Type ℓ)
      → (Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (μ (id-map X) P Q s (λ p → η Q (ϕ p))))
      → μ-pos (id-map X) P Q s (λ p → η Q (ϕ p)) (μ-fst (id-map X) P Q s (λ p → η Q (ϕ p)) p)
         (η-pos Q (ϕ (μ-fst (id-map X) P Q s (λ p → η Q (ϕ p)) p))) ↦ p
    {-# REWRITE map-η-idmap #-}

    --
    -- Monad Laws
    --
    
    unit-left : ∀ {ℓ} (X Y : 𝕆Type ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y)
      → (f : Frm X) (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Src Q (Frm⇒ σ f))
      → μ σ P Q (η P x) ϕ ↦ ϕ (η-pos P x)
    {-# REWRITE unit-left #-}

    unit-right : ∀ {ℓ} (X : 𝕆Type ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ (id-map X) P P s (λ p → η P (s ⊚ p)) ↦ s
    {-# REWRITE unit-right #-}

    μ-assoc : ∀ {ℓ} (X Y Z : 𝕆Type ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) 
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (ψ : (pq : Pos Q (μ σ P Q s ϕ)) → Src R (Frm⇒ τ (Typ Q (μ σ P Q s ϕ) pq)))
      → μ τ Q R (μ σ P Q s ϕ) ψ ↦ μ (τ ⊙ σ) P R s (λ p → μ τ Q R (ϕ p) (λ q → ψ (μ-pos σ P Q s ϕ p q)))
    {-# REWRITE μ-assoc #-}

    -- BUG!  Specialized for id-map ...
    μ-assoc-idmap-l : ∀ {ℓ} (X Z : 𝕆Type ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm X → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (τ : X ⇒ Z) 
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
      → (ψ : (pq : Pos Q (μ (id-map X) P Q s ϕ)) → Src R (Frm⇒ τ (Typ Q (μ (id-map X) P Q s ϕ) pq)))
      → μ τ Q R (μ (id-map X) P Q s ϕ) ψ ↦ μ τ P R s (λ p → μ τ Q R (ϕ p) (λ q → ψ (μ-pos (id-map X) P Q s ϕ p q)))
    {-# REWRITE μ-assoc-idmap-l #-}

  module _ {ℓ} {X : 𝕆Type ℓ} {P : Frm X → Type ℓ}
           (U : Frm (X ▸ P) → Type ℓ) where

    data Tr : Frm (X ▸ P) → Type ℓ

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
         → (flr : U (f , μ (id-map X) Branch P brs (λ p → η P (stm (brs ⊚ p))) , tgt)) 
         → Tr (f , μ (id-map X) Branch P  brs (λ p → lvs (brs ⊚ p)) , tgt)




