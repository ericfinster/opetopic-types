{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Universe where

  postulate

    Σₛ : (A : Set) (B : A → Set) → Set

    prₛ : (A : Set) (B : A → Set)
      → (a : A) (b : B a)
      → Σₛ A B

    fstₛ : (A : Set) (B : A → Set)
      → (s : Σₛ A B)
      → A

    sndₛ : (A : Set) (B : A → Set)
      → (s : Σₛ A B)
      → B (fstₛ A B s)

    --
    --  Computation rules
    --
    
    Σₛ-β : (A : Set) (B : A → Set) 
      → (s : Σₛ A B)
      → prₛ A B (fstₛ A B s) (sndₛ A B s) ↦ s
    {-# REWRITE Σₛ-β #-}

    fstₛ-β : (A : Set) (B : A → Set)
      → (a : A) (b : B a)
      → fstₛ A B (prₛ A B a b) ↦ a
    {-# REWRITE fstₛ-β #-}

    sndₛ-β : (A : Set) (B : A → Set)
      → (a : A) (b : B a)
      → sndₛ A B (prₛ A B a b) ↦ b
    {-# REWRITE sndₛ-β #-}
  
    --
    --  Strict Unitality and Associativity
    --
    
    Σₛ-unit-right : (A : Set)
      → Σₛ A (cst ⊤) ↦ A
    {-# REWRITE Σₛ-unit-right #-}

    Σₛ-unit-left : (B : ⊤ → Set)
      → Σₛ ⊤ B ↦ B tt
    {-# REWRITE Σₛ-unit-left #-}

    Σₛ-assoc : (A : Set) (B : A → Set) (C : Σₛ A B → Set)
      → Σₛ (Σₛ A B) C ↦ Σₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) 
    {-# REWRITE Σₛ-assoc #-}

    prₛ-unit-right : (A : Set) (a : A)
      → prₛ A (cst ⊤) a tt ↦ a 
    {-# REWRITE prₛ-unit-right #-}

    prₛ-unit-left : (B : ⊤ → Set) (u : ⊤) (b : B u)
      → prₛ ⊤ B u b ↦ b
    {-# REWRITE prₛ-unit-left #-}

    prₛ-assoc : (A : Set) (B : A → Set) (C : Σₛ A B → Set)
      → (s : Σₛ A B) (t : C s)
      → prₛ (Σₛ A B) C s t ↦ prₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) (fstₛ A B s)
                                 (prₛ (B (fstₛ A B s)) (λ b → C (prₛ A B (fstₛ A B s) b)) (sndₛ A B s) t)
    {-# REWRITE prₛ-assoc #-}

    fstₛ-unit-right : (A : Set) (a : A)
      → fstₛ A (cst ⊤) a ↦ a
    {-# REWRITE fstₛ-unit-right #-}

    fstₛ-unit-left : (B : ⊤ → Set) (u : ⊤) (b : B u)
      → fstₛ ⊤ B b ↦ tt
    {-# REWRITE fstₛ-unit-left #-}

    fstₛ-assoc : (A : Set) (B : A → Set) (C : Σₛ A B → Set)
      → (s : Σₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A (λ z → B z) a b))))
      → fstₛ (Σₛ A B) C s ↦ prₛ A B (fstₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s)
                                    (fstₛ (B (fstₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s))
                                    (λ b → C (prₛ A B (fstₛ A (λ a → Σₛ (B a) (λ b₁ → C (prₛ A B a b₁))) s) b))
                                      (sndₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s))
    {-# REWRITE fstₛ-assoc #-}

    sndₛ-unit-right : (A : Set) (a : A)
      → sndₛ A (cst ⊤) a ↦ tt
    {-# REWRITE sndₛ-unit-right #-}

    sndₛ-unit-left : (B : ⊤ → Set) (u : ⊤) (b : B u)
      → sndₛ ⊤ B b ↦ b
    {-# REWRITE sndₛ-unit-left #-}

    sndₛ-assoc : (A : Set) (B : A → Set) (C : Σₛ A B → Set)
      → (s : Σₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A (λ z → B z) a b))))
      → sndₛ (Σₛ A B) C s ↦ sndₛ (B (fstₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s))
                              (λ b → C (prₛ A B (fstₛ A (λ a → Σₛ (B a) (λ b₁ → C (prₛ A B a b₁))) s) b))
                                       (sndₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s)
    {-# REWRITE sndₛ-assoc #-}


  --
  --  Currying of strict sigma
  --
  
  curryₛ : {A : Set} {B : A → Set}
    → (C : Σₛ A B → Set)
    → (a : A) → B a → Set
  curryₛ {A} {B} C a b = C (prₛ A B a b) 

  uncurryₛ : {A : Set} {B : A → Set}
    → (C : (a : A) → B a → Set)
    → Σₛ A B → Set
  uncurryₛ {A} {B} C s = C (fstₛ A B s) (sndₛ A B s) 
