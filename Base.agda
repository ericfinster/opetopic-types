{-# OPTIONS --without-K --rewriting #-}

module Base where

  open import Agda.Primitive public using (lzero)
    renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

  -- Rewriting
  infix 30 _↦_
  postulate  
    _↦_ : ∀ {i} {A : Set i} → A → A → Set i

  {-# BUILTIN REWRITE _↦_ #-}

  Π : ∀ {i j} (A : Set i) (B : A → Set j) → Set (lmax i j)
  Π A B = (a : A) → B a

  infixr 60 _,_ _×_ _⊔_

  _∘_ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set k}
    (g : {x : A} → Π (B x) (C x)) (f : Π A B) → Π A (λ x → C x (f x))
  g ∘ f = λ x → g (f x)

  record Σ {i j} (A : Set i) (B : A → Set j) : Set (lmax i j) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  _×_ : ∀ {i j} → Set i → Set j → Set (lmax i j)
  A × B = Σ A (λ _ → B)

  record ⊤ : Set where
    instance constructor unit

  Unit = ⊤

  {-# BUILTIN UNIT ⊤ #-}

  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  _+_ : ℕ → ℕ → ℕ
  m + O = m
  m + S n = S (m + n)

  data _⊔_ {i j} (A : Set i) (B : Set j) : Set (lmax i j) where
    inl : A → A ⊔ B
    inr : B → A ⊔ B

  data ⊥ : Set where

  data _==_ {i} {A : Set i} (a : A) : A → Set i where
    idp : a == a

  --
  --  Equivalences
  --

  -- record Eqv {i j} (A : Set i) (B : Set j) : Set (lmax (lsucc i) (lsucc j)) where
  --   field
  --     R : A → B → Set (lmax i j)
  --     left-contr : (a : A) → is-contr (Σ B (λ b → R a b))
  --     right-contr : (b : B) → is-contr (Σ A (λ a → R a b))

  -- open Eqv public

  -- To : ∀ {i j} {A : Set i} {B : Set j} → Eqv A B → A → B
  -- To E a = fst (fst (left-contr E a))

  -- From : ∀ {i j} {A : Set i} {B : Set j} → Eqv A B → B → A
  -- From E b = fst (fst (right-contr E b))

  -- IdEqv : ∀ {i} → (A : Set i) → Eqv A A
  -- R (IdEqv A) a₀ a₁ = a₀ == a₁
  -- left-contr (IdEqv A) a = (a , idp) , λ { (a , idp) → idp }
  -- right-contr (IdEqv A) a = (a , idp) , λ { (a , idp) → idp }


