{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FiniteUniverse where

  infixl 50 _⊔₀_
  
  data 𝔽 : Set where
    ⊥₀ : 𝔽
    ⊤₀ : 𝔽
    _⊔₀_ : 𝔽 → 𝔽 → 𝔽

  postulate

    El : 𝔽 → Set 

    ⊥₀-elim : (A : Set)
      → El ⊥₀ → A

    tt₀ : El ⊤₀

    ⊤₀-elim : (P : El ⊤₀ → Set)
      → (p : P tt₀)
      → (u : El ⊤₀) → P u

    ⊤₀-comp : (P : El ⊤₀ → Set)
      → (p : P tt₀)
      → ⊤₀-elim P p tt₀ ↦ p
    {-# REWRITE ⊤₀-comp #-}

    inl₀ : (A B : 𝔽) → El A → El (A ⊔₀ B)
    inr₀ : (A B : 𝔽) → El B → El (A ⊔₀ B)

    ⊔₀-elim : (A B : 𝔽) (P : El (A ⊔₀ B) → Set)
      → (inl* : (a : El A) → P (inl₀ A B a))
      → (inr* : (b : El B) → P (inr₀ A B b))
      → (ab : El (A ⊔₀ B)) → P ab

    ⊔₀-inl-β : (A B : 𝔽) (P : El (A ⊔₀ B) → Set)
      → (inl* : (a : El A) → P (inl₀ A B a))
      → (inr* : (b : El B) → P (inr₀ A B b))
      → (a : El A)
      → ⊔₀-elim A B P inl* inr* (inl₀ A B a) ↦ inl* a 
    {-# REWRITE ⊔₀-inl-β #-}

    ⊔₀-inr-β : (A B : 𝔽) (P : El (A ⊔₀ B) → Set)
      → (inl* : (a : El A) → P (inl₀ A B a))
      → (inr* : (b : El B) → P (inr₀ A B b))
      → (b : El B)
      → ⊔₀-elim A B P inl* inr* (inr₀ A B b) ↦ inr* b
    {-# REWRITE ⊔₀-inr-β #-}

    --
    --  Strict Associativity
    --
    
    ⊔-unit-l : (A : 𝔽)
      → ⊥₀ ⊔₀ A ↦ A 
    {-# REWRITE ⊔-unit-l #-}

    ⊔-unit-r : (A : 𝔽)
      → A ⊔₀ ⊥₀ ↦ A
    {-# REWRITE ⊔-unit-r #-}
    
    ⊔-assoc : (A B C : 𝔽)
      → A ⊔₀ (B ⊔₀ C) ↦ (A ⊔₀ B) ⊔₀ C 
    {-# REWRITE ⊔-assoc #-}

  π : (F : 𝔽) (X : El F → Set) → Set
  π ⊥₀ X = ⊤
  π ⊤₀ X = X tt₀
  π (F ⊔₀ G) X = π F (λ f → X (inl₀ F G f)) × π G (λ g → X (inr₀ F G g))

  ev : {F : 𝔽} {X : El F → Set}
    → π F X → (f : El F) → X f
  ev {⊥₀} {X} α f = ⊥₀-elim (X f) f
  ev {⊤₀} {X} α f = ⊤₀-elim X α f
  ev {A ⊔₀ B} {X} (α , β) f = ⊔₀-elim A B X (ev α) (ev β) f

  infixr 50 _⇒_
  
  _⇒_ : 𝔽 → Set → Set
  A ⇒ X = π A (cst X)

  cst₀ : {A : 𝔽} {X : Set} → X → A ⇒ X
  cst₀ {⊥₀} {X} _ = tt
  cst₀ {⊤₀} {X} x = x
  cst₀ {A₀ ⊔₀ A₁} {X} x =
    cst₀ {A₀} {X} x , cst₀ {A₁} {X} x

  σ : (A : 𝔽) (B : A ⇒ 𝔽) → 𝔽
  σ ⊥₀ _ = ⊥₀
  σ ⊤₀ B = B
  σ (A₀ ⊔₀ A₁) (B₀ , B₁) = σ A₀ B₀ ⊔₀ σ A₁ B₁

  -- curry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set} → σ A B ⇒ X
  --   → (a : El A) → ev B a ⇒ X
  -- curry₀ {⊥₀} {B} {X} α a = ⊥₀-elim (⊥₀-elim 𝔽 a ⇒ X) a
  -- curry₀ {⊤₀} {B} {X} α a = ⊤₀-elim (λ u → ⊤₀-elim (cst 𝔽) B u ⇒ X) α a
  -- curry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} (α , β) ab =
  --   ⊔₀-elim A₀ A₁ (λ u → ⊔₀-elim A₀ A₁ (cst 𝔽) (ev B₀) (ev B₁) u ⇒ X)
  --   (λ a → curry₀ α a) (λ b → curry₀ β b) ab
  
  -- uncurry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set} 
  --   → (ϕ : (a : El A) → ev B a ⇒ X)
  --   → σ A B ⇒ X
  -- uncurry₀ {⊥₀} {B} {X} ϕ = tt
  -- uncurry₀ {⊤₀} {B} {X} ϕ = ϕ tt₀
  -- uncurry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} ϕ =
  --   uncurry₀ (ϕ ∘ inl₀ A₀ A₁) , uncurry₀ (ϕ ∘ inr₀ A₀ A₁)

  uncurry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set} 
    → (ϕ : π A (λ a → ev B a ⇒ X))
    → σ A B ⇒ X
  uncurry₀ {⊥₀} {B} {X} ϕ = ϕ
  uncurry₀ {⊤₀} {B} {X} ϕ = ϕ
  uncurry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} (ϕ₀ , ϕ₁) =
    uncurry₀ {A = A₀} {B = B₀} {X} ϕ₀ ,
    uncurry₀ {A = A₁} {B = B₁} {X} ϕ₁

  curry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set}
    → σ A B ⇒ X
    → π A (λ a → ev B a ⇒ X)
  curry₀ {⊥₀} {B} {X} α = α
  curry₀ {⊤₀} {B} {X} α = α
  curry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} (α , β) =
    curry₀ {A = A₀} {B = B₀} {X} α ,
    curry₀ {A = A₁} {B = B₁} {X} β

  -- Ok! This is much more interesting.  So now we have very precise
  -- control over how these objects compute.  The function type is
  -- defined as a finite collection of elements.

  -- Now we are going to render σ definitionally associative and
  -- see what the fuck happens.

  postulate

    cst-ev : {A : 𝔽} {X : Set} (x : X) (a : El A)
      → ev (cst₀ {A} x) a ↦ x 
    {-# REWRITE cst-ev #-}

    σ-unit-r : (A : 𝔽)
      → σ A (cst₀ {A} ⊤₀) ↦ A
    {-# REWRITE σ-unit-r #-}

    uncurry-unit-r : {A : 𝔽} {X : Set} (α : A ⇒ X)
      → uncurry₀ {A = A} {B = cst₀ {A} ⊤₀} {X = X} α ↦ α
    {-# REWRITE uncurry-unit-r #-}
