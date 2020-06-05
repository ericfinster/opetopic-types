{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FiniteUniverse where

  postulate

    𝔹 : Set
    El : 𝔹 → Set

    𝟘 : 𝔹
    𝕊 : 𝔹 → 𝔹

    z : {U : 𝔹} → El (𝕊 U)
    s : {U : 𝔹} → El U → El (𝕊 U)

    π : (U : 𝔹) (V : El U → Set) → Set
    ev : {U : 𝔹} {V : El U → Set}
      → π U V → (u : El U) → V u

    π-𝟘 : (V : El 𝟘 → Set)
      → π 𝟘 V ↦ ⊤
    {-# REWRITE π-𝟘 #-}

    π-𝕊 : (U : 𝔹) (V : El (𝕊 U) → Set)
      → π (𝕊 U) V ↦ V z × π U (V ∘ s)
    {-# REWRITE π-𝕊 #-}
    
    ev-z : (U : 𝔹) (V : El (𝕊 U) → Set)
      → (ϕ : π (𝕊 U) V)
      → ev {V = V} ϕ z ↦ fst ϕ
    {-# REWRITE ev-z #-}

    ev-s : (U : 𝔹) (V : El (𝕊 U) → Set)
      → (ϕ : π (𝕊 U) V) (u : El U)
      → ev {V = V} ϕ (s u) ↦ ev {V = V ∘ s} (snd ϕ) u
    {-# REWRITE ev-s #-}

    --
    --  These guys can be defined ...
    --

    _⊕_ : 𝔹 → 𝔹 → 𝔹 

    ⊕-𝟘 : (U : 𝔹) 
      → (U ⊕ 𝟘) ↦ U

    ⊕-𝕊 : (U V : 𝔹)
      → (U ⊕ (𝕊 V)) ↦ 𝕊 (U ⊕ V)

    σ : (U : 𝔹) (V : π U (cst 𝔹)) → 𝔹

    σ-𝟘 : (V : π 𝟘 (cst 𝔹))
      → σ 𝟘 V ↦ 𝟘 

    σ-𝕊 : (U : 𝔹) (V : π (𝕊 U) (cst 𝔹))
      → σ (𝕊 U) V ↦ (fst V ⊕ σ U (snd V) ) 

    fst-σ : {U : 𝔹} {V : π U (cst 𝔹)}
      → El (σ U V) → El U

    snd-σ : {U : 𝔹} {V : π U (cst 𝔹)}
      → (uv : El (σ U V)) → El (ev V (fst-σ uv))

    ◁ : (U : 𝔹) (V : π U (cst 𝔹)) (W : (u : El U) → El (ev V u) → Set)
      → π U (λ u → π (ev V u) (W u))
      → π (σ U V) (λ uv → W (fst-σ uv) (snd-σ uv))

    unev : {U : 𝔹} {V : El U → Set}
      → (ϕ : (u : El U) → V u)
      → π U V 

    ev-unev : {U : 𝔹} {V : El U → Set}
      → (ϕ : (u : El U) → V u) (u : El U)
      → ev (unev {U = U} {V = V} ϕ) u ↦ ϕ u
    {-# REWRITE ev-unev #-}

  infixr 50 _⇒_
  
  _⇒_ : 𝔹 → Set → Set
  U ⇒ X = π U (cst X)

  𝟙 : 𝔹
  𝟙 = 𝕊 𝟘

  cst-𝔹 : {X : Set} (U : 𝔹) → X → U ⇒ X
  cst-𝔹 {X} U x = unev {U = U} {V = cst X} (cst x)

  -- Okay.  What I'm going to do is simply just axiomatize exactly
  -- what I need to make things typecheck, and we will worry about
  -- the realization problem later.

  -- Now, we come to what is, I guess, the main point.  I don't want
  -- to allow π to be higher order, I want you to define π elements
  -- of π by *induction*.  So I guess this is somehow exactly the
  -- elimination rule for 𝔹.

  -- Hmmm.  But it does not actually seem like there *is* any
  -- condition on this restricted π: they are always tuples, and
  -- so picking an element should not make a difference...

  -- data 𝔹 : Set where
  --   𝟘 : 𝔹
  --   𝕊 : 𝔹 → 𝔹

  -- Tup : (n : ℕ) (X : Set) → Set
  -- Tup O X = ⊤
  -- Tup (S n) X = X × (Tup n X)

  -- Errr.  Frustrating.  How to define this guy? So, there clearly is
  -- a map ℕ → 𝔹.  I guess what I want to say is that, we can extend
  -- over this map.  So, we could start with the naive definition, and
  -- then show that any equivalence from Fin n ≃ Fin n extends to an
  -- equivalence of this guy.  In principle, this should be a
  -- characterization of 𝔹.  I see. Okay.

  -- Okay, but we actually need the dependent guy.  So, we need
  -- dependent tupling.  And then is σ a definition? π? 
  
  -- infixl 50 _⊔₀_
  
  -- data 𝔽 : Set where
  --   ⊥₀ : 𝔽
  --   ⊤₀ : 𝔽
  --   _⊔₀_ : 𝔽 → 𝔽 → 𝔽

  -- postulate

  --   El : 𝔽 → Set 

  --   ⊥₀-elim : (A : Set)
  --     → El ⊥₀ → A

  --   tt₀ : El ⊤₀

  --   ⊤₀-elim : (P : El ⊤₀ → Set)
  --     → (p : P tt₀)
  --     → (u : El ⊤₀) → P u

  --   ⊤₀-comp : (P : El ⊤₀ → Set)
  --     → (p : P tt₀)
  --     → ⊤₀-elim P p tt₀ ↦ p
  --   {-# REWRITE ⊤₀-comp #-}

  --   inl₀ : (A B : 𝔽) → El A → El (A ⊔₀ B)
  --   inr₀ : (A B : 𝔽) → El B → El (A ⊔₀ B)

  --   ⊔₀-elim : (A B : 𝔽) (P : El (A ⊔₀ B) → Set)
  --     → (inl* : (a : El A) → P (inl₀ A B a))
  --     → (inr* : (b : El B) → P (inr₀ A B b))
  --     → (ab : El (A ⊔₀ B)) → P ab

  --   ⊔₀-inl-β : (A B : 𝔽) (P : El (A ⊔₀ B) → Set)
  --     → (inl* : (a : El A) → P (inl₀ A B a))
  --     → (inr* : (b : El B) → P (inr₀ A B b))
  --     → (a : El A)
  --     → ⊔₀-elim A B P inl* inr* (inl₀ A B a) ↦ inl* a 
  --   {-# REWRITE ⊔₀-inl-β #-}

  --   ⊔₀-inr-β : (A B : 𝔽) (P : El (A ⊔₀ B) → Set)
  --     → (inl* : (a : El A) → P (inl₀ A B a))
  --     → (inr* : (b : El B) → P (inr₀ A B b))
  --     → (b : El B)
  --     → ⊔₀-elim A B P inl* inr* (inr₀ A B b) ↦ inr* b
  --   {-# REWRITE ⊔₀-inr-β #-}

  --   --
  --   --  Strict Associativity
  --   --
    
  --   ⊔-unit-l : (A : 𝔽)
  --     → ⊥₀ ⊔₀ A ↦ A 
  --   {-# REWRITE ⊔-unit-l #-}

  --   ⊔-unit-r : (A : 𝔽)
  --     → A ⊔₀ ⊥₀ ↦ A
  --   {-# REWRITE ⊔-unit-r #-}
    
  --   ⊔-assoc : (A B C : 𝔽)
  --     → A ⊔₀ (B ⊔₀ C) ↦ (A ⊔₀ B) ⊔₀ C 
  --   {-# REWRITE ⊔-assoc #-}

  -- π : (F : 𝔽) (X : El F → Set) → Set
  -- π ⊥₀ X = ⊤
  -- π ⊤₀ X = X tt₀
  -- π (F ⊔₀ G) X = π F (λ f → X (inl₀ F G f)) × π G (λ g → X (inr₀ F G g))

  -- ev : {F : 𝔽} {X : El F → Set}
  --   → π F X → (f : El F) → X f
  -- ev {⊥₀} {X} α f = ⊥₀-elim (X f) f
  -- ev {⊤₀} {X} α f = ⊤₀-elim X α f
  -- ev {A ⊔₀ B} {X} (α , β) f = ⊔₀-elim A B X (ev α) (ev β) f

  -- infixr 50 _⇒_
  
  -- _⇒_ : 𝔽 → Set → Set
  -- A ⇒ X = π A (cst X)

  -- cst₀ : {A : 𝔽} {X : Set} → X → A ⇒ X
  -- cst₀ {⊥₀} {X} _ = tt
  -- cst₀ {⊤₀} {X} x = x
  -- cst₀ {A₀ ⊔₀ A₁} {X} x =
  --   cst₀ {A₀} {X} x , cst₀ {A₁} {X} x

  -- σ : (A : 𝔽) (B : A ⇒ 𝔽) → 𝔽
  -- σ ⊥₀ _ = ⊥₀
  -- σ ⊤₀ B = B
  -- σ (A₀ ⊔₀ A₁) (B₀ , B₁) = σ A₀ B₀ ⊔₀ σ A₁ B₁

  -- -- curry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set} → σ A B ⇒ X
  -- --   → (a : El A) → ev B a ⇒ X
  -- -- curry₀ {⊥₀} {B} {X} α a = ⊥₀-elim (⊥₀-elim 𝔽 a ⇒ X) a
  -- -- curry₀ {⊤₀} {B} {X} α a = ⊤₀-elim (λ u → ⊤₀-elim (cst 𝔽) B u ⇒ X) α a
  -- -- curry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} (α , β) ab =
  -- --   ⊔₀-elim A₀ A₁ (λ u → ⊔₀-elim A₀ A₁ (cst 𝔽) (ev B₀) (ev B₁) u ⇒ X)
  -- --   (λ a → curry₀ α a) (λ b → curry₀ β b) ab
  
  -- -- uncurry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set} 
  -- --   → (ϕ : (a : El A) → ev B a ⇒ X)
  -- --   → σ A B ⇒ X
  -- -- uncurry₀ {⊥₀} {B} {X} ϕ = tt
  -- -- uncurry₀ {⊤₀} {B} {X} ϕ = ϕ tt₀
  -- -- uncurry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} ϕ =
  -- --   uncurry₀ (ϕ ∘ inl₀ A₀ A₁) , uncurry₀ (ϕ ∘ inr₀ A₀ A₁)

  -- uncurry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set} 
  --   → (ϕ : π A (λ a → ev B a ⇒ X))
  --   → σ A B ⇒ X
  -- uncurry₀ {⊥₀} {B} {X} ϕ = ϕ
  -- uncurry₀ {⊤₀} {B} {X} ϕ = ϕ
  -- uncurry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} (ϕ₀ , ϕ₁) =
  --   uncurry₀ {A = A₀} {B = B₀} {X} ϕ₀ ,
  --   uncurry₀ {A = A₁} {B = B₁} {X} ϕ₁

  -- curry₀ : {A : 𝔽} {B : A ⇒ 𝔽} {X : Set}
  --   → σ A B ⇒ X
  --   → π A (λ a → ev B a ⇒ X)
  -- curry₀ {⊥₀} {B} {X} α = α
  -- curry₀ {⊤₀} {B} {X} α = α
  -- curry₀ {A₀ ⊔₀ A₁} {B₀ , B₁} {X} (α , β) =
  --   curry₀ {A = A₀} {B = B₀} {X} α ,
  --   curry₀ {A = A₁} {B = B₁} {X} β

  -- -- Ok! This is much more interesting.  So now we have very precise
  -- -- control over how these objects compute.  The function type is
  -- -- defined as a finite collection of elements.

  -- -- Now we are going to render σ definitionally associative and
  -- -- see what the fuck happens.

  -- postulate

  --   cst-ev : {A : 𝔽} {X : Set} (x : X) (a : El A)
  --     → ev (cst₀ {A} x) a ↦ x 
  --   {-# REWRITE cst-ev #-}

  --   σ-unit-r : (A : 𝔽)
  --     → σ A (cst₀ {A} ⊤₀) ↦ A
  --   {-# REWRITE σ-unit-r #-}

  --   uncurry-unit-r : {A : 𝔽} {X : Set} (α : A ⇒ X)
  --     → uncurry₀ {A = A} {B = cst₀ {A} ⊤₀} {X = X} α ↦ α
  --   {-# REWRITE uncurry-unit-r #-}
