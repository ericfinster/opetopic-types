{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT

module Universe where

  --  Our strictly associative universe
  
  postulate

    𝕌 : Set
    El : 𝕌 → Set

    --
    -- Empty
    --
    
    ⊥ₛ : 𝕌

    ⊥ₛ-elim : (A : Set)
      → El ⊥ₛ → A
      
    --
    -- Unit
    --
    
    ⊤ₛ : 𝕌
    ttₛ : El ⊤ₛ

    ⊤ₛ-elim : (P : El ⊤ₛ → Set)
      → (p : P ttₛ)
      → (u : El ⊤ₛ) → P u

    ⊤ₛ-comp : (P : El ⊤ₛ → Set)
      → (p : P ttₛ)
      → ⊤ₛ-elim P p ttₛ ↦ p
    {-# REWRITE ⊤ₛ-comp #-}

    --
    -- Dependent sum
    --
    
    Σₛ : (A : 𝕌) (B : El A → 𝕌) → 𝕌

    prₛ : (A : 𝕌) (B : El A → 𝕌)
      → (a : El A) (b : El (B a))
      → El (Σₛ A B)

    fstₛ : (A : 𝕌) (B : El A → 𝕌)
      → (s : El (Σₛ A B))
      → El A

    sndₛ : (A : 𝕌) (B : El A → 𝕌)
      → (s : El (Σₛ A B))
      → El (B (fstₛ A B s))

    prₛ-β : (A : 𝕌) (B : El A → 𝕌) 
      → (s : El (Σₛ A B))
      → prₛ A B (fstₛ A B s) (sndₛ A B s) ↦ s
    {-# REWRITE prₛ-β #-}
    
    fstₛ-β : (A : 𝕌) (B : El A → 𝕌)
      → (a : El A) (b : El (B a))
      → fstₛ A B (prₛ A B a b) ↦ a
    {-# REWRITE fstₛ-β #-}

    sndₛ-β : (A : 𝕌) (B : El A → 𝕌)
      → (a : El A) (b : El (B a))
      → sndₛ A B (prₛ A B a b) ↦ b
    {-# REWRITE sndₛ-β #-}

    --
    --  Binary sums
    --
    
    _⊔ₛ_ : 𝕌 → 𝕌 → 𝕌 
    inlₛ : (A B : 𝕌) → El A → El (A ⊔ₛ B)
    inrₛ : (A B : 𝕌) → El B → El (A ⊔ₛ B)

    ⊔ₛ-elim : (A B : 𝕌) (P : El (A ⊔ₛ B) → Set)
      → (inl* : (a : El A) → P (inlₛ A B a))
      → (inr* : (b : El B) → P (inrₛ A B b))
      → (ab : El (A ⊔ₛ B)) → P ab

    ⊔ₛ-inl-β : (A B : 𝕌) (P : El (A ⊔ₛ B) → Set)
      → (inl* : (a : El A) → P (inlₛ A B a))
      → (inr* : (b : El B) → P (inrₛ A B b))
      → (a : El A)
      → ⊔ₛ-elim A B P inl* inr* (inlₛ A B a) ↦ inl* a 
    {-# REWRITE ⊔ₛ-inl-β #-}

    ⊔ₛ-inr-β : (A B : 𝕌) (P : El (A ⊔ₛ B) → Set)
      → (inl* : (a : El A) → P (inlₛ A B a))
      → (inr* : (b : El B) → P (inrₛ A B b))
      → (b : El B)
      → ⊔ₛ-elim A B P inl* inr* (inrₛ A B b) ↦ inr* b
    {-# REWRITE ⊔ₛ-inr-β #-}

    --
    --  Typing Equations
    --

    -- Σₛ is absorbing for ⊥ₛ
    Σₛ-absorb-right : (A : 𝕌)
      → Σₛ A (cst ⊥ₛ) ↦ ⊥ₛ
    {-# REWRITE Σₛ-absorb-right #-}

    Σₛ-absorb-left : (A : El ⊥ₛ → 𝕌)
      → Σₛ ⊥ₛ A ↦ ⊥ₛ
    {-# REWRITE Σₛ-absorb-left #-}

    -- prₛ-absorb-left : (A : El ⊥ₛ → 𝕌)
    --   → (b : El ⊥ₛ) (a : El (A b))
    --   → prₛ ⊥ₛ A b a ↦ {!!} 

    -- Σₛ is right unital
    Σₛ-unit-right : (A : 𝕌)
      → Σₛ A (cst ⊤ₛ) ↦ A
    {-# REWRITE Σₛ-unit-right #-}
  
    prₛ-unit-right : (A : 𝕌) (a : El A)
      → prₛ A (cst ⊤ₛ) a ttₛ ↦ a 
    {-# REWRITE prₛ-unit-right #-}

    fstₛ-unit-right : (A : 𝕌) (a : El A)
      → fstₛ A (cst ⊤ₛ) a ↦ a
    {-# REWRITE fstₛ-unit-right #-}

    sndₛ-unit-right : (A : 𝕌) (a : El A)
      → sndₛ A (cst ⊤ₛ) a ↦ ttₛ
    {-# REWRITE sndₛ-unit-right #-}

    -- Σₛ is left unital
    Σₛ-unit-left : (B : El ⊤ₛ → 𝕌)
      → Σₛ ⊤ₛ B ↦ B ttₛ
    {-# REWRITE Σₛ-unit-left #-}

    -- These next two may need to be generalized
    -- using ⊤ₛ-elim ....
    prₛ-unit-left : (B : El ⊤ₛ → 𝕌) (b : El (B ttₛ))
      → prₛ ⊤ₛ B ttₛ b ↦ b
    {-# REWRITE prₛ-unit-left #-}

    fstₛ-unit-left : (B : El ⊤ₛ → 𝕌) (b : El (B ttₛ))
      → fstₛ ⊤ₛ B b ↦ ttₛ
    {-# REWRITE fstₛ-unit-left #-}

    sndₛ-unit-left : (B : El ⊤ₛ → 𝕌) (b : El (B ttₛ))
      → sndₛ ⊤ₛ B b ↦ b
    {-# REWRITE sndₛ-unit-left #-}

    -- Σₛ is associative 
    Σₛ-assoc : (A : 𝕌) (B : El A → 𝕌) (C : El (Σₛ A B) → 𝕌)
      → Σₛ (Σₛ A B) C ↦ Σₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) 
    {-# REWRITE Σₛ-assoc #-}

    prₛ-assoc : (A : 𝕌) (B : El A → 𝕌) (C : El (Σₛ A B) → 𝕌)
      → (s : El (Σₛ A B)) (t : El (C s))
      → prₛ (Σₛ A B) C s t ↦ prₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) (fstₛ A B s)
                                 (prₛ (B (fstₛ A B s)) (λ b → C (prₛ A B (fstₛ A B s) b)) (sndₛ A B s) t)
    {-# REWRITE prₛ-assoc #-}

    fstₛ-assoc : (A : 𝕌) (B : El A → 𝕌) (C : El (Σₛ A B) → 𝕌)
      → (s : El (Σₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A (λ z → B z) a b)))))
      → fstₛ (Σₛ A B) C s ↦ prₛ A B (fstₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s)
                                    (fstₛ (B (fstₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s))
                                    (λ b → C (prₛ A B (fstₛ A (λ a → Σₛ (B a) (λ b₁ → C (prₛ A B a b₁))) s) b))
                                      (sndₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s))
    {-# REWRITE fstₛ-assoc #-}

    sndₛ-assoc : (A : 𝕌) (B : El A → 𝕌) (C : El (Σₛ A B) → 𝕌)
      → (s : El (Σₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A (λ z → B z) a b)))))
      → sndₛ (Σₛ A B) C s ↦ sndₛ (B (fstₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s))
                              (λ b → C (prₛ A B (fstₛ A (λ a → Σₛ (B a) (λ b₁ → C (prₛ A B a b₁))) s) b))
                                       (sndₛ A (λ a → Σₛ (B a) (λ b → C (prₛ A B a b))) s)
    {-# REWRITE sndₛ-assoc #-}


    -- Distributivity
    Σₛ-distrib : (A B : 𝕌) (C : El (A ⊔ₛ B) → 𝕌)
      → Σₛ (A ⊔ₛ B) C ↦ (Σₛ A (λ a → C (inlₛ A B a)) ⊔ₛ Σₛ B (λ b → C (inrₛ A B b)))
    {-# REWRITE Σₛ-distrib #-}

    prₛ-distrib : (A B : 𝕌) (C : El (A ⊔ₛ B) → 𝕌)
      → (ab : El (A ⊔ₛ B)) (c : El (C ab))
      → prₛ (A ⊔ₛ B) C ab c ↦ ⊔ₛ-elim A B (λ x → El (C x) → El (Σₛ A (λ a → C (inlₛ A B a)) ⊔ₛ Σₛ B (λ b → C (inrₛ A B b))))
                                          (λ a₀ c₀ → inlₛ _ _ (prₛ A (λ a → C (inlₛ A B a)) a₀ c₀))
                                          (λ b₀ c₀ → inrₛ _ _ (prₛ B (λ b → C (inrₛ A B b)) b₀ c₀)) ab c
    {-# REWRITE prₛ-distrib #-}

    fstₛ-distrib : (A B : 𝕌) (C : El (A ⊔ₛ B) → 𝕌)
      → (s : El (Σₛ (A ⊔ₛ B) C))
      → fstₛ (A ⊔ₛ B) C s ↦ ⊔ₛ-elim (Σₛ A (λ a → C (inlₛ A B a))) (Σₛ B (λ b → C (inrₛ A B b))) (λ _ → El (A ⊔ₛ B))
                                    (λ ac → inlₛ A B (fstₛ A (λ a → C (inlₛ A B a)) ac))
                                    (λ bc → inrₛ A B (fstₛ B (λ b → C (inrₛ A B b)) bc)) s 
    {-# REWRITE fstₛ-distrib #-}

    sndₛ-distrib : (A B : 𝕌) (C : El (A ⊔ₛ B) → 𝕌)
      → (s : El (Σₛ (A ⊔ₛ B) C))
      → sndₛ (A ⊔ₛ B) C s ↦ ⊔ₛ-elim (Σₛ A (λ a → C (inlₛ A B a))) (Σₛ B (λ b → C (inrₛ A B b))) (λ ab → El (C (fstₛ (A ⊔ₛ B) C ab)))
                                    (λ ac → sndₛ A (λ a → C (inlₛ A B a)) ac)
                                    (λ bc → sndₛ B (λ b → C (inrₛ A B b)) bc) s 
    {-# REWRITE sndₛ-distrib #-}
    
    -- ⊔ₛ is unital and associative
    ⊔ₛ-unit-right : (A : 𝕌)
      → (A ⊔ₛ ⊥ₛ) ↦ A 
    {-# REWRITE ⊔ₛ-unit-right #-}

    inlₛ-unit-right : (A : 𝕌) (a : El A)
      → inlₛ A ⊥ₛ a ↦ a 
    {-# REWRITE inlₛ-unit-right #-}

    ⊔ₛ-elim-unit-right : (A : 𝕌) (P : El (A ⊔ₛ ⊥ₛ) → Set)
      → (inl* : (a : El A) → P (inlₛ A ⊥ₛ a))
      → (inr* : (b : El ⊥ₛ) → P (inrₛ A ⊥ₛ b))
      → (ab : El (A ⊔ₛ ⊥ₛ)) → P ab
      → ⊔ₛ-elim A ⊥ₛ P inl* inr* ab ↦ inl* ab
    {-# REWRITE ⊔ₛ-elim-unit-right #-}

    ⊔ₛ-unit-left : (A : 𝕌)
      → (⊥ₛ ⊔ₛ A) ↦ A
    {-# REWRITE ⊔ₛ-unit-left #-}

    inrₛ-unit-left : (A : 𝕌) (a : El A)
      → inrₛ ⊥ₛ A a ↦ a
    {-# REWRITE inrₛ-unit-left #-}

    ⊔ₛ-elim-unit-left : (B : 𝕌) (P : El (⊥ₛ ⊔ₛ B) → Set)
      → (inl* : (a : El ⊥ₛ) → P (inlₛ ⊥ₛ B a))
      → (inr* : (b : El B) → P (inrₛ ⊥ₛ B b))
      → (ab : El (⊥ₛ ⊔ₛ B))
      → ⊔ₛ-elim ⊥ₛ B P inl* inr* ab ↦ inr* ab
    {-# REWRITE ⊔ₛ-elim-unit-left #-}

    -- Not quite sure which associativity will
    -- be more convenient.  Guess it doesn't matter?
    ⊔ₛ-assoc : (A B C : 𝕌)
      → ((A ⊔ₛ B) ⊔ₛ C) ↦ (A ⊔ₛ (B ⊔ₛ C))
    {-# REWRITE ⊔ₛ-assoc #-}

    inlₛ-assoc : (A B C : 𝕌)
      → (ab : El (A ⊔ₛ B))
      → inlₛ (A ⊔ₛ B) C ab ↦ ⊔ₛ-elim A B (λ _ → El (A ⊔ₛ (B ⊔ₛ C)))
                                     (λ a → inlₛ A (B ⊔ₛ C) a)
                                     (λ b → inrₛ A (B ⊔ₛ C) (inlₛ B C b)) ab
    {-# REWRITE inlₛ-assoc #-}
      
    inrₛ-assoc : (A B C : 𝕌)
      → (c : El C)
      → inrₛ (A ⊔ₛ B) C c ↦ inrₛ A (B ⊔ₛ C) (inrₛ B C c)
    {-# REWRITE inrₛ-assoc #-}

    ⊔ₛ-elim-assoc : (A B C : 𝕌) (P : El ((A ⊔ₛ B) ⊔ₛ C) → Set)
      → (inl* : (ab : El (A ⊔ₛ B)) → P (inlₛ (A ⊔ₛ B) C ab))
      → (inr* : (c : El C) → P (inrₛ (A ⊔ₛ B) C c))
      → (abc : El ((A ⊔ₛ B) ⊔ₛ C))
      → ⊔ₛ-elim (A ⊔ₛ B) C P inl* inr* abc ↦ ⊔ₛ-elim A (B ⊔ₛ C) P
                                                     (λ a → inl* (inlₛ A B a))
                                                     (⊔ₛ-elim B C (λ bc → P (inrₛ A (B ⊔ₛ C) bc))
                                                                  (λ b → inl* (inrₛ A B b)) inr*) abc
    {-# REWRITE ⊔ₛ-elim-assoc #-}
                                                                  

