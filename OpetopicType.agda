{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import PositionUniverse

module OpetopicType where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ

  postulate 

    Web : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (f : Frm X) (P : ℙ) (t : πₚ P (cst (Frm X)))
      → Set ℓ

  -- These should be reindexed to start at -1 ...
  𝕆 ℓ O = ⊤ 
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ X → (f : Frm X) → Set ℓ)

  Frm {n = O} X = ⊤
  Frm {n = S n} (Xₙ , Xₛₙ) =
    Σ (Frm Xₙ) (λ f →
    Σ (Xₛₙ f) (λ x → 
    Σ ℙ (λ P →
    Σ (πₚ P (cst (Frm Xₙ))) (λ δf →
    Σ (πₚ P (λ p → Xₛₙ (app δf p))) (λ δx → 
    Web Xₙ f P δf)))))

  postulate

    --
    --  Monadic signature
    -- 

    η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
      → Web X f ⊤ₚ (π-⊤ (cst (Frm X)) f)

    μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Web X c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Web X (app c-typ p) δ-pos δ-typ))))
      → Web X c-frm (Σₚ c-pos (lam c-pos (λ p → fst (app δ p))))
                    (π-Σ c-pos (lam c-pos (λ p → fst (app δ p))) (cst (Frm X))
                      (lam c-pos (λ p → lam (fst (app δ p))
                                 (λ q → app (fst (snd (app δ p))) q))))

    --
    --  Monadic laws
    --

    μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Web X c-frm c-pos c-typ)
      → μ c (lam c-pos (λ p → _ , _ , η (app c-typ p))) ↦ c
    {-# REWRITE μ-unit-r #-}
    
    μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (c-frm : Frm X)       
      → (δ : πₚ ⊤ₚ (λ p → Σ ℙ (λ δ-pos → Σ (πₚ δ-pos (cst (Frm X)))
                          (Web X (app (π-⊤ (cst (Frm X)) c-frm) p) δ-pos))))
      → μ (η c-frm) δ ↦ snd (snd (app δ ttₚ))
    {-# REWRITE μ-unit-l #-}

    -- μ-assoc : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
    --   → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
    --   → (c : Web X c-frm c-pos c-typ)
    --   → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
    --                          Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
    --                          Web X (app c-typ p) δ-pos δ-typ))))
    --   → (ε : πₚ (Σₚ c-pos (lam c-pos (λ p → fst (app δ p))))
    --             (λ pq → Σ ℙ (λ ε-pos →
    --                     Σ (πₚ ε-pos (cst (Frm X)))
    --                     (Web X (app (π-Σ c-pos (lam c-pos (λ p → fst (app δ p))) (cst (Frm X))
    --                                 (lam c-pos (λ p → fst (snd (app δ p))))) pq) ε-pos))))
    --   → μ (μ c δ) ε ↦ μ c (lam c-pos (λ p → _ , _ ,
    --                    μ (snd (snd (app δ p))) (lam (fst (app δ p)) (λ q →
    --                      app ε ⟦ c-pos , lam (c-pos) (λ p → fst (app δ p)) ∣ p , q ⟧ₚ))))
    -- {-# REWRITE μ-assoc #-}

    --
    --  Web Constructors
    --

    -- objects
    obj : ∀ {ℓ} (P : ℙ) → Web {ℓ = ℓ} {n = O} tt tt P (lam P (cst tt))

    -- leaves
    lf : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ)
      → (f : Frm Xₙ) (x : Xₛₙ f)
      → Web (Xₙ , Xₛₙ) (f , x , _ , _ , π-⊤ _ x , η f) ⊥ₚ (π-⊥ _)

    -- nodes
    nd : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ)
      → {c-frm : Frm Xₙ} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm Xₙ))}
      → (c : Web Xₙ c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm Xₙ))) (λ δ-typ →
                             Web Xₙ (app c-typ p) δ-pos δ-typ))))
                             
      → (x : Xₛₙ c-frm) (x' : πₚ c-pos (λ p → Xₛₙ (app c-typ p)))
      → (x'' : πₚ c-pos (λ p → πₚ (fst (app δ p)) (λ q → Xₛₙ (app (fst (snd (app δ p))) q))))

      → (ε : πₚ c-pos (λ p → Σ ℙ (λ ε-pos →
                             Σ (πₚ ε-pos (cst (Frm (Xₙ , Xₛₙ)))) (λ ε-typ →
                             Web (Xₙ , Xₛₙ) (app c-typ p , app x' p , fst (app δ p) ,
                                            fst (snd (app δ p)) , app x'' p ,
                                            snd (snd (app δ p))) ε-pos ε-typ))))
                             
      → Web (Xₙ , Xₛₙ) (c-frm , x , _ , _ , π-Σ c-pos (lam c-pos (λ p → fst (app δ p))) _ x'' , μ c δ)
          (⊤ₚ ⊔ₚ Σₚ c-pos (lam c-pos (λ p → fst (app ε p))))
          (π-⊔ (cst (Frm (Xₙ , Xₛₙ))) (π-⊤ _ (c-frm , x , c-pos , c-typ , x' , c))
                                      (π-Σ c-pos (lam c-pos (λ p → fst (app ε p))) (cst (Frm (Xₙ , Xₛₙ)))
                                        (lam c-pos (λ p → lam (fst (app ε p)) (λ q → app (fst (snd (app ε p))) q)))))





