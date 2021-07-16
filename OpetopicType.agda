{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import MiniHoTT
open import PositionUniverse

module OpetopicType where

  --
  --  The Universe of Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ} {n : ℕ} → 𝕆 ℓ n → Set ℓ

  postulate 

    Cns : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
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
    Cns Xₙ f P δf)))))

  postulate

    --
    --  Monadic signature
    -- 

    η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
      → Cns X f ⊤ₚ (π-⊤ (cst (Frm X)) f)

    μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Cns X c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Cns X (app c-typ p) δ-pos δ-typ))))
      → Cns X c-frm (Σₚ c-pos (map {Y = λ _ _ → ℙ} (λ _ → fst) δ))
                    (π-Σ c-pos (map (λ _ → fst) δ) (cst (Frm X))
                       (map {Y = λ u opr → πₚ (fst opr) (cst (Frm X))}
                         (λ u opr → fst (snd opr)) δ))


    --
    --  Monadic laws
    --

    μ-unit-r : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Cns X c-frm c-pos c-typ)
      → μ c (map {Y = λ p f → Σ ℙ (λ δ-pos →
                              Σ (πₚ δ-pos (cst (Frm X)))
                              (Cns X f δ-pos))} (λ p f → _ , _ , η f) c-typ)
        ↦ c

    μ-unit-l : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
      → (c-frm : Frm X)       
      → (δ : πₚ ⊤ₚ (λ p → Σ ℙ (λ δ-pos → Σ (πₚ δ-pos (cst (Frm X)))
                          (Cns X (app (π-⊤ (cst (Frm X)) c-frm) p) δ-pos))))
      → μ (η c-frm) δ ↦ snd (snd (app δ ttₚ))
    {-# REWRITE μ-unit-l #-}


    μ-assoc : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Cns X c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Cns X (app c-typ p) δ-pos δ-typ))))
      → (ε : πₚ (Σₚ c-pos (map (λ _ → fst) δ)) (λ pq →
                Σ ℙ (λ ε-pos →
                Σ (πₚ ε-pos (cst (Frm X)))
                (Cns X (app (π-Σ c-pos (map (λ _ → fst) δ) (cst (Frm X))
                       (map (λ u opr → fst (snd opr)) δ)) pq) ε-pos)))) → 
        let δ' : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Cns X (app c-typ p) δ-pos δ-typ)))
            δ' = {!!} 
       in μ (μ c δ) ε ↦ μ c δ'


-- Goal: Cns X c-frm
--       (Σₚ c-pos
--        (map (λ u → Σₚ (fst (app δ u)))
--         (uncurryₚ c-pos (map (λ _ → fst) δ) (map (λ _ → fst) ε))))
--       (π-Σ c-pos
--        (map (λ u → Σₚ (fst (app δ u)))
--         (uncurryₚ c-pos (map (λ _ → fst) δ) (map (λ _ → fst) ε)))
--        (λ _ → Frm X)
--        (map
--         (λ u →
--            π-Σ (fst (app δ u))
--            (app (uncurryₚ c-pos (map (λ _ → fst) δ) (map (λ _ → fst) ε)) u)
--            (λ v → Frm X))
--         (uncurryₚ c-pos (map (λ _ → fst) δ)
--          (map (λ u opr → fst (snd opr)) ε))))

-- Have: Cns X c-frm (Σₚ c-pos (map (λ _ → fst) ?0))
--       (π-Σ c-pos (map (λ _ → fst) ?0) (cst (Frm X))
--        (map (λ u opr → fst (snd opr)) ?0))



    -- μ-assoc : ∀ {ℓ} {n : ℕ} (X : 𝕆 ℓ n)
    --   → {f : Frm X} (c : Opr X f)
    --   → (δ : (p : El (pos c)) → Opr X (app (typ c) p))
    --   → (ε : (p : El (pos (μ c δ))) → Opr X (app (typ (μ c δ)) p))
    --   → μ-cns (μ c δ) ε ↦ μ-cns c (λ p → μ (δ p)
    --       (λ q → ε ⟦ pos c , (λ p → pos (δ p)) ∣ p , q ⟧ₚ))
    -- {-# REWRITE μ-assoc #-}

    --
    --  Tree constructors  (should we say Web????)
    --

    -- objects
    obj : ∀ {ℓ} (P : ℙ) → Cns {ℓ = ℓ} {n = O} tt tt P (cstₚ P tt)

    -- leaves
    lf : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ)
      → (f : Frm Xₙ) (x : Xₛₙ f)
      -- Can we make the fibration implicit for ⊤ and ⊥? 
      → Cns (Xₙ , Xₛₙ) (f , x , _ , _ , π-⊤ _ x , η f) ⊥ₚ (π-⊥ _)

    -- nodes
    nd : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ)
      → {c-frm : Frm Xₙ} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm Xₙ))}
      → (c : Cns Xₙ c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm Xₙ))) (λ δ-typ →
                             Cns Xₙ (app c-typ p) δ-pos δ-typ))))
                             
      → (x : Xₛₙ c-frm) (x' : πₚ c-pos (λ p → Xₛₙ (app c-typ p)))
      → (x'' : πₚ c-pos (λ p → πₚ (fst (app δ p)) (λ q → Xₛₙ (app (fst (snd (app δ p))) q))))

      → (ε : πₚ c-pos (λ p → Σ ℙ (λ ε-pos →
                             Σ (πₚ ε-pos (cst (Frm (Xₙ , Xₛₙ)))) (λ ε-typ →
                             Cns (Xₙ , Xₛₙ) (app c-typ p , app x' p , fst (app δ p) ,
                                            fst (snd (app δ p)) , app x'' p ,
                                            snd (snd (app δ p))) ε-pos ε-typ))))
                             
      → Cns (Xₙ , Xₛₙ) (c-frm , x , _ , _ , π-Σ c-pos (map (λ _ → fst) δ) _ x'' , μ c δ)
          (⊤ₚ ⊔ₚ Σₚ c-pos (map {Y = λ _ _ → ℙ} (λ _ → fst) ε))
          (π-⊔ {U = ⊤ₚ} {V = Σₚ c-pos (map {Y = λ _ _ → ℙ} (λ _ → fst) ε)}
            (cst (Frm (Xₙ , Xₛₙ))) (π-⊤ _ (c-frm , x , c-pos , c-typ , x' , c))
                                  (π-Σ c-pos (map (λ _ → fst) ε) (cst (Frm (Xₙ , Xₛₙ)))
                                         (map (λ u opr → fst (snd opr)) ε )))





