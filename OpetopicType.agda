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

    η-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X)
      → Cns X f ⊤ₚ (π-⊤ (cst (Frm X)) f)

    μ-cns : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
      → {frm : Frm X} {pos : ℙ} {typ : πₚ pos (cst (Frm X))}
      → (c : Cns X frm pos typ)
      → (δ : πₚ pos (λ p → Σ ℙ (λ δpos →
                           Σ (πₚ δpos (cst (Frm X))) (λ δtyp →
                           Cns X (app typ p) δpos δtyp))))
      → Cns X frm (Σₚ pos (map {Y = λ _ _ → ℙ} (λ _ → fst) δ))
                  (π-Σ pos (map (λ _ → fst) δ) (cst (Frm X))
                      (map {Y = λ u opr → πₚ (fst opr) (cst (Frm X))}
                        (λ u opr → fst (snd opr)) δ))

  --
  --  Monadic helpers
  --

  -- η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} (f : Frm X) → Opr X f
  -- η f = ⟪ _ , _ , η-cns f ⟫ₒₚ

  -- η-frm : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
  --   → (f : Frm Xₙ) (x : Xₛₙ f)
  --   → Frmₛ Xₛₙ f x 
  -- η-frm {Xₛₙ = Xₛₙ} f x = ⟪ η f , π-⊤ (λ p → Xₛₙ (app (typ (η f)) p)) x ⟫f

  -- μ : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n}
  --   → {f : Frm X} (c : Opr X f)
  --   → (δ : πₚ (pos c) (λ p → Opr X (app (typ c) p)))
  --   -- → (δ : (p : El (pos c)) → Opr X (app (typ c) p))
  --   → Opr X f
  -- μ c δ = ⟪ _ , _ , μ-cns c δ ⟫ₒₚ

  -- -- Nice.  So mapping works essentially as expected.
  -- -- Just have to clean this up a bit and put it into place....
  -- μ-frm' : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
  --   → {f : Frm Xₙ} {x : Xₛₙ f} (P : ℙ) (δf : πₚ P (cst (Frm Xₙ))) (δx : πₚ P (λ p → Xₛₙ (app δf p))) (c : Cns Xₙ f P δf)
  --   → (ϕ : πₚ P (λ p → Σ ℙ (λ Q → Σ (πₚ Q (cst (Frm Xₙ))) (λ δf' → Σ (πₚ Q (λ q → Xₛₙ (app δf' q))) (λ δx' → Cns Xₙ (app δf p) Q δf')))))
  --   → Frmₛ Xₛₙ f x
  -- μ-frm' P δf δx c ϕ  = ⟪ μ ⟪ P , δf , c ⟫ₒₚ (map (λ { p (Q , δf' , δx' , c') → ⟪ Q , δf' , c' ⟫ₒₚ } ) ϕ) ,
  --   π-Σ P (λ p → fst (app ϕ p)) _ (λ p → fst (snd (snd (app ϕ p)))) ⟫f

  -- postulate
  
  --   -- the trivial object constructor...
  --   obj : ∀ {ℓ} (P : ℙ) → Cns {ℓ = ℓ} {n = O} tt tt P (cstₚ P tt)

  --   lf : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ)
  --     → (f : Frm Xₙ) (x : Xₛₙ f)
  --     → Cns (Xₙ , Xₛₙ) (f , x , η-frm {Xₛₙ = Xₛₙ} f x) ⊥ₚ (π-⊥ _)

    -- Have to finish converting to decoration style ...
    -- nd : ∀ {ℓ} {n : ℕ} (Xₙ : 𝕆 ℓ n) (Xₛₙ : Frm Xₙ → Set ℓ)
    --   → {fₙ : Frm Xₙ} (x : Xₛₙ fₙ) (fₛₙ : Frmₛ Xₛₙ fₙ x)
    --   → (δ : (p : El (pos (opr fₛₙ))) → Frmₛ Xₛₙ (app (typ (opr fₛₙ)) p) (app (dec fₛₙ) p))
    --   → (ε : (p : El (pos (opr fₛₙ))) → Opr (Xₙ , Xₛₙ) (app (typ (opr fₛₙ)) p , app (dec fₛₙ) p , δ p)) 
    --   → Cns (Xₙ , Xₛₙ) (fₙ , x , μ-frm {Xₛₙ = Xₛₙ} {x = x} fₛₙ δ) 
    --       (⊤ₚ ⊔ₚ Σₚ (pos (opr fₛₙ)) (λ p → pos (ε p))) {!!} 
    --       -- (⊔-dec (⊤-dec (fₙ , x , fₛₙ))
    --       --        (Σ-dec (λ p → typ (ε p)))) 




