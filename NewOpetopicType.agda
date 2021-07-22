{-# OPTIONS --without-K --rewriting --no-positivity --guardedness #-}

open import MiniHoTT
open import PositionUniverse

module NewOpetopicType where

  --
  --  The Universe of Opetopic Types
  --

  data 𝕆 (ℓ : Level) : Set (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ} → 𝕆 ℓ → Set ℓ
  Web : ∀ {ℓ} (X : 𝕆 ℓ)
    → (f : Frm X) (P : ℙ)
    → (t : πₚ P (cst (Frm X)))
    → Set ℓ

  data 𝕆 ℓ where
    ● : 𝕆 ℓ
    _∣_ : (X : 𝕆 ℓ) (Y : Frm X → Set ℓ) → 𝕆 ℓ 

  Frm ● = ⊤ 
  Frm (X ∣ Y) = 
    Σ (Frm X) (λ f →
    Σ (Y f) (λ x → 
    Σ ℙ (λ P →
    Σ (πₚ P (cst (Frm X))) (λ δf →
    Σ (πₚ P (λ p → Y (app δf p))) (λ δx → 
    Web X f P δf)))))

  postulate

    --
    --  Monadic signature
    -- 

    η : ∀ {ℓ} {X : 𝕆 ℓ} (f : Frm X)
      → Web X f ⊤ₚ (π-⊤ (cst (Frm X)) f)

    μ : ∀ {ℓ} {X : 𝕆 ℓ}
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Web X c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Web X (app c-typ p) δ-pos δ-typ))))
      → Web X c-frm (Σₚ c-pos (λ p → fst (app δ p)))
          (π-Σ c-pos (λ p → fst (app δ p)) (cst (Frm X))
          (lam c-pos λ p → lam (fst (app δ p)) λ q →
              app (fst (snd (app δ p))) q))

    γ : ∀ {ℓ} {X : 𝕆 ℓ} {Y : Frm X → Set ℓ}

      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Web X c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Web X (app c-typ p) δ-pos δ-typ))))

      → (y : Y c-frm) (y' : πₚ c-pos (λ p → Y (app c-typ p)))
      → (y'' : πₚ c-pos (λ p → πₚ (fst (app δ p)) (λ q → Y (app (fst (snd (app δ p))) q))))

      → (ω-pos : ℙ) (ω-typ : πₚ ω-pos (cst (Frm (X ∣ Y))))
      → (ω : Web (X ∣ Y) (c-frm , y , c-pos , c-typ , y' , c) ω-pos ω-typ)

      → (ε : πₚ c-pos (λ p → Σ ℙ (λ ε-pos →
                             Σ (πₚ ε-pos (cst (Frm (X ∣ Y)))) (λ ε-typ →
                             Web (X ∣ Y) (app c-typ p , app y' p , fst (app δ p) ,
                                            fst (snd (app δ p)) , app y'' p ,
                                            snd (snd (app δ p))) ε-pos ε-typ))))

      → Web (X ∣ Y) (c-frm , y , _ , _ ,  π-Σ c-pos (λ p → fst (app δ p)) _ y'' , μ c δ)
          (ω-pos ⊔ₚ Σₚ c-pos (λ p → fst (app ε p)))
          (π-⊔ {U = ω-pos} {V = Σₚ c-pos (λ p → fst (app ε p))} _ ω-typ
            (π-Σ c-pos (λ p → fst (app ε p)) (cst (Frm (X ∣ Y)))
               (lam c-pos λ p → lam (fst (app ε p)) λ q →
                 app (fst (snd (app ε p))) q)))

  --
  --  The data of a next dim'l web tree
  --
  
  data Webₛ {ℓ} (X : 𝕆 ℓ) (Y : Frm X → Set ℓ) :
    Frm (X ∣ Y) → (Q : ℙ) → πₚ Q (cst (Frm (X ∣ Y))) → Set ℓ where

    lf : (f : Frm X) (y : Y f)
      → Webₛ X Y (f , y , ⊤ₚ , π-⊤ _ f , π-⊤ _ y , η f)
          ⊥ₚ (π-⊥ _) 

    nd : {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Web X c-frm c-pos c-typ)
      → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
                             Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                             Web X (app c-typ p) δ-pos δ-typ))))
                             
      → (y : Y c-frm) (y' : πₚ c-pos (λ p → Y (app c-typ p)))
      → (y'' : πₚ c-pos (λ p → πₚ (fst (app δ p)) (λ q → Y (app (fst (snd (app δ p))) q))))

      → (ε : πₚ c-pos (λ p → Σ ℙ (λ ε-pos →
                             Σ (πₚ ε-pos (cst (Frm (X ∣ Y)))) (λ ε-typ →
                             Webₛ X Y (app c-typ p , app y' p , fst (app δ p) ,
                                            fst (snd (app δ p)) , app y'' p ,
                                            snd (snd (app δ p))) ε-pos ε-typ))))

      → Webₛ X Y (c-frm , y , _ , _ , π-Σ c-pos (λ p → fst (app δ p)) _ y'' , μ c δ)
          (⊤ₚ ⊔ₚ Σₚ c-pos (λ p → fst (app ε p)))
          (π-⊔ (cst (Frm (X ∣ Y)))
            (π-⊤ _ (c-frm , y , c-pos , c-typ , y' , c))
            (π-Σ c-pos (λ p → fst (app ε p)) (cst (Frm (X ∣ Y)))
              ((lam c-pos (λ p → lam (fst (app ε p)) (λ q → app (fst (snd (app ε p))) q)))))) 

  Web ● tt P δ = ⊤
  Web (X ∣ Y) = Webₛ X Y

  --
  --  Infinite Opetopic Types
  --

  record 𝕆∞ {ℓ} (X : 𝕆 ℓ) : Set (ℓ-suc ℓ) where
    coinductive
    field
      Head : Frm X → Set ℓ
      Tail : 𝕆∞ (X ∣ Head)

  open 𝕆∞ public 
