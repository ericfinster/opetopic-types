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


  --
  --  Monadic signature
  -- 

  η : ∀ {ℓ} {X : 𝕆 ℓ} (f : Frm X)
    → Web X f ⊤ₚ (π-⊤ (cst (Frm X)) f)

  postulate
  
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
    --  Monadic laws
    --

    μ-unit-r : ∀ {ℓ} (X : 𝕆 ℓ)
      → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
      → (c : Web X c-frm c-pos c-typ)
      → μ c (lam c-pos (λ p → _ , _ , η (app c-typ p))) ↦ c
    {-# REWRITE μ-unit-r #-}
    
    μ-unit-l : ∀ {ℓ} (X : 𝕆 ℓ)
      → (c-frm : Frm X)       
      → (δ : πₚ ⊤ₚ (λ p → Σ ℙ (λ δ-pos → Σ (πₚ δ-pos (cst (Frm X)))
                          (Web X (app (π-⊤ (cst (Frm X)) c-frm) p) δ-pos))))
      → μ (η c-frm) δ ↦ snd (snd (app δ ttₚ))
    {-# REWRITE μ-unit-l #-}

    -- μ-assoc : ∀ {ℓ} {X : 𝕆 ℓ}
    --   → {c-frm : Frm X} {c-pos : ℙ} {c-typ : πₚ c-pos (cst (Frm X))}
    --   → (c : Web X c-frm c-pos c-typ)
    --   → (δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos →
    --                          Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
    --                          Web X (app c-typ p) δ-pos δ-typ))))
    --   → (ε : πₚ (Σₚ c-pos (λ p → fst (app δ p)))
    --             (λ pq → Σ ℙ (λ ε-pos →
    --                     Σ (πₚ ε-pos (cst (Frm X)))
    --                     (Web X (app (π-Σ c-pos (λ p → fst (app δ p)) (cst (Frm X))
    --                                 (lam c-pos (λ p → fst (snd (app δ p))))) pq) ε-pos))))
    --   → μ (μ c δ) ε ↦ μ c (lam c-pos (λ p → _ , _ ,
    --                    μ (snd (snd (app δ p))) (lam (fst (app δ p)) (λ q →
    --                      app ε ⟦ c-pos , (λ p → fst (app δ p)) ∣ p , q ⟧ₚ))))
    -- {-# REWRITE μ-assoc #-}

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
  --  Monadic implementations
  --

  -- This is an η-expansion problem for ⊤ₚ ....
  η {X = ●} _ = tt
  η {X = X ∣ Y} (f , y , c-pos , c-typ , y'' , c) = {!y''!} 
    -- nd c  (lam c-pos (λ p → _ , _ , η (app c-typ p))) y y'' (lam c-pos (λ p → π-⊤ _ (app y'' p))) (lam c-pos (λ p → ⊥ₚ , π-⊥ _ , lf (app c-typ p) (app y'' p)))

     where fred : πₚ c-pos (λ p → Y (app c-typ p))
           fred = lam c-pos (λ u →
                      app (app (lam c-pos (λ p →
                        π-⊤ (λ q → Y (app (fst (snd
                            (app (lam c-pos {X = λ p → Σ ℙ (λ δ-pos →
                                                       Σ (πₚ δ-pos (cst (Frm X))) (λ δ-typ →
                                                       Web X (app c-typ p) δ-pos δ-typ))}
                              (λ p₁ → ⊤ₚ , π-⊤ (cst (Frm X)) (app c-typ p₁) , η (app c-typ p₁)))
                             p))) q))
                      (app y'' p))) u) ttₚ)

           claim : fred ≡ y''
           claim = refl

           δ : πₚ c-pos (λ p → Σ ℙ (λ δ-pos → Σ (πₚ δ-pos (cst (Frm X))) (Web X (app c-typ p) δ-pos)))
           δ = lam c-pos (λ p → ⊤ₚ , π-⊤ (cst (Frm X)) (app c-typ p) , η (app c-typ p))

           y''' : πₚ c-pos (λ p → πₚ (fst (app δ p)) (λ q → Y (app (fst (snd (app δ p))) q)))
           y''' = lam c-pos (λ p → π-⊤ _ (app y'' p)) 


           ε : πₚ c-pos (λ p → Σ ℙ (λ ε-pos →
                             Σ (πₚ ε-pos (cst (Frm (X ∣ Y)))) (λ ε-typ →
                             Webₛ X Y (app c-typ p , app y'' p , fst (app δ p) ,
                                            fst (snd (app δ p)) , app y''' p ,
                                            snd (snd (app δ p))) ε-pos ε-typ)))
           ε = lam c-pos (λ p → ⊥ₚ , π-⊥ _ , lf (app c-typ p) (app y'' p))
           
           attempt : Webₛ X Y (f , y , c-pos , c-typ ,  y'' , c)
                       ⊤ₚ (π-⊤ _ (f , y , c-pos , c-typ , y'' , c))
           attempt = {! nd c δ y y'' y''' ε  !}

           ive-got : Webₛ X Y (f , y , c-pos ,  c-typ ,
                                     lam c-pos (λ u → app (app
                                       (lam c-pos
                                        (λ p →
                                           π-⊤ (λ q → Y (app (π-⊤ (cst (Frm X)) (app c-typ p)) q))
                                           (app y'' p))) u) ttₚ) , c)
                     ⊤ₚ (π-⊤ _ (f , y , c-pos , c-typ , y'' , c))
           ive-got = {!nd c δ y y'' y''' ε!} -- 
           

  -- η-cns {n = O} f = tt
  -- η-cns {n = S n} {X = Xₙ , Xₛₙ} (fₙ , x , fₛₙ) = 
  --   nd x fₛₙ (λ p → η-frm {Xₛₙ = Xₛₙ} (app (typ (opr fₛₙ)) p) (dec fₛₙ p))
  --           (λ p → ⟪ _ , _ , lf (app (typ (opr fₛₙ)) p) (dec fₛₙ p) ⟫ₒₚ)

  -- μ-cns {n = O} _ _ = tt
  -- μ-cns {n = S n} ⟪ _ , _ , lf f x ⟫ₒₚ κ = lf f x
  -- μ-cns {n = S n} {X = Xₙ , Xₛₙ} ⟪ _ , _ , nd {fₙ} x fₛₙ δ ε ⟫ₒₚ κ = 
  --   let w = κ (inlₚ (Σₚ (pos (opr fₛₙ)) (λ p₁ → pos (ε p₁))) ttₚ)
  --       κ' p q = κ (inrₚ ⊤ₚ ⟦ pos (opr fₛₙ) , (λ p₁ → pos (ε p₁)) ∣ p , q ⟧ₚ) 
  --       ϕ p = μ (ε p) (κ' p) 
  --   in γ-cns w δ ϕ

  -- γ-cns ⟪ _ , _ , lf f x ⟫ₒₚ δ ε = cns (ε ttₚ)
  -- γ-cns {Xₙ = Xₙ} {Xₛₙ = Xₛₙ} ⟪ _ , _ , nd {fₙ} x c δ ε ⟫ₒₚ ϕ ψ =
  --   let ϕ' p q = ϕ ⟦ pos (opr c) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
  --       ψ' p q = ψ ⟦ pos (opr c) , (λ p' → pos (opr (δ p'))) ∣ p , q ⟧ₚ
  --       δ' p = μ-frm {Xₛₙ = Xₛₙ} {x = dec c p} (δ p) (ϕ' p)
  --       ε' p = ⟪ _ , _ , γ-cns (ε p) (ϕ' p) (ψ' p) ⟫ₒₚ
  --   in nd x c δ' ε'
  --
  --  Infinite Opetopic Types
  --

  record 𝕆∞ {ℓ} (X : 𝕆 ℓ) : Set (ℓ-suc ℓ) where
    coinductive
    field
      Head : Frm X → Set ℓ
      Tail : 𝕆∞ (X ∣ Head)

  open 𝕆∞ public 
