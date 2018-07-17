{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module Poly where

  record Poly (I : Type₀) : Type₁ where
    field
      γ : I → Type₀
      ρ : (i : I) (c : γ i) → Type₀
      τ : (i : I) (c : γ i) (p : ρ i c) → I

  open Poly public
  
  ⟦_⟧ : {I : Type₀} (P : Poly I) → (I → Set) → I → Set
  ⟦ P ⟧ X i = Σ (γ P i) (λ c → (p : ρ P i c) → X (τ P i c p))

  ⟦_⟧₀ : {I : Type₀} (P : Poly I) {X Y : I → Set}
    → (f : (i : I) → X i → Y i)
    → (i : I) → ⟦ P ⟧ X i → ⟦ P ⟧ Y i
  ⟦ P ⟧₀ f i (c , δ) =  c , (λ p → f (τ P i c p) (δ p))

  module _ {I : Type₀} (P : Poly I) where
  
    data W : I → Type₀ where
      lf : (i : I) → W i
      nd : (i : I) → ⟦ P ⟧ W i → W i

    leaf : {i : I} → W i → Type₀
    leaf (lf i) = ⊤
    leaf (nd i (c , δ)) = Σ (ρ P i c) (leaf ∘ δ)

    leaf-type : {i : I} (w : W i) (l : leaf w) → I
    leaf-type (lf i) tt = i
    leaf-type (nd i (c , δ)) (p , l) = leaf-type (δ p) l

    leaf-inv : {i₀ i₁ : I} (w : W i₀) 
      → (p : i₀ == i₁) 
      → leaf w ≃ leaf (transport W p w)
    leaf-inv w idp = ide (leaf w)

    leaf-inv-! : {i₀ i₁ : I} (w : W i₁) 
      → (p : i₀ == i₁) 
      → leaf w ≃ leaf (transport! W p w)
    leaf-inv-! w idp = ide (leaf w)

    leaf-inv-coh : {i₀ i₁ : I} (w : W i₀) 
      → (p : i₀ == i₁) (l : leaf w)
      → leaf-type w l == leaf-type (transport W p w) (–> (leaf-inv w p) l) 
    leaf-inv-coh w idp l = idp
    
    node : {i : I} → W i → Type₀
    node (lf i) = ⊥
    node (nd i (c , δ)) = ⊤ ⊔ Σ (ρ P i c) (node ∘ δ) 

    node-type : {i : I} (w : W i) (n : node w) → Σ I (γ P)
    node-type (lf i) ()
    node-type (nd i (c , δ)) (inl unit) = i , c
    node-type (nd i (c , δ)) (inr (p , n)) = node-type (δ p) n

    node-inv : {i₀ i₁ : I} (w : W i₁) 
      → (p : i₀ == i₁) 
      → node w ≃ node (transport! W p w)
    node-inv w idp = ide (node w)

    node-inv-coh : {i₀ i₁ : I} (w : W i₁) 
      → (p : i₀ == i₁)
      → (n : node (transport! W p w))
      → node-type w (<– (node-inv w p) n) == node-type (transport! W p w) n
    node-inv-coh w idp n = idp

    node-height : {i : I} (w : W i) (n : node w) → ℕ
    node-height (lf i) ()
    node-height (nd i (c , δ)) (inl unit) = O
    node-height (nd i (c , δ)) (inr (p , n)) = S (node-height (δ p) n)

    node-equiv : {i : I} (w₀ w₁ : W i) → Type₀
    node-equiv w₀ w₁ = Σ (node w₀ ≃ node w₁) (λ e → (n : node w₀) → node-type w₀ n == node-type w₁ (–> e n))

    -- This should be a property!
    is-height-preserving : {i : I} {w₀ w₁ : W i} (e : node-equiv w₀ w₁) → Type₀
    is-height-preserving {i} {w₀} {w₁} (e , _) =
      (n : node w₀) → node-height w₀ n == node-height w₁ (–> e n)

    -- reconstruction-lemma : {i : I} (w₀ w₁ : W i)
    --   → (e : node-equiv w₀ w₁)
    --   → (is-hp : is-height-preserving e)
    --   → w₀ == w₁
    -- reconstruction-lemma (lf i) (lf .i) (e , coh) is-hp = idp
    -- reconstruction-lemma (lf i) (nd .i _) (e , coh) is-hp = ⊥-elim (<– e (inl unit))
    -- reconstruction-lemma (nd i _) (lf .i) (e , coh) is-hp = ⊥-elim (–> e (inl unit))
    -- reconstruction-lemma (nd i (c₀ , δ₀)) (nd .i (c₁ , δ₁)) (e , coh) is-hp = {!!}

    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd i (c , λ p → lf (τ P i c p))

    corolla-ρ-eqv : {i : I} (c : γ P i)
      → leaf (corolla c) ≃ ρ P i c
    corolla-ρ-eqv c = Σ₂-Unit

    -- unique-node-lem : {i : I} (w : W i)
    --   → (is-c : is-contr (node w))
    --   → fst (node-type w (contr-center is-c)) == i
    -- unique-node-lem (lf i) is-c = ⊥-elim {P = λ _ → fst (node-type (lf i) (contr-center is-c)) == i} (contr-center is-c) 
    -- unique-node-lem (nd i (c , δ)) is-c = fst= (ap (λ x → node-type (nd i (c , δ)) x) (contr-path is-c (inl unit)))

    -- corolla-unique-pth : {i : I} (c : γ P i) (w : W i)
    --   → (is-c : is-contr (node w))
    --   → (pth : node-type w (contr-center is-c) == (i , c))
    --   → i == i
    -- corolla-unique-pth c (lf i) is-c pth = ⊥-elim (contr-center is-c)
    -- corolla-unique-pth c (nd i (c' , δ)) is-c pth =
    --   fst= ((! (ap (λ x → node-type (nd i (c' , δ)) x) (contr-path is-c (inl unit)))) ∙ pth)

    -- corolla-unique : {i : I} (c : γ P i) (w : W i)
    --   → (is-c : is-contr (node w))
    --   → (pth : node-type w (contr-center is-c) == (i , c))
    --   → corolla c == w [ W ↓ corolla-unique-pth c w is-c pth ]
    -- corolla-unique c (lf i) is-c pth =
    --   ⊥-elim {P = λ _ → corolla c == lf i [ W ↓ ⊥-elim (fst (has-level-apply is-c)) ]} (contr-center is-c) 
    -- corolla-unique c (nd i (c' , δ)) is-c pth = {!corolla=!} -- corolla= ∙'ᵈ and-so

    --   where lem : (i , c') == (i , c)
    --         lem = (! (ap (λ x → node-type (nd i (c' , δ)) x) (contr-path is-c (inl unit)))) ∙ pth

    --         corolla= : corolla c' == corolla c [ W ↓ fst= lem ]
    --         corolla= = {!apd↓-cst corolla (snd= lem)!}

    --         must-be-leaves : (p : ρ P i c') → δ p == lf (τ P i c' p)
    --         must-be-leaves p with δ p | inspect δ p
    --         must-be-leaves p | lf .(τ P i c' p) | ingraph e = idp
    --         must-be-leaves p | nd .(τ P i c' p) _ | ingraph e = ⊥-elim
    --           (inl≠inr unit no-no (contr-has-all-paths ⦃ is-c ⦄ (inl unit) (inr no-no))) 

    --           where no-no : Σ (ρ P i c') (node ∘ δ)
    --                 no-no = p , transport! node e (inl unit)

    --         and-so : corolla c' == nd i (c' , δ)
    --         and-so = ap (λ d → nd i (c' , d)) (λ= (λ p → ! (must-be-leaves p)))

  Fr : {I : Type₀} (P : Poly I) → Poly I
  γ (Fr P) = W P
  ρ (Fr P) i = leaf P {i}
  τ (Fr P) i = leaf-type P {i}

  module _ {I : Type₀} (P : Poly I) where
  
    γ-fr = γ (Fr P)
    ρ-fr = ρ (Fr P)
    τ-fr = τ (Fr P)
    
    graft : (i : I) (w : W P i) (ε : (l : leaf P w) → W P (leaf-type P w l)) → W P i
    graft i (lf .i) ε = ε tt
    graft i (nd .i (c , δ)) ε = nd i (c , λ p → graft (τ P i c p) (δ p) (λ l → ε (p , l)))

    --
    --  Leaves in a graft
    --
    
    graft-lf-to : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p) (δ p))
      → ρ-fr i (graft i w δ)
    graft-lf-to i (lf .i) δ (unit , p₁) = p₁
    graft-lf-to i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) =
      p₀ , graft-lf-to (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)

    graft-lf-from : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → ρ-fr i (graft i w δ)
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p) (δ p))
    graft-lf-from i (lf .i) δ p = unit , p
    graft-lf-from i (nd .i (c , δ₀)) δ (p₀ , p₁) =
      let pp = graft-lf-from (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
      in (p₀ , fst pp) , snd pp

    graft-lf-to-from : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → (p : ρ-fr i (graft i w δ))
      → graft-lf-to i w δ (graft-lf-from i w δ p) == p
    graft-lf-to-from i (lf .i) δ p = idp
    graft-lf-to-from i (nd .i (c , δ₀)) δ (p₀ , p₁) = 
      let ih = graft-lf-to-from (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
      in ap (λ p₂ → p₀ , p₂) ih

    graft-lf-from-to : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → (p : Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p)))
      → graft-lf-from i w δ (graft-lf-to i w δ p) == p
    graft-lf-from-to i (lf .i) δ (unit , p₁) = idp
    graft-lf-from-to i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) =
      let ih = graft-lf-from-to (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)
          ρ-fr-δ x = ρ-fr (τ-fr (τ P i c (fst x)) (δ₀ (fst x)) (snd x)) (δ x)
      in pair= (pair= idp (fst= ih)) (↓-ap-in ρ-fr-δ (λ x → (p₀ , x)) (snd= ih))

    graft-lf-eqv : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
        ≃ ρ-fr i (graft i w δ)
    graft-lf-eqv i w δ =
      equiv (graft-lf-to i w δ) (graft-lf-from i w δ)
            (graft-lf-to-from i w δ) (graft-lf-from-to i w δ)

    --
    --  Nodes in a graft
    --
    
    graft-nd-to : (i : I) (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l))
      → node P w ⊔ Σ (leaf P w) (node P ∘ ε) 
      → node P (graft i w ε)
    graft-nd-to i (lf .i) ε (inl ())
    graft-nd-to i (lf .i) ε (inr (unit , n)) = n
    graft-nd-to i (nd .i (c , δ)) ε (inl true) = inl unit
    graft-nd-to i (nd .i (c , δ)) ε (inl (inr (p , n))) =
      inr (p , graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n))
    graft-nd-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) =
      inr (p , (graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inr (l , n))))
    
    graft-nd-from : (i : I) (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l))
      → node P (graft i w ε)
      → node P w ⊔ Σ (leaf P w) (node P ∘ ε) 
    graft-nd-from i (lf .i) ε n = inr (tt , n)
    graft-nd-from i (nd .i (c , δ)) ε (inl unit) = inl (inl unit)
    graft-nd-from i (nd .i (c , δ)) ε (inr (p , n)) with graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) n
    graft-nd-from i (nd .i (c , δ)) ε (inr (p , n)) | inl n' = inl (inr (p , n'))
    graft-nd-from i (nd .i (c , δ)) ε (inr (p , n)) | inr (l , n') = inr ((p , l) , n')

    graft-nd-to-from : (i : I) (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l))
      → (n : node P (graft i w ε))
      → graft-nd-to i w ε (graft-nd-from i w ε n) == n
    graft-nd-to-from i (lf .i) ε n = idp
    graft-nd-to-from i (nd .i (c , δ)) ε (inl unit) = idp
    graft-nd-to-from i (nd .i (c , δ)) ε (inr (p , n)) with
      (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l))) n |
      inspect (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l))) n
    graft-nd-to-from i (nd .i (c , δ)) ε (inr (p , n)) | inl n' | ingraph e =
      ap (λ x → inr (p , x)) lem
  
      where lem = graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n')
                    =⟨ ! e |in-ctx (λ x → graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) x) ⟩
                  graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))
                    (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) n)
                    =⟨ graft-nd-to-from (τ P i c p) (δ p) (λ l → ε (p , l)) n ⟩ 
                  n ∎ 

    graft-nd-to-from i (nd .i (c , δ)) ε (inr (p , n)) | inr (l , n') | ingraph e = 
      ap (λ x → inr (p , x)) lem

      where lem = graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inr (l , n'))
                    =⟨ ! e |in-ctx (λ x → graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) x) ⟩ 
                  graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
                    (graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) n)
                    =⟨ graft-nd-to-from (τ P i c p) (δ p) (λ l → ε (p , l)) n ⟩ 
                  n ∎

    graft-nd-from-to : (i : I) (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l))
      → (n : node P w ⊔ Σ (leaf P w) (node P ∘ ε))
      → graft-nd-from i w ε (graft-nd-to i w ε n) == n
    graft-nd-from-to i (lf .i) ε (inl ())
    graft-nd-from-to i (lf .i) ε (inr (unit , n)) = idp
    graft-nd-from-to i (nd .i (c , δ)) ε (inl (inl unit)) = idp
    graft-nd-from-to i (nd .i (c , δ)) ε (inl (inr (p , n))) with 
      (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inl n)
      | inspect (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inl n)
    graft-nd-from-to i (nd .i (c , δ)) ε (inl (inr (p , n))) | inl n' | ingraph e =
      ap (λ x → inl (inr (p , x))) (–> (inl=inl-equiv n' n) lem)

      where lem = inl n' =⟨ ! e ⟩
                  graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l))
                    (graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n))
                    =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n) ⟩ 
                  inl n ∎
                  
    graft-nd-from-to i (nd .i (c , δ)) ε (inl (inr (p , n))) | inr (l , n') | ingraph e =
      ⊥-elim ((inr≠inl (l , n') n) lem)

      where lem = inr (l , n') =⟨ ! e ⟩ 
                  graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
                    (graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inl n))
                    =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n) ⟩ 
                  inl n ∎

    graft-nd-from-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) with
      (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inr (l , n))
      | inspect (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inr (l , n))
    graft-nd-from-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) | inl n' | ingraph e =
      ⊥-elim (inl≠inr n' (l , n) lem)

      where lem = inl n' =⟨ ! e ⟩
                  graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
                    (graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inr (l , n)))
                    =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inr (l , n)) ⟩ 
                  inr (l , n) ∎ 

    graft-nd-from-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) | inr (l' , n') | ingraph e =
      ap (λ x → inr ((p , fst x) , snd x)) (–> (inr=inr-equiv (l' , n') (l , n)) lem)

      where lem = inr (l' , n') =⟨ ! e ⟩
                  graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
                    (graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inr (l , n)))
                    =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inr (l , n)) ⟩ 
                  inr (l , n) ∎ 

    
    graft-nd-eqv : (i : I) (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l))
      → node P w ⊔ Σ (leaf P w) (node P ∘ ε) 
        ≃ node P (graft i w ε)
    graft-nd-eqv i w ε =
      equiv (graft-nd-to i w ε) (graft-nd-from i w ε)
            (graft-nd-to-from i w ε) (graft-nd-from-to i w ε)
