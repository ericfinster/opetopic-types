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

    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd i (c , λ p → lf (τ P i c p))

    corolla-ρ-eqv : {i : I} (c : γ P i)
      → leaf (corolla c) ≃ ρ P i c
    corolla-ρ-eqv c = Σ₂-Unit

    unique-node-lem : {i : I} (w : W i)
      → (is-c : is-contr (node w))
      → fst (node-type w (contr-center is-c)) == i
    unique-node-lem (lf i) is-c = ⊥-elim {P = λ _ → fst (node-type (lf i) (contr-center is-c)) == i} (contr-center is-c) 
    unique-node-lem (nd i (c , δ)) is-c = fst= (ap (λ x → node-type (nd i (c , δ)) x) (contr-path is-c (inl unit)))

    -- -- Right.  It's clear that you can do this.
    -- -- It's what you've done below.
    -- reconstruct : {i : I} (w : W i)
    --   → (is-c : is-contr (node w))
    --   → w == corolla (snd (node-type w (contr-center is-c))) [ W ↓ ! (unique-node-lem w is-c) ]
    -- reconstruct w is-c = {!!}

    is-corolla : Σ I W → Type₀
    is-corolla (i , w) = is-contr (node w)
    
    corolla-eqv-to : Σ I (γ P) → Σ (Σ I W) is-corolla
    corolla-eqv-to (i , c) = (i , corolla c) , {!!}

    corolla-eqv-from : Σ (Σ I W) is-corolla → Σ I (γ P)
    corolla-eqv-from ((i , w) , is-c) = node-type w (contr-center is-c)

    corolla-eqv : is-equiv corolla-eqv-to
    corolla-eqv = {!!}

    -- Okay, if we have this, then the I think the type of
    -- i and w which project to (i , c) is contractible.

    -- Does this solve the problem?
    
    -- Annoying.  I seem to blow a bubble.  But I don't think
    -- it should be there.  Can you get rid of it?
    corolla-unique : {i : I} (c : γ P i) (w : W i)
      → (is-c : is-contr (node w))
      → (pth : node-type w (contr-center is-c) == (i , c))
      → corolla c == w 
    corolla-unique c (lf i) is-c pth = ⊥-elim (contr-center is-c)
    corolla-unique c (nd i (c' , δ)) is-c pth = ap corolla {!!} ∙ and-so

      where lem : (i , c') == (i , c)
            lem = (! (ap (λ x → node-type (nd i (c' , δ)) x) (contr-path is-c (inl unit)))) ∙ pth

            must-be-leaves : (p : ρ P i c') → δ p == lf (τ P i c' p)
            must-be-leaves p with δ p | inspect δ p
            must-be-leaves p | lf .(τ P i c' p) | ingraph e = idp
            must-be-leaves p | nd .(τ P i c' p) _ | ingraph e = ⊥-elim
              (inl≠inr unit no-no (contr-has-all-paths ⦃ is-c ⦄ (inl unit) (inr no-no))) 

              where no-no : Σ (ρ P i c') (node ∘ δ)
                    no-no = p , transport! node e (inl unit)

            and-so : corolla c' == nd i (c' , δ)
            and-so = ap (λ d → nd i (c' , d)) (λ= (λ p → ! (must-be-leaves p)))

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

    μ-fr : (i : I) (c : γ-fr i) (δ : (p : ρ-fr i c) → γ-fr (τ-fr i c p)) → γ-fr i
    μ-fr i (lf .i) δ = δ unit
    μ-fr i (nd .i (c , δ₀)) δ = nd i (c , λ p₀ → μ-fr (τ P i c p₀) (δ₀ p₀) (λ p₁ → δ (p₀ , p₁)))

    μρ-to-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
      → ρ-fr i (μ-fr i w δ)
    μρ-to-fr i (lf .i) δ (unit , p₁) = p₁
    μρ-to-fr i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) = p₀ , μρ-to-fr (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)

    μρ-from-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → ρ-fr i (μ-fr i w δ)
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p) (δ p))
    μρ-from-fr i (lf .i) δ p = unit , p
    μρ-from-fr i (nd .i (c , δ₀)) δ (p₀ , p₁) =
      let pp = μρ-from-fr (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
      in (p₀ , fst pp) , snd pp

    μρ-to-from-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → (p : ρ-fr i (μ-fr i w δ))
      → μρ-to-fr i w δ (μρ-from-fr i w δ p) == p
    μρ-to-from-fr i (lf .i) δ p = idp
    μρ-to-from-fr i (nd .i (c , δ₀)) δ (p₀ , p₁) = 
      let ih = μρ-to-from-fr (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
      in ap (λ p₂ → p₀ , p₂) ih

    μρ-from-to-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → (p : Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p)))
      → μρ-from-fr i w δ (μρ-to-fr i w δ p) == p
    μρ-from-to-fr i (lf .i) δ (unit , p₁) = idp
    μρ-from-to-fr i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) =
      let ih = μρ-from-to-fr (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)
          ρ-fr-δ x = ρ-fr (τ-fr (τ P i c (fst x)) (δ₀ (fst x)) (snd x)) (δ x)
      in pair= (pair= idp (fst= ih)) (↓-ap-in ρ-fr-δ (λ x → (p₀ , x)) (snd= ih))

    μρ-equiv-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
        ≃' ρ-fr i (μ-fr i w δ)
    μρ-equiv-fr i w δ =
      equiv' (μρ-to-fr i w δ) (μρ-from-fr i w δ)
             (μρ-to-from-fr i w δ) (μρ-from-to-fr i w δ)


  ZeroPoly : (I : Type₀) → Poly I
  γ  (ZeroPoly I) i = ⊥
  ρ (ZeroPoly I) i () 
  τ (ZeroPoly I) i () _
