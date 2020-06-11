{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType

module Experiments where

  -- Here's my working definition of the opetopic type
  -- determined by a monad over.
  OverToOpetopicType : (M : 𝕄) (M↓ : 𝕄↓ M) → OpetopicType M
  Ob (OverToOpetopicType M M↓) = Idx↓ M↓ 
  Hom (OverToOpetopicType M M↓) =
    OverToOpetopicType (Slice (Pb M (Idx↓ M↓)))
                       (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)))

  -- This should be a characterization of those monads which
  -- arise as the slice construction of an algebra.
  is-algebraic : (M : 𝕄) (M↓ : 𝕄↓ M) → Set
  is-algebraic M M↓ = (i : Idx M) (c : Cns M i)
    → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
    → is-contr (Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))) 

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    record alg-comp (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) : Set where
      constructor ⟦_∣_∣_⟧
      field
        idx : Idx↓ M↓ i 
        cns : Cns↓ M↓ idx c
        typ : Typ↓ M↓ cns == ν

    is-alg : Set
    is-alg = (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (alg-comp i c ν) 

  open alg-comp

  pth-alg₀ : ∀ {ℓ} {A : Set ℓ} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₁) (q : a₂ == a₁) 
    → (p ∙ ! q) ∙ q == p
  pth-alg₀ idp idp = idp

  pth-alg₁ : ∀ {ℓ} {A : Set ℓ} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₂) (q : a₁ == a₀) 
    → p == (! q ∙ idp) ∙ q ∙ p
  pth-alg₁ idp idp = idp 

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    Slc : 𝕄
    Slc = Slice (Pb M (Idx↓ M↓))

    Slc↓ : 𝕄↓ Slc
    Slc↓ = Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k))

    -- Lemma about transporting in constructors
    cns-trans-lem : {i : Idx M} {c : Cns M i}
      → {j j' : Idx↓ M↓ i} (e : j == j')
      → (d : Cns↓ M↓ j c) (p : Pos M c)
      → Typ↓ M↓ (transport (λ x → Cns↓ M↓ x c) e d) p == Typ↓ M↓ d p
    cns-trans-lem idp d p = idp

    -- Great.  So this isolates exactly what we need to
    -- prove below.  It's possible that the hypotheses
    -- can be jumbled around a bit to get better definitional
    -- behavior....
    slc-idx-lem : (i : Idx M) (j : Idx↓ M↓ i)
      → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j₀ : Idx↓ M↓ i} {e₀ : j₀ == j}
      → {d₀ : Cns↓ M↓ j₀ c} {α₀ : (p : Pos M c) → Typ↓ M↓ d₀ p == ν p}
      → {j₁ : Idx↓ M↓ i} {e₁ : j₁ == j}
      → {d₁ : Cns↓ M↓ j₁ c} {α₁ : (p : Pos M c) → Typ↓ M↓ d₁ p == ν p}
      → (q : j₀ == j₁) (r : q ∙ e₁ == e₀)
      → (s : transport (λ x → Cns↓ M↓ x c) q d₀ == d₁)
      → (t : (p : Pos M c) → α₀ p == (! (cns-trans-lem q d₀ p) ∙ ap (λ x → Typ↓ M↓ x p) s) ∙ α₁ p)
      → Path {A = Idx↓ Slc↓ ((i , j) , c , ν)}
        ((j₀ , e₀) , (d₀ , α₀)) ((j₁ , e₁) , (d₁ , α₁)) 
    slc-idx-lem i j c ν idp idp idp t =
      pair= idp (pair= idp (λ= t))

    slc-idx : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Idx↓ Slc↓ i
    slc-idx ((i , j) , ._ , ._) (lf .(i , j)) ϕ = (j , idp) , (η↓ M↓ j , cst idp)
    slc-idx ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ = 
      let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
          ϕ' p q = ϕ (inr (p , q))
          idx-ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          d' p = fst (snd (idx-ih p))
          jih=ν p = snd (fst (idx-ih p)) 
          pth p = snd (snd (idx-ih p))
          trnspth p = jih=ν p ∙ ! (typ-d=ν p)  
          ctl p q = cns-trans-lem (trnspth p) (d' p) q ∙ (pth p q)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ' p = transport (C p) (trnspth p) (d' p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in ctl p q
      in (j' , j=j') , μ↓ M↓ d δ' , ev

    slc-cns : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Cns↓ Slc↓ (slc-idx i σ ϕ) σ
    slc-cns ((i , j) , ._ , ._) (lf .(i , j)) ϕ = lf↓ (j , idp)
    slc-cns ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ = 
      let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
          ϕ' p q = ϕ (inr (p , q))
          idx-ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          d' p = fst (snd (idx-ih p))
          jih=ν p = snd (fst (idx-ih p)) 
          pth p = snd (snd (idx-ih p))
          trnspth p = jih=ν p ∙ ! (typ-d=ν p)  
          ctl p q = cns-trans-lem (trnspth p) (d' p) q ∙ (pth p q)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ' p = transport (C p) (trnspth p) (d' p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in ctl p q 

          cns-ih p = slc-cns ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          P p x = Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)) x (ε p)

          ε' p = transport (P p) (slc-idx-lem (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
                                 (trnspth p) (pth-alg₀ (jih=ν p) (typ-d=ν p)) idp
                                 (λ q → pth-alg₁ (pth p q) (cns-trans-lem (trnspth p) (d' p) q)  ))
                           (cns-ih p)
  
          goal : Cns↓ Slc↓ ((j' , j=j') , (μ↓ M↓ d δ' , ev)) (nd (c , ν) δ ε)
          goal = nd↓ {M↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)} {σ = c , ν} {δ = δ}
                   {ε = ε} {f↓ = j' , j=j'} (d , typ-d=ν) (λ p → δ' p , λ q → ctl p q) ε'
          
      in goal

    slc-typ : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → (p : Pos Slc σ)
      → Typ↓ Slc↓ (slc-cns i σ ϕ) p == ϕ p 
    slc-typ ((i , j) , ._ , ._) (lf .(i , j)) ϕ () 
    slc-typ ((i , j) , ._ , ._) (nd σ δ ε) ϕ true = idp
    slc-typ ((i , j) , ._ , ._) (nd σ δ ε) ϕ (inr (p , q)) = {!!}

    -- And then this looks like it's essentially just commuting
    -- a transport and the induction hypothesis....


    -- Oh, wow.  The fact that the first one came out to be idp
    -- is super reassuring.  For the second, we'll have to finish
    -- up the lemmas above.
