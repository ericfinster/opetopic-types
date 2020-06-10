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

    slc-idx : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Idx↓ Slc↓ i
    slc-idx ((i , j) , ._ , ._) (lf .(i , j)) ϕ = (j , idp) , (η↓ M↓ j , cst idp)
    slc-idx ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ = 
      let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
          ϕ' p q = ϕ (inr (p , q))
          ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          arg p = fst (snd (ih p))
          wit p = snd (fst (ih p)) ∙ ! (typ-d=ν p)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ' p = transport (C p) (wit p) (arg p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in cns-trans-lem (wit p) (arg p) q ∙ (snd (snd (ih p)) q)
      in (j' , j=j') , μ↓ M↓ d δ' , ev

    slc-cns : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Cns↓ Slc↓ (slc-idx i σ ϕ) σ
    slc-cns ((i , j) , ._ , ._) (lf .(i , j)) ϕ = lf↓ (j , idp)
    slc-cns ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ = 
      let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
          ϕ' p q = ϕ (inr (p , q))
          ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          arg p = fst (snd (ih p))
          wit p = snd (fst (ih p)) ∙ ! (typ-d=ν p)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ' p = transport (C p) (wit p) (arg p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in cns-trans-lem (wit p) (arg p) q ∙ (snd (snd (ih p)) q)
                  
          goal : Cns↓ Slc↓ ((j' , j=j') , (μ↓ M↓ d δ' , ev)) (nd (c , ν) δ ε)
          goal = {!nd↓ {M↓ = (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k))} {σ = c , ν} {δ = δ} {ε = ε} {f↓ = (j' , j=j')} (d , typ-d=ν) !}
          
      in goal


-- Have: (δ↓
--        : (p : Posₚ M (λ z → Idx↓ M↓ z) (c , ν)) →
--          Cns↓ₚ M↓ (λ z → Idx↓ M↓ z) (λ z z₁ i₁ → z₁ == i₁)
--          (Typ↓ M↓ (fst (snd (ϕ (inl tt)))) p , snd (snd (ϕ (inl tt))) p)
--          (δ p)) →
--       ((p : Posₚ M (λ z → Idx↓ M↓ z) (c , ν)) →
--        Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ j₁ k → j₁ == k))
--        (Typ↓ₚ M↓ (λ z → Idx↓ M↓ z) (λ z f↓ i₁ → f↓ == i₁)
--         (snd (ϕ (inl tt))) p
--         , δ↓ p)
--        (ε p)) →
--       Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ j₁ k → j₁ == k))
--       ((fst (fst (ϕ true)) , snd (fst (ϕ true))) ,
--        μ↓ (Pb↓ M↓ (Idx↓ M↓) (λ p j₁ k → j₁ == k))
--        (fst (snd (ϕ true)) , snd (snd (ϕ true))) δ↓)
--       (nd (c , ν) δ ε)


    -- nd↓ : {f : Idx M} {σ : Cns M f}
    --   → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
    --   → {ε : (p : Pos M σ) → Pd M (Typ M σ p , δ p)}
    --   → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
    --   → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
    --   → (ε↓ : (p : Pos M σ) → Pd↓ M↓ (Typ↓ M↓ σ↓ p , δ↓ p) (ε p))
    --   → Pd↓ M↓ (f↓ , μ↓ M↓ σ↓ δ↓) (nd σ δ ε) 



    slc-typ : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Typ↓ Slc↓ (slc-cns i σ ϕ) == ϕ
    slc-typ ((i , j) , ._ , ._) (lf .(i , j)) ϕ = λ= (λ { () })
    slc-typ ((i , j) , ._ , ._) (nd σ δ ε) ϕ = {!!}



