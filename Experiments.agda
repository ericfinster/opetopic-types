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
          idx-ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          arg p = fst (snd (idx-ih p))
          wit p = snd (fst (idx-ih p)) ∙ ! (typ-d=ν p)
          pth p q = snd (snd (idx-ih p)) q
          ctl p q = cns-trans-lem (wit p) (arg p) q ∙ (pth p q)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ' p = transport (C p) (wit p) (arg p)
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
          arg p = fst (snd (idx-ih p))
          wit p = snd (fst (idx-ih p)) ∙ ! (typ-d=ν p)
          pth p q = snd (snd (idx-ih p)) q
          ctl p q = cns-trans-lem (wit p) (arg p) q ∙ (pth p q)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ' p = transport (C p) (wit p) (arg p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in cns-trans-lem (wit p) (arg p) q ∙ (pth p q)


          cns-ih p = slc-cns ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          P p x = Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)) x (ε p)

          lemma : (p : Posₚ M (Idx↓ M↓) {f = i , j} (c , ν))
            → idx-ih p == Typ↓ₚ M↓ (Idx↓ M↓) (λ i j k → j == k) {j = (j' , j=j')} (d , typ-d=ν) p , δ' p , λ q → ctl p q
          lemma p = {!!} 

          ε' p = transport (P p) (lemma p) (cns-ih p)

          goal : Cns↓ Slc↓ ((j' , j=j') , (μ↓ M↓ d δ' , ev)) (nd (c , ν) δ ε)
          goal = nd↓ {M↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)} {σ = c , ν} {δ = δ}
                   {ε = ε} {f↓ = j' , j=j'} (d , typ-d=ν) (λ p → δ' p , λ q → ctl p q) ε'
          
      in goal


-- goal: Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ j₁ k → j₁ == k))
--       (Typ↓ₚ M↓ (λ z → Idx↓ M↓ z) (λ z z₁ i₁ → z₁ == i₁)
--        (snd (ϕ (inl tt))) p
--        ,
--        transport (λ x → Cns↓ M↓ x (fst (δ p)))
--        (snd
--         (fst
--          (slc-idx ((Typ M c p , ν p) , δ p) (ε p) (λ q → ϕ (inr (p , q)))))
--         ∙ ! (snd (snd (ϕ true)) p))
--        (fst
--         (snd
--          (slc-idx ((Typ M c p , ν p) , δ p) (ε p) (λ q → ϕ (inr (p , q))))))
--        ,
--        (λ q →
--           cns-trans-lem
--           (snd
--            (fst
--             (slc-idx ((Typ M c p , ν p) , δ p) (ε p)
--              (λ q₁ → ϕ (inr (p , q₁)))))
--            ∙ ! (snd (snd (ϕ true)) p))
--           (fst
--            (snd
--             (slc-idx ((Typ M c p , ν p) , δ p) (ε p)
--              (λ q₁ → ϕ (inr (p , q₁))))))
--           q
--           ∙
--           snd
--           (snd
--            (slc-idx ((Typ M c p , ν p) , δ p) (ε p)
--             (λ q₁ → ϕ (inr (p , q₁)))))
--           q))
--       (ε p)
-- Have: Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ p₁ → _==_))
--       (fst
--        (slc-idx ((Typ M c p , ν p) , δ p) (ε p) (λ q → ϕ (inr (p , q))))
--        ,
--        snd
--        (slc-idx ((Typ M c p , ν p) , δ p) (ε p) (λ q → ϕ (inr (p , q)))))
--       (ε p)



    slc-typ : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Typ↓ Slc↓ (slc-cns i σ ϕ) == ϕ
    slc-typ ((i , j) , ._ , ._) (lf .(i , j)) ϕ = λ= (λ { () })
    slc-typ ((i , j) , ._ , ._) (nd σ δ ε) ϕ = {!!}



