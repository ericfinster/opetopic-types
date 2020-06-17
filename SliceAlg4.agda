{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Lemmas
open import Algebras

module SliceAlg4 (M : 𝕄) (M↓ : 𝕄↓ M) where

  open SliceOver M M↓ 
  open import SliceAlg M M↓ 
  open import SliceAlg2 M M↓
  open import SliceAlg3 M M↓

  slc-typ-unique : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → (α : alg-comp Slc Slc↓ i σ ϕ)
    → (p : Pos Slc σ)
    → slc-typ i σ ϕ p == ap (λ x → Typ↓ Slc↓ (snd x) p) (pair= (slc-idx-unique i σ ϕ α) (slc-cns-unique i σ ϕ α)) ∙ (app= (typ α) p)
  slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ (inl unit) = 
    let open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open CnsUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open IdxIh i j c ν δ ε ϕ
        open CnsIh i j c ν δ ε ϕ
        open Helpers i j c ν δ ε d' typ-d'=ν
    in slc-typ-cst (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ ε↓' ε↓ (λ= δ↓'=δ↓)
         (λ=ε↓ (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓ ε↓' ε↓ ε↓'=ε↓) 

  slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ (inr (p , q)) = goal

    where open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
          open CnsUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
          open IdxIh i j c ν δ ε ϕ
          open CnsIh i j c ν δ ε ϕ
          open Helpers i j c ν δ ε d' typ-d'=ν


          typ-u-ih : slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q
            == ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)) ∙ idp 
          typ-u-ih = slc-typ-unique ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p)) (α p) q

          isp = idx-slc-slc-pth (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ ε↓' ε↓
                  (λ= δ↓'=δ↓) (λ=ε↓ (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓ ε↓' ε↓ ε↓'=ε↓)

      -- idx-ih-coh : idx-ih p == ((Typ↓ M↓ d p , typ-d=ν p) , (δ↓' p , typ-δ↓'=ν' p))                             
      -- idx-ih-coh = slc-idx-lem (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
      --                (k=typ-dp p) (pth-alg₀ (k=νp p) (typ-d=ν p)) idp
      --                (λ q → pth-alg₁ (typ-e=ν' p q) (typ-trans-inv M M↓ (k=typ-dp p) (e p) q))

          suffices : typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙ 
                     ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p))
                     == ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp
          suffices = {!idx-ih p == idx (α p)!} 
          
          goal : typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
                 slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q
                 == ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp ∙ idp
          goal = {!!} 

        -- typ-trans-inv : (M : 𝕄) (M↓ : 𝕄↓ M)
        --   → {i : Idx M} {c : Cns M i}
        --   → {j j' : Idx↓ M↓ i} (e : j == j')
        --   → (d : Cns↓ M↓ j c) (p : Pos M c)
        --   → Typ↓ M↓ (transport (λ x → Cns↓ M↓ x c) e d) p == Typ↓ M↓ d p
        -- typ-trans-inv M M↓ idp d p = idp

      -- α : alg-comp Slc Slc↓ ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))
      -- α = ⟦ ((Typ↓ M↓ d p , typ-d=ν p) , δ↓ p) ∣ ε↓ p ∣ idp ⟧
