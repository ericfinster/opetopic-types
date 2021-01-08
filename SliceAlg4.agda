{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import IdentityMonad
open import Pb
open import OpetopicType
open import SliceLemmas

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
    in slc-typ-cst (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ ε↓' ε↓ (λ= δ↓'=δ↓) (λ=↓ δ↓'=δ↓ ε↓'=ε↓)

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
                  (λ= δ↓'=δ↓) (λ=↓ δ↓'=δ↓ ε↓'=ε↓)

          lem = slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q
                  =⟨ typ-u-ih ⟩
                ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)) ∙ idp
                  =⟨ ∙-unit-r (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p))) ⟩
                ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)) =∎ 


          goal = typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
                   slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q

                   =⟨ lem |in-ctx (λ x → typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙ x) ⟩

                 typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
                 (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)))

                   =⟨ the-lemma (idx-ih-coh p) (cns-ih p) q (idx-u-ih p) (ε↓ p) (cns-u-ih p) (contr-lemma p) ⟩ 

                 ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (δ↓'=δ↓ p) (ε↓'=ε↓ p))

                   =⟨ ! (app=-pair δ↓'=δ↓ ε↓'=ε↓ p) |in-ctx (ap (λ x → Typ↓ Slc↓ (snd x) q)) ⟩

                 ap (λ x → Typ↓ Slc↓ (snd x) q)
                   (pair= (app= (λ= δ↓'=δ↓) p) (app=↓ (λ= δ↓'=δ↓) (λ=↓ δ↓'=δ↓ ε↓'=ε↓) p))
                   
                   =⟨ slc-typ-cst-coh (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ ε↓' ε↓
                      (λ= δ↓'=δ↓) (λ=↓ δ↓'=δ↓ ε↓'=ε↓) p q ⟩
                      
                 ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp
                 
                   =⟨ ! (∙-unit-r (ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp)) ⟩
                   
                 ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp ∙ idp =∎

