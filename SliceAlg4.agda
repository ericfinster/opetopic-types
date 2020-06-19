{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import SliceLemmas
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

          goal = typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
                 slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q
                   =⟨ ap (λ z → typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙ z) typ-u-ih ⟩ 
                 typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
                 (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)) ∙ idp)
                   =⟨ ap (λ z → typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙ z)
                        (∙-unit-r (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)))) ⟩ 
                 typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
                 (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (idx-u-ih p) (cns-u-ih p)))
                   =⟨ the-lemma (idx-ih-coh p) (cns-ih p) q (idx-u-ih p) (ε↓ p) (cns-u-ih p) (contr-lemma p) ⟩
                 (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (δ↓'=δ↓ p) (ε↓'=ε↓ p)))
                   -- Well, it works, but this step here makes the typechecking take
                   -- a full couple minutes.  Perhaps explicit the arguments or something?
                   =⟨ ap (λ z → ap (λ x → Typ↓ₛ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) (snd x) q) z)
                          (app=-pair δ↓'=δ↓ ε↓'=ε↓ p) ⟩
                   -- Ooops!  I changed the definition of λ=↓ and now this step fails.  Have
                   -- to go back to the previous version.
                 (ap (λ x → Typ↓ Slc↓ (snd x) q)
                   (pair= (app= (λ= δ↓'=δ↓) p) (app=↓ (λ= δ↓'=δ↓) (λ=↓ δ↓'=δ↓ ε↓'=ε↓) p)))
                   =⟨ slc-typ-cst-coh (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ ε↓' ε↓
                  (λ= δ↓'=δ↓) (λ=↓ δ↓'=δ↓ ε↓'=ε↓) p q ⟩ 
                 ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp
                   =⟨ ! (∙-unit-r (ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp)) ⟩ 
                 ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) isp ∙ idp =∎

  --
  --  The main theorem
  --

  slc-algebraic : is-algebraic Slc Slc↓
  slc-algebraic i c ν = has-level-in (ctr , unique) 

    where ctr : alg-comp Slc Slc↓ i c ν
          ctr = ⟦ slc-idx i c ν ∣ slc-cns i c ν ∣ λ= (slc-typ i c ν) ⟧
          
          unique : (α : alg-comp Slc Slc↓ i c ν) → ctr == α
          unique α = alg-comp-= Slc Slc↓ i c ν
                     (slc-idx-unique i c ν α)
                     (slc-cns-unique i c ν α)
                     (λ p → app=-β (slc-typ i c ν) p ∙ slc-typ-unique i c ν α p)
