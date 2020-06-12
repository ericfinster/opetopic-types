{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Lemmas

module Experiments where

  module ContrCenter (M : 𝕄) (M↓ : 𝕄↓ M) where

    open SliceOver M M↓ public

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
          ctl p q = typ-trans-inv M M↓ (trnspth p) (d' p) q ∙ (pth p q)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ↓' p = transport (C p) (trnspth p) (d' p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in ctl p q
      in (j' , j=j') , μ↓ M↓ d δ↓' , ev

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
          ctl p q = typ-trans-inv M M↓ (trnspth p) (d' p) q ∙ (pth p q)
          C p x = Cns↓ M↓ x (fst (δ p))
          δ↓' p = transport (C p) (trnspth p) (d' p)
          ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
                      q = μ-pos-snd M c (fst ∘ δ) pq
                  in ctl p q 

          cns-ih p = slc-cns ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          P p x = Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)) x (ε p)

          typ-pth p = (slc-idx-lem (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
                                 (trnspth p) (pth-alg₀ (jih=ν p) (typ-d=ν p)) idp
                                 (λ q → pth-alg₁ (pth p q) (typ-trans-inv M M↓ (trnspth p) (d' p) q)))
                                 
          ε↓' p = transport (P p) (typ-pth p) (cns-ih p)
  
          goal : Cns↓ Slc↓ ((j' , j=j') , (μ↓ M↓ d δ↓' , ev)) (nd (c , ν) δ ε)
          goal = nd↓ {M↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)} {σ = c , ν} {δ = δ}
                   {ε = ε} {f↓ = j' , j=j'} (d , typ-d=ν) (λ p → δ↓' p , λ q → ctl p q) ε↓'
          
      in goal

    slc-typ : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → (p : Pos Slc σ)
      → Typ↓ Slc↓ (slc-cns i σ ϕ) p == ϕ p 
    slc-typ ((i , j) , ._ , ._) (lf .(i , j)) ϕ () 
    slc-typ ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ true = idp
    slc-typ ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ (inr (p , q)) =
      let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
          ϕ' p q = ϕ (inr (p , q))
          idx-ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
          d' p = fst (snd (idx-ih p))
          jih=ν p = snd (fst (idx-ih p)) 
          pth p = snd (snd (idx-ih p))
          trnspth p = jih=ν p ∙ ! (typ-d=ν p)  
          typ-pth p = (slc-idx-lem (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
                                 (trnspth p) (pth-alg₀ (jih=ν p) (typ-d=ν p)) idp
                                 (λ q → pth-alg₁ (pth p q) (typ-trans-inv M M↓ (trnspth p) (d' p) q)))
          typ-ih p = slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
      in  typ-trans-inv Slc Slc↓ (typ-pth p) (slc-cns ((Typ M c p , ν p) , δ p) (ε p)
        (λ q₁ → ϕ (inr (p , q₁)))) q ∙ typ-ih p q

