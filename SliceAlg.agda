{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import SliceLemmas

module SliceAlg (M : 𝕄) (M↓ : 𝕄↓ M) where

  open SliceOver M M↓ 

  slc-idx : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → Idx↓ Slc↓ i

  slc-cns : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → Cns↓ Slc↓ (slc-idx i σ ϕ) σ

  slc-typ : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → (p : Pos Slc σ)
    → Typ↓ Slc↓ (slc-cns i σ ϕ) p == ϕ p 

  module IdxIh (i : Idx M) (j : Idx↓ M↓ i)
               (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
               (δ : (p : Pos Plbk {i = i , j} (c , ν)) → Cns Plbk (Typ Plbk {i = i , j} (c , ν) p))
               (ε : (p : Pos Plbk {i = i , j} (c , ν)) → Cns Slc (Typ Plbk {i = i , j} (c , ν) p , δ p))
               (ϕ : (p : Pos Slc (nd {i = i , j} (c , ν) δ ε)) → Idx↓ Slc↓ (Typ Slc (nd {i = i , j} (c , ν) δ ε) p)) where

    j' = fst (fst (ϕ (inl unit)))
    j'=j = snd (fst (ϕ (inl unit)))
    d = fst (snd (ϕ (inl unit)))
    typ-d=ν = snd (snd (ϕ (inl unit)))
    
    ϕ' : (p : Pos M c) (q : Pos Slc (ε p)) → Idx↓ Slc↓ (Typ Slc (ε p) q)
    ϕ' p q = ϕ (inr (p , q))

    module _ (p : Pos M c) where

      ν' = snd (δ p)
      
      idx-ih : Idx↓ Slc↓ ((Typ M c p , ν p) , δ p) 
      idx-ih = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)

      k : Idx↓ M↓ (Typ M c p)
      k = fst (fst idx-ih)

      e : Cns↓ M↓ k (fst (δ p))
      e = fst (snd idx-ih) 

      k=νp : k == ν p
      k=νp = snd (fst idx-ih) 

      typ-e=ν' : (q : Pos M (fst (δ p))) → Typ↓ M↓ e q == ν' q
      typ-e=ν' = snd (snd idx-ih) 

      CnsFib : Idx↓ M↓ (Typ M c p) → Set
      CnsFib x = Cns↓ M↓ x (fst (δ p)) 

      k=typ-dp : k == Typ↓ M↓ d p
      k=typ-dp = k=νp ∙ ! (typ-d=ν p) 

      δ↓' = transport CnsFib k=typ-dp e

      typ-δ↓'=ν' : (q : Pos M (fst (δ p))) → Typ↓ M↓ δ↓' q == ν' q
      typ-δ↓'=ν' q = typ-trans-inv M M↓ k=typ-dp e q ∙ typ-e=ν' q 
      
    module _ (pq : Pos M (μ M c (fst ∘ δ))) where

      μfst : Pos M c
      μfst = μ-pos-fst M c (fst ∘ δ) pq

      μsnd : Pos M (fst (δ μfst))
      μsnd = μ-pos-snd M c (fst ∘ δ) pq
      
      typ-μ↓=ν' : Typ↓ M↓ (δ↓' μfst) μsnd == ν' μfst μsnd
      typ-μ↓=ν' = typ-δ↓'=ν' μfst μsnd 

  module CnsIh (i : Idx M) (j : Idx↓ M↓ i)
               (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
               (δ : (p : Pos Plbk {i = i , j} (c , ν)) → Cns Plbk (Typ Plbk {i = i , j} (c , ν) p))
               (ε : (p : Pos Plbk {i = i , j} (c , ν)) → Cns Slc (Typ Plbk {i = i , j} (c , ν) p , δ p))
               (ϕ : (p : Pos Slc (nd {i = i , j} (c , ν) δ ε)) → Idx↓ Slc↓ (Typ Slc (nd {i = i , j} (c , ν) δ ε) p)) where

    open IdxIh i j c ν δ ε ϕ 

    module _ (p : Pos M c) where

      cns-ih : Cns↓ Slc↓ (idx-ih p) (ε p)  
      cns-ih = slc-cns ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)

      PdFib : Idx↓ Slc↓ ((Typ M c p , ν p) , δ p) → Set
      PdFib x = Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)) x (ε p) 
  
      idx-ih-coh : idx-ih p == ((Typ↓ M↓ d p , typ-d=ν p) , (δ↓' p , typ-δ↓'=ν' p))
      idx-ih-coh = slc-idx-lem (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
                     (k=typ-dp p) (pth-alg₀ (k=νp p) (typ-d=ν p)) idp
                     (λ q → pth-alg₁ (typ-e=ν' p q) (typ-trans-inv M M↓ (k=typ-dp p) (e p) q))

      ε↓' : Cns↓ Slc↓ ((Typ↓ M↓ d p , typ-d=ν p) , (δ↓' p , typ-δ↓'=ν' p)) (ε p)
      ε↓' = transport PdFib idx-ih-coh cns-ih

  slc-idx ((i , j) , ._ , ._) (lf .(i , j)) ϕ =
    (j , idp) , (η↓ M↓ j , cst idp)
  slc-idx ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ =
    let open IdxIh i j c ν δ ε ϕ
    in (j' , j'=j) , (μ↓ M↓ d δ↓' , typ-μ↓=ν')

  slc-cns ((i , j) , ._ , ._) (lf .(i , j)) ϕ = lf↓ (j , idp)
  slc-cns ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ =
    let open IdxIh i j c ν δ ε ϕ
        open CnsIh i j c ν δ ε ϕ 
    in nd↓ (d , typ-d=ν) (λ p → δ↓' p , λ q → typ-δ↓'=ν' p q) ε↓'

  slc-typ ((i , j) , ._ , ._) (lf .(i , j)) ϕ () 
  slc-typ ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ true = idp
  slc-typ ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ (inr (p , q)) =
    let open IdxIh i j c ν δ ε ϕ 
        open CnsIh i j c ν δ ε ϕ
    in typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
       slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q

