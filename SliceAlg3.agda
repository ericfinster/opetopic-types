{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Lemmas
open import Algebras

module SliceAlg3 (M : 𝕄) (M↓ : 𝕄↓ M) where

  open SliceOver M M↓ 
  open import SliceAlg M M↓ 
  open import SliceAlg2 M M↓

  slc-cns-unique : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → (α : alg-comp Slc Slc↓ i σ ϕ)
    → slc-cns i σ ϕ == cns α [ (λ x → Cns↓ Slc↓ x σ) ↓ slc-idx-unique i σ ϕ α ]

  module CnsUniqueIh (i : Idx M) (j : Idx↓ M↓ i)
                     (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
                     (δ : (p : Pos Plbk {f = i , j} (c , ν)) → Cns Plbk (Typ Plbk {f = i , j} (c , ν) p))
                     (ε : (p : Pos Plbk {f = i , j} (c , ν)) → Cns Slc (Typ Plbk {f = i , j} (c , ν) p , δ p))
                     (d' : Cns↓ M↓ j c) (typ-d'=ν : (p : Pos M c) → Typ↓ M↓ d' p == ν p)
                     (δ↓ : (p : Pos Plbk {f = i , j} (c , ν)) → Cns↓ Plbk↓ (Typ↓ M↓ d' p , typ-d'=ν p) (δ p))
                     (ε↓ : (p : Pos Plbk {f = i , j} (c , ν)) → Cns↓ Slc↓ ((Typ↓ M↓ d' p , typ-d'=ν p) , δ↓ p) (ε p)) where


    open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓

    open IdxIh i j c ν δ ε ϕ
    open CnsIh i j c ν δ ε ϕ

    module _ (p : Pos M c) where

      by-defn : cns-ih p == ε↓' p [ PdFib p ↓ idx-ih-coh p ] 
      by-defn = from-transp (PdFib p) (idx-ih-coh p) idp

      cns-u-ih : cns-ih p == ε↓ p [ PdFib p ↓ slc-u-ih p ]
      cns-u-ih = slc-cns-unique ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p)) (α p) 

      ε-claim : ε↓' p == ε↓ p [ (λ x → Cns↓ Slc↓ ((Typ↓ M↓ d' p , typ-d'=ν p) , x) (ε p)) ↓ δ↓'=δ↓ p ]
      ε-claim = Σ-fst-triv-lem₁ {C = λ z → Cns↓ Slc↓ z (ε p)} {a = (Typ↓ M↓ d' p , typ-d'=ν p)}
        (idx-pth p) (contr-lemma p) (!ᵈ by-defn ∙ᵈ cns-u-ih)

    -- And clearly, for the second part, we lift the constructors and
    -- use the above claim + a bit of fixup related to funext.  So
    -- it's completely clear that we can get this, even if a bit
    -- tedious.
    
    goal : (nd↓ {f↓ = j , idp} (d' , typ-d'=ν) (λ p → δ↓' p , λ q → typ-δ↓'=ν' p q) ε↓')  
           == (nd↓ {f↓ = j , idp} (d' , typ-d'=ν) δ↓ ε↓) [ (λ x → Cns↓ Slc↓ x (nd (c , ν) δ ε)) ↓
                slc-idx-lem i j (μ M c (fst ∘ δ)) δμ idp idp
                (ap (μ↓ M↓ d') (λ= (λ p → fst= (δ↓'=δ↓ p)))) finally ]
    goal = {!!} 

  slc-cns-unique ((i , j) , ._ , ._) (lf .(i , j)) ._ ⟦ (._ , idp) , ._ , ._ ∣ lf↓ (.j , .idp) ∣ idp ⟧ = idp
  slc-cns-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ =
    let open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open CnsUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
    in goal 




