{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import IdentityMonad
open import Pb
open import OpetopicType
open import SliceLemmas

module SliceAlg2 (M : 𝕄) (M↓ : 𝕄↓ M) where

  open SliceOver M M↓ 
  open import SliceAlg M M↓ 

  slc-idx-unique : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → (α : alg-comp Slc Slc↓ i σ ϕ)
    → slc-idx i σ ϕ == idx α

  slc-idx-unique-coh : (i : Idx Slc) (σ : Cns Slc i)
    → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    → (α : alg-comp Slc Slc↓ i σ ϕ)
    → pair= (snd (fst (slc-idx i σ ϕ)) ∙ ! (snd (fst (idx α))))
            (↓-idf=cst-in (pth-alg₀ (snd (fst (slc-idx i σ ϕ))) (snd (fst (idx α)))))
      == fst= (slc-idx-unique i σ ϕ α)

  module IdxUniqueIh (i : Idx M) (j : Idx↓ M↓ i)
                     (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
                     (δ : (p : Pos Plbk {i = i , j} (c , ν)) → Cns Plbk (Typ Plbk {i = i , j} (c , ν) p))
                     (ε : (p : Pos Plbk {i = i , j} (c , ν)) → Cns Slc (Typ Plbk {i = i , j} (c , ν) p , δ p))
                     (d' : Cns↓ M↓ j c) (typ-d'=ν : (p : Pos M c) → Typ↓ M↓ d' p == ν p)
                     (δ↓ : (p : Pos Plbk {i = i , j} (c , ν)) → Cns↓ Plbk↓ (Typ↓ M↓ d' p , typ-d'=ν p) (δ p))
                     (ε↓ : (p : Pos Plbk {i = i , j} (c , ν)) → Cns↓ Slc↓ ((Typ↓ M↓ d' p , typ-d'=ν p) , δ↓ p) (ε p)) where

    open Helpers i j c ν δ ε d' typ-d'=ν 

    idxslc↓ : Idx↓ Slc↓ ((i , j) , μ M c (fst ∘ δ) , λ p → snd (δ (μf p)) (μs p))
    idxslc↓ = (j , idp) , μ↓ M↓ d' (fst ∘ δ↓) , δ↓μ δ↓

    -- Note that by opening the Idx module with this definition, we
    -- get definitionally in what follows that:
    --
    -- j' := j, j'=j := idp, d := d', typ-d=ν = typ-d'=ν
    --
    -- Hence it would probably not be so bad to just have overlapping
    -- notation for these guys .... this explains why we didn't see
    -- that proof obligation and why we seem to only need to characterize
    -- δ↓ and ε↓ in terms of previous data.

    ϕ : (p : Pos Slc (nd {i = i , j} (c , ν) δ ε)) → Idx↓ Slc↓ (Typ Slc (nd {i = i , j} (c , ν) δ ε) p)
    ϕ = Typ↓ Slc↓ {i↓ = idxslc↓} (nd↓ {i↓ = j , idp} (d' , typ-d'=ν) δ↓ ε↓)

    open IdxIh i j c ν δ ε ϕ
    open CnsIh i j c ν δ ε ϕ
    
    module _ (p : Pos M c) where
    
      -- The inductive evidence for algebraic composition
      α : alg-comp Slc Slc↓ ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))
      α = ⟦ ((Typ↓ M↓ d p , typ-d=ν p) , δ↓ p) ∣ ε↓ p ∣ idp ⟧

      idx-u-ih : idx-ih p == idx α
      idx-u-ih = slc-idx-unique ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p)) α

      idx-pth : ((Typ↓ M↓ d p , typ-d=ν p) , (δ↓' p , typ-δ↓'=ν' p)) ==
                  ((Typ↓ M↓ d p , typ-d=ν p) , δ↓ p)
      idx-pth = ! (idx-ih-coh p) ∙ idx-u-ih  

      contr-lemma : fst= idx-pth == idp
      contr-lemma = fst= (! (idx-ih-coh p) ∙ idx-u-ih)
                         =⟨ fst=-comm (idx-ih-coh p) idx-u-ih ⟩
                    ! (fst= (idx-ih-coh p)) ∙ fst= idx-u-ih
                         =⟨ slc-idx-lem-coh (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
                               (k=typ-dp p) (pth-alg₀ (k=νp p) (typ-d=ν p)) idp
                               (λ q → pth-alg₁ (typ-e=ν' p q) (typ-trans-inv M M↓ (k=typ-dp p) (e p) q))
                            |in-ctx (λ x → ! x ∙ fst= idx-u-ih) ⟩
                    ! (pair= (k=typ-dp p) (↓-idf=cst-in (pth-alg₀ (k=νp p) (typ-d=ν p)))) ∙ fst= idx-u-ih
                         =⟨ ! (slc-idx-unique-coh ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p)) α) |in-ctx
                            (λ x → ! (pair= (k=typ-dp p) (↓-idf=cst-in (pth-alg₀ (k=νp p) (typ-d=ν p)))) ∙ x) ⟩
                    ! (pair= (k=typ-dp p) (↓-idf=cst-in (pth-alg₀ (k=νp p) (typ-d=ν p)))) ∙
                      (pair= (k=typ-dp p) (↓-idf=cst-in (pth-alg₀ (k=νp p) (typ-d=ν p))))
                         =⟨ !-inv-l (pair= (k=typ-dp p) (↓-idf=cst-in (pth-alg₀ (k=νp p) (typ-d=ν p)))) ⟩ 
                    idp =∎  

      δ↓'=δ↓ : (δ↓' p , typ-δ↓'=ν' p) == δ↓ p
      δ↓'=δ↓ = Σ-fst-triv-lem₀ {B = (λ x → Cns↓ Plbk↓ x (δ p))}
                     idx-pth contr-lemma

      -- transport (λ y → (δ↓' p , typ-δ↓'=ν' p) == (δ↓ p) [ (λ x → Cns↓ Plbk↓ x (δ p)) ↓ y ])
      --            contr-lemma (snd= idx-pth)  

  slc-idx-unique ((i , j) , ._ , ._) (lf .(i , j)) ._ ⟦ (._ , idp) , ._ , ._ ∣ lf↓ (.j , .idp) ∣ idp ⟧ = idp
  slc-idx-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ =
    let open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open IdxIh i j c ν δ ε ϕ
        open CnsIh i j c ν δ ε ϕ
        open Helpers i j c ν δ ε d' typ-d'=ν 
    in pair= idp (pb-pth (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓)

  slc-idx-unique-coh ((i , j) , ._ , ._) (lf .(i , j)) ._ ⟦ (._ , idp) , ._ , ._ ∣ lf↓ (.j , .idp) ∣ idp ⟧ = idp
  slc-idx-unique-coh ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ =
    let open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
        open IdxIh i j c ν δ ε ϕ
        open CnsIh i j c ν δ ε ϕ
        open Helpers i j c ν δ ε d' typ-d'=ν 
    in ! (fst=-β idp (pb-pth (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓))






