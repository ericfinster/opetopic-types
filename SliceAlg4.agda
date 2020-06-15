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
  slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ (inl unit) = goal

    where open IdxUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
          open CnsUniqueIh i j c ν δ ε d' typ-d'=ν δ↓ ε↓
          open IdxIh i j c ν δ ε ϕ
          open CnsIh i j c ν δ ε ϕ
          open Helpers i j c ν δ ε d' typ-d'=ν


          what-is-the-type : (j , idp) , (d' , typ-d'=ν) == (j , idp) , (d' , typ-d'=ν)
          what-is-the-type = ap (λ x → Typ↓ Slc↓ (snd x) true)
                                (pair= (pair= idp (pb-pth (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓))
                                       (result (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓ ε↓' ε↓ ε-claim))

  -- Oh!  So the main lemma is that Typ↓ₛ ignores δ↓ and ε↓!  Okay, so now I *really* believe this is going
  -- to work.

  -- Typ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Idx (Slice M)} {σ : Cns (Slice M) f} 
  --   → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
  --   → (p : Pos (Slice M) σ) → Idx↓ₛ M↓ (Typ (Slice M) σ p)
  -- Typ↓ₛ M↓ (nd↓ {f↓ = f↓} σ↓ δ↓ ε↓) (inl unit) = f↓ , σ↓
  -- Typ↓ₛ M↓ (nd↓ σ↓ δ↓ ε↓) (inr (p , q)) = Typ↓ₛ M↓ (ε↓ p) q

    -- Typ↓ₚ : {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
    --   → {j : Idx↓ₚ i} (d : Cns↓ₚ j c)
    --   → (p : Pos (Pb M X) {f = i} c) → Idx↓ₚ (Typ (Pb M X) {f = i} c p)
    -- Typ↓ₚ (d , κ) p = Typ↓ M↓ d p , κ p 

          -- before-the-app : ((j , idp) , μ↓ M↓ d' (fst ∘ (λ p → δ↓' p , typ-δ↓'=ν' p)) , δ↓μ (λ p → δ↓' p , typ-δ↓'=ν' p)) ,
          --                     nd↓ (d' , typ-d'=ν) (λ p → (fst ∘ (λ p₁ → δ↓' p₁ , typ-δ↓'=ν' p₁)) p , typ-δ↓'=ν' p) ε↓'
          --                  ==
          --                  ((j , idp) , μ↓ M↓ d' (fst ∘ δ↓) , δ↓μ δ↓) ,
          --                     nd↓ (d' , typ-d'=ν) (λ p → (fst ∘ δ↓) p , snd (δ↓ p)) ε↓
          -- before-the-app = (pair= (pair= idp (pb-pth (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓))
          --                              (result (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓ ε↓' ε↓ ε-claim))

          -- Exactly.

          -- pb-pth : Path {A = Cns↓ Plbk↓ (j , idp) (μ M c (fst ∘ δ) , δμ)}
          --             (μ↓ M↓ d (fst ∘ δ↓₀) , δ↓μ δ↓₀)
          --             (μ↓ M↓ d (fst ∘ δ↓₁) , δ↓μ δ↓₁)
          -- pb-pth = ap (λ x → μ↓ M↓ d (fst ∘ x) , δ↓μ x) (λ= δ-eq)


          goal : idp == ap (λ x → Typ↓ Slc↓ (snd x) true)
                          (pair= (pair= idp (pb-pth (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓))
                                 (result (λ p → δ↓' p , typ-δ↓'=ν' p) δ↓ δ↓'=δ↓ ε↓' ε↓ ε-claim)) ∙ idp
          goal = {!!} 


  -- slc-idx ((i , j) , ._ , ._) (lf .(i , j)) ϕ =
  --   (j , idp) , (η↓ M↓ j , cst idp)
  -- slc-idx ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ =
  --   let open IdxIh i j c ν δ ε ϕ
  --   in (j' , j'=j) , (μ↓ M↓ d δ↓' , typ-μ↓=ν')

  -- slc-cns ((i , j) , ._ , ._) (lf .(i , j)) ϕ = lf↓ (j , idp)
  -- slc-cns ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ =
  --   let open IdxIh i j c ν δ ε ϕ
  --       open CnsIh i j c ν δ ε ϕ 
  --   in nd↓ (d , typ-d=ν) (λ p → δ↓' p , λ q → typ-δ↓'=ν' p q) ε↓'

  -- slc-typ ((i , j) , ._ , ._) (lf .(i , j)) ϕ () 
  -- slc-typ ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ true = idp
  -- slc-typ ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ (inr (p , q)) =
  --   let open IdxIh i j c ν δ ε ϕ 
  --       open CnsIh i j c ν δ ε ϕ
  --   in typ-trans-inv Slc Slc↓ (idx-ih-coh p) (cns-ih p) q ∙
  --      slc-typ ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p) q

  slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d' , typ-d'=ν) δ↓ ε↓ ∣ idp ⟧ (inr (p , q)) = {!!}
  
