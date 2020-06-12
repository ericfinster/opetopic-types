{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import Lemmas
open import Algebras
open import Experiments

module Experiments2 where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    open ContrCenter M M↓

    slc-idx-unique : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → (α : alg-comp Slc Slc↓ i σ ϕ)
      → slc-idx i σ ϕ == idx α

    slc-idx-unique-coh : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → (α : alg-comp Slc Slc↓ i σ ϕ)
      → snd (fst (slc-idx i σ ϕ)) ∙ ! (snd (fst (idx α))) == 
        fst= (fst= (slc-idx-unique i σ ϕ α))

    -- Right.  I suspect we will also need this guy asserting that
    -- the proof that the triangle commutes *is* the proof given
    -- by showing that it is the composition.
    slc-idx-unique-coh₁ : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → (α : alg-comp Slc Slc↓ i σ ϕ)
      → ↓-idf=cst-in {a = snd (fst i)} {p = (ap fst (ap fst (slc-idx-unique i σ ϕ α)))}
                     {u = (snd (fst (slc-idx i σ ϕ)))} {v = (snd (fst (idx α)))}
                     (rotate (snd (fst (slc-idx i σ ϕ))) (snd (fst (idx α)))
                             (fst= (fst= (slc-idx-unique i σ ϕ α))) (slc-idx-unique-coh i σ ϕ α)) ==
        snd= (fst= (slc-idx-unique i σ ϕ α))
        
    slc-idx-unique = {!!} 
    slc-idx-unique-coh = {!!} 
    slc-idx-unique-coh₁ = {!!} 

    -- slc-idx-unique ((i , j) , ._ , ._) (lf .(i , j)) ._ ⟦ (._ , idp) , ._ , ._ ∣ lf↓ (.j , .idp) ∣ idp ⟧ = idp
    -- slc-idx-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d , typ-d=ν) δ↓ ε↓ ∣ idp ⟧ =
    --   let idx-ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))
    --       cns-ih p = slc-cns ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))
    --       typ-ih p = slc-typ ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))
    --       d' p = fst (snd (idx-ih p))
    --       jih=ν p = snd (fst (idx-ih p)) 
    --       pth p = snd (snd (idx-ih p))
    --       trnspth p = jih=ν p ∙ ! (typ-d=ν p)  
    --       ctl p q = typ-trans-inv M M↓ (trnspth p) (d' p) q ∙ (pth p q)
    --       C p x = Cns↓ M↓ x (fst (δ p))
    --       δ↓' p = transport (C p) (trnspth p) (d' p)
    --       ev pq = let p = μ-pos-fst M c (fst ∘ δ) pq
    --                   q = μ-pos-snd M c (fst ∘ δ) pq
    --               in ctl p q

    --       P p x = Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)) x (ε p)

    --       typ-pth p = (slc-idx-lem (Typ M c p) (ν p) (fst (δ p)) (snd (δ p))
    --                              (trnspth p) (pth-alg₀ (jih=ν p) (typ-d=ν p)) idp
    --                              (λ q → pth-alg₁ (pth p q) (typ-trans-inv M M↓ (trnspth p) (d' p) q)))
                                 
    --       ε↓' p = transport (P p) (typ-pth p) (cns-ih p)

    --       typ' p q = typ-trans-inv Slc Slc↓ (typ-pth p) (slc-cns ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))) q ∙ typ-ih p q

    --       -- Okay!  So we can produce an inductive hypothesis.
    --       α' : (p : Pos M c) → alg-comp Slc Slc↓ ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p))
    --       α' p = ⟦ ((Typ↓ M↓ d p , typ-d=ν p) , δ↓ p) ∣ ε↓ p ∣ idp ⟧ 

    --       slc-u-ih p = slc-idx-unique ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p)) (α' p)
    --       slc-u-coh p = slc-idx-unique-coh ((Typ M c p , ν p) , δ p) (ε p) (Typ↓ Slc↓ (ε↓ p)) (α' p)
          
    --       lem₀ : (p : Pos M c) → δ↓' p == fst (δ↓ p)
    --       lem₀ p = ap (λ x → transport (C p) x (d' p)) (slc-u-coh p) ∙
    --               (to-transp (↓-ap-in (C p) fst (↓-Σ-fst (snd= (slc-u-ih p))))) 

    --       lem₁ : (pq : Pos M (μ M c (fst ∘ δ))) → ev pq ==
    --         ap (λ x → Typ↓ M↓ x pq) (ap (μ↓ M↓ d) (λ= lem₀)) ∙
    --         snd (δ↓ (μ-pos-fst M c (λ p → fst (δ p)) pq)) (μ-pos-snd M c (λ p → fst (δ p)) pq)
    --       lem₁ pq = {!!}
    --       -- ↓-Pb-out (snd= (slc-u-ih ((μ-pos-fst M c (λ p → fst (δ p)) pq)))) (μ-pos-snd M c (λ p → fst (δ p)) pq)

    --   in slc-idx-lem i j (μ M c (fst ∘ δ)) (λ pq → snd (δ (μ-pos-fst M c (fst ∘ δ) pq)) (μ-pos-snd M c (fst ∘ δ) pq))
    --        idp idp (ap (μ↓ M↓ d) (λ= lem₀)) lem₁

    -- -- Okay, bingo.  This *can* be completed in finite time....
    -- slc-idx-unique-coh ((i , j) , ._ , ._) (lf .(i , j)) ._ ⟦ (._ , idp) , ._ , ._ ∣ lf↓ (.j , .idp) ∣ idp ⟧ = idp
    -- slc-idx-unique-coh ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d , typ-d=ν) δ↓ ε↓ ∣ idp ⟧ = {!!}
    --   -- ! (slc-idx-lem-coh i j (μ M c (fst ∘ δ)) (λ pq → snd (δ (μ-pos-fst M c (fst ∘ δ) pq)) (μ-pos-snd M c (fst ∘ δ) pq)) idp idp {!!} {!!}) 

    -- slc-cns-unique : (i : Idx Slc) (σ : Cns Slc i)
    --   → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    --   → (α : alg-comp Slc Slc↓ i σ ϕ)
    --   → slc-cns i σ ϕ == cns α [ (λ x → Cns↓ Slc↓ x σ) ↓ slc-idx-unique i σ ϕ α ]
    -- slc-cns-unique ((i , j) , ._ , ._) (lf .(i , j)) ._ ⟦ (._ , idp) , ._ , ._ ∣ lf↓ (.j , .idp) ∣ idp ⟧ = idp
    -- slc-cns-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d , typ-d=ν) δ↓ ε↓ ∣ idp ⟧ = {!!} 

    -- slc-typ-unique : (i : Idx Slc) (σ : Cns Slc i)
    --   → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
    --   → (α : alg-comp Slc Slc↓ i σ ϕ)
    --   → (p : Pos Slc σ)
    --   → slc-typ i σ ϕ p == app= (typ α) p [ (λ ic → Typ↓ Slc↓ (snd ic) p == ϕ p ) ↓
    --                                         pair= (slc-idx-unique i σ ϕ α) (slc-cns-unique i σ ϕ α) ]
    -- slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d , typ-d=ν) δ↓ ε↓ ∣ idp ⟧ (inl unit) = {!!}
    -- slc-typ-unique ((i , j) , ._ , ._) (nd (c , ν) δ ε) ._ ⟦ (.j , idp) , ._ , ._ ∣ nd↓ (d , typ-d=ν) δ↓ ε↓ ∣ idp ⟧ (inr (p , q)) = {!!}


