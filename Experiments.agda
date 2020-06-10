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

    slc-idx : (i : Idx Slc) (σ : Cns Slc i)
      → (ϕ : (p : Pos Slc σ) → Idx↓ Slc↓ (Typ Slc σ p))
      → Idx↓ Slc↓ i
    slc-idx ((i , j) , ._ , ._) (lf .(i , j)) ϕ = (j , idp) , (η↓ M↓ j , cst idp)
    slc-idx ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ = 
      let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
          ϕ' p q = ϕ (inr (p , q))
          ih p = slc-idx ((Typ M c p , ν p) , δ p) (ε p) (ϕ' p)
      in (j' , j=j') , μ↓ M↓ {δ = fst ∘ δ} d (λ p → {!fst (snd (ih p))!}) , {!!}

    -- conj : is-alg Slc Slc↓ 
    -- conj ((i , j) , ._ , ._) (lf .(i , j)) ϕ = has-level-in (ctr , unique)

    --   where ctr : alg-comp Slc Slc↓ ((i , j) , η M i , (λ _ → j)) (lf (i , j)) ϕ
    --         idx ctr = (j , idp) , (η↓ M↓ j , λ _ → idp)
    --         cns ctr = lf↓ {M↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)} (j , idp)
    --         typ ctr = λ= (λ { () })

    --         -- Bingo!  Now we see that it's exactly the ability to match on the
    --         -- slice constructor which fixes the second pair, as I had thought.
    --         unique : (ac : alg-comp Slc Slc↓ ((i , j) , η M i , (λ _ → j)) (lf (i , j)) ϕ) → ctr == ac
    --         unique ⟦ (.j , idp) , .(η↓ M↓ j) , .(λ _ → idp) ∣ lf↓ (.j , .idp) ∣ c ⟧ = {!!}

    -- conj ((i , j) , ._ , ._) (nd (c , ν) δ ε) ϕ =
    --   let ((j' , j=j') , (d , typ-d=ν)) = ϕ (inl unit)
    --   in has-level-in (ctr , {!d!})
  
    --   where ctr : alg-comp Slc Slc↓ ((i , j) , μ M c (λ p → fst (δ p)) ,
    --                                            (λ p → snd (δ (μ-pos-fst M c (λ p₁ → fst (δ p₁)) p))
    --                                                       (μ-pos-snd M c (λ p₁ → fst (δ p₁)) p))) (nd (c , ν) δ ε) ϕ
    --         idx ctr = (fst (fst (ϕ true)) , snd (fst (ϕ (inl unit)))) , (μ↓ M↓ (fst (snd (ϕ (inl tt)))) (λ p → {!!}) , {!!})
    --         cns ctr = {!!}
    --         typ ctr = {!!}

    -- Hmm.  Shit.  But now I'm worried about the "typ" field.  I
    -- mean, I think we'll be able to prove the equality just fine.
    -- But then don't you need to show that this proof is in fact
    -- unique?  It's okay in the leaf case because we're in a
    -- contractible type.  But the node case looks dubious...

