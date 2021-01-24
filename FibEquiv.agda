{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import SliceLemmas

module FibEquiv where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) where

    open import SliceUnfold M
    open ExtUnfold M↓

    -- This variant of the slice index lemma appears to be somewhat
    -- simpler, and more in line with what actually happens in practice.
    -- Perhaps you should in fact use it in the SliceAlg proof.
    slc-idx-lem' : (i : Idx M) (j : Idx↓ M↓ i)
      → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j₀ : Idx↓ M↓ i} {e₀ : j₀ == j}
      → {d₀ : Cns↓ M↓ j₀ c} {α₀ : (p : Pos M c) → Typ↓ M↓ d₀ p == ν p}
      → {j₁ : Idx↓ M↓ i} {e₁ : j₁ == j}
      → {d₁ : Cns↓ M↓ j₁ c} {α₁ : (p : Pos M c) → Typ↓ M↓ d₁ p == ν p}
      → (q : j₀ == j₁) (r : e₀ == q ∙ e₁)
      → (s : d₀ == d₁ [ (λ x → Cns↓ M↓ x c) ↓ q ])
      → (t : (p : Pos M c) → α₀ p == ap (λ x → Typ↓ M↓ (snd x) p) (pair= q s) ∙ α₁ p)
      → Path {A = Idx↓ ExtSlc↓₁ ((i , j) , c , ν)}
        ((j₀ , e₀) , (d₀ , α₀)) ((j₁ , e₁) , (d₁ , α₁)) 
    slc-idx-lem' i j c ν idp idp idp t = pair= (pair= idp idp) (pair= idp (λ= t)) 

    module _ (X : Rel₁ (Idx↓ M↓)) (is-fib-X : is-fib₁ X)
             (X-is-alg : (i : Idx M) (c : Cns M i)
               → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
               → X ((i , idx (contr-center (is-alg i c ν)) ) , c , ν)) where

      fib-eqv : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X i 
      fib-eqv ((i , j) , c , ν) = equiv to from to-from from-to 

        where to : Idx↓ ExtSlc↓₁ ((i , j) , c , ν) → X ((i , j) , c , ν)
              to ((j' , j'=j) , d , t) = transport (λ x → X ((i , x) , c , ν)) to-pth (X-is-alg i c ν) 

                where α : alg-comp M M↓ i c ν
                      α = ⟦ j' ∣ d ∣ λ= t ⟧ 

                      to-pth : idx (contr-center (is-alg i c ν)) == j
                      to-pth = ap idx (contr-path (is-alg i c ν) α) ∙ j'=j 

              from :  X ((i , j) , c , ν) → Idx↓ ExtSlc↓₁ ((i , j) , c , ν) 
              from x = (idx α , from-pth) , cns α , app= (typ α)

                where α : alg-comp M M↓ i c ν
                      α = contr-center (is-alg i c ν)

                      from-pth : idx α == j
                      from-pth = fst= (contr-has-all-paths ⦃ is-fib-X i c ν ⦄ (idx α , X-is-alg i c ν) (j , x))  

              to-from : (x : X ((i , j) , c , ν)) → to (from x) == x
              to-from x = transport (λ x → X ((i , x) , c , ν))
                            (ap idx (contr-path (is-alg i c ν) ⟦ idx α ∣ cns α ∣ λ= (app= (typ α)) ⟧) ∙ from-pth)
                            (X-is-alg i c ν) =⟨ lemma 
                             |in-ctx (λ h → transport (λ x → X ((i , x) , c , ν)) (h ∙ from-pth) (X-is-alg i c ν)) ⟩ 
                          transport (λ x → X ((i , x) , c , ν))
                            (ap idx (contr-path (is-alg i c ν) α) ∙ from-pth)
                            (X-is-alg i c ν) =⟨ contr-has-all-paths ⦃ =-preserves-contr (is-alg i c ν) ⦄
                              (contr-path (is-alg i c ν) α) idp
                            |in-ctx (λ h → transport (λ x → X ((i , x) , c , ν)) (ap idx h ∙ from-pth) (X-is-alg i c ν)) ⟩
                          transport (λ x → X ((i , x) , c , ν)) from-pth (X-is-alg i c ν)
                            =⟨ to-transp (snd= (contr-has-all-paths ⦃ is-fib-X i c ν ⦄ (idx α , X-is-alg i c ν) (j , x))) ⟩ 
                          x =∎

                where α : alg-comp M M↓ i c ν
                      α = contr-center (is-alg i c ν)

                      from-pth : idx α == j
                      from-pth = fst= (contr-has-all-paths ⦃ is-fib-X i c ν ⦄ (idx α , X-is-alg i c ν) (j , x))  

                      α'=α : α == ⟦ idx α ∣ cns α ∣ λ= (app= (typ α)) ⟧
                      α'=α = alg-comp-= M M↓ i c ν idp idp (λ p → ! (app=-β (app= (typ α)) p))
                      
                      lemma = ap idx (contr-path (is-alg i c ν) ⟦ idx α ∣ cns α ∣ λ= (app= (typ α)) ⟧) 
                                =⟨ ap (ap idx) ((contr-has-all-paths ⦃ =-preserves-contr (is-alg i c ν) ⦄
                                  (contr-path (is-alg i c ν) ⟦ idx α ∣ cns α ∣ λ= (app= (typ α)) ⟧) α'=α)) ⟩
                              ap idx α'=α
                                =⟨ alg-comp-=-fst-β M M↓ i c ν idp idp (λ p → ! (app=-β (app= (typ α)) p)) ⟩ 
                              idp
                                =⟨ ap (ap idx) (contr-has-all-paths ⦃ =-preserves-contr (is-alg i c ν) ⦄
                                  idp (contr-path (is-alg i c ν) α)) ⟩ 
                              ap idx (contr-path (is-alg i c ν) α) =∎

              from-to : (a : Idx↓ ExtSlc↓₁ ((i , j) , c , ν)) → from (to a) == a
              from-to ((j' , j'=j) , d , t) =
                (idx α , from-pth) , cns α , app= (typ α)
                  =⟨ slc-idx-lem' i j c ν (ap idx α=α') lemma
                    (alg-comp-cns-= M M↓ α=α') (λ p → alg-comp-typ-= M M↓ α=α' p ∙
                      ap (λ h → ap (λ x → Typ↓ M↓ (snd x) p) (pair= (alg-comp-idx-= M M↓ α=α') (alg-comp-cns-= M M↓ α=α')) ∙ h) (app=-β t p)) ⟩ 
                ((j' , j'=j) , d , t) =∎

                where open SliceOver M M↓

                      α : alg-comp M M↓ i c ν
                      α = contr-center (is-alg i c ν)
              
                      α' : alg-comp M M↓ i c ν
                      α' = ⟦ j' ∣ d ∣ λ= t ⟧ 

                      α=α' : α == α'
                      α=α' = contr-path (is-alg i c ν) α'

                      to-pth : idx α == j
                      to-pth = ap idx α=α' ∙ j'=j 

                      ctr-pth : (idx α , X-is-alg i c ν) == (j , transport (λ x → X ((i , x) , c , ν)) to-pth (X-is-alg i c ν))
                      ctr-pth = (contr-has-all-paths ⦃ is-fib-X i c ν ⦄ (idx α , X-is-alg i c ν)
                        (j , transport (λ x → X ((i , x) , c , ν)) to-pth (X-is-alg i c ν)))

                      other-pth : (idx α , X-is-alg i c ν) == (j , transport (λ x → X ((i , x) , c , ν)) to-pth (X-is-alg i c ν))
                      other-pth = pair= to-pth (from-transp (λ x → X ((i , x) , c , ν)) to-pth idp) 

                      from-pth : idx α == j
                      from-pth = fst= ctr-pth

                      lemma : from-pth == to-pth 
                      lemma = from-pth
                                =⟨ contr-has-all-paths ⦃ =-preserves-contr (is-fib-X i c ν) ⦄
                                   ctr-pth other-pth |in-ctx fst= ⟩
                              fst= other-pth
                                =⟨ fst=-β to-pth (from-transp (λ x → X ((i , x) , c , ν)) to-pth idp) ⟩ 
                              to-pth =∎ 

    -- Proof that it suffices to have a map in order to have an equivalence
    module _ (X : Rel₁ (Idx↓ M↓)) (is-fib-X : is-fib₁ X)
             (ϕ : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i → X i) where

      X-is-alg : (i : Idx M) (c : Cns M i)
        → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
        → X ((i , idx (contr-center (is-alg i c ν)) ) , c , ν)
      X-is-alg i c ν = ϕ ((i , idx α) , c , ν) ((idx α , idp) , cns α , app= (typ α)) 

        where α : alg-comp M M↓ i c ν
              α = (contr-center (is-alg i c ν))

      hence : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X i
      hence = fib-eqv X is-fib-X X-is-alg
