{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver 
open import FundamentalThm

module Algebricity where

  --
  --  Algebricity of an extension 
  --

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    -- NOTE: I think switching the "typ" entry to be a function would
    -- probably save a bunch of extra annoying funext problems later
    -- on.   Is there a reason you opted for this?
    record alg-comp (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) : Set where
      constructor ⟦_∣_∣_⟧
      field
        idx : Idx↓ M↓ i 
        cns : Cns↓ M↓ idx c
        typ : Typ↓ M↓ cns == ν

    is-algebraic : Set
    is-algebraic = (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (alg-comp i c ν) 
    
    open alg-comp public

    alg-comp-idx-= : {i : Idx M} {c : Cns M i} {ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)}
      → {α α' : alg-comp i c ν} (p : α == α')
      → idx α == idx α'
    alg-comp-idx-= p = ap idx p 

    alg-comp-cns-= : {i : Idx M} {c : Cns M i} {ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)}
      → {α α' : alg-comp i c ν} (p : α == α')
      → cns α == cns α' [ (λ x → Cns↓ M↓ x c) ↓ alg-comp-idx-= p ]
    alg-comp-cns-= idp = idp

    alg-comp-typ-= : {i : Idx M} {c : Cns M i} {ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)}
      → {α α' : alg-comp i c ν} (p : α == α')
      → (q : Pos M c) → app= (typ α) q ==
        ap (λ x → Typ↓ M↓ (snd x) q) (pair= (alg-comp-idx-= p) (alg-comp-cns-= p)) ∙ app= (typ α') q 
    alg-comp-typ-= idp q = idp
    
    alg-comp-= : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j j' : Idx↓ M↓ i} (m : j == j')
      → {d : Cns↓ M↓ j c} {d' : Cns↓ M↓ j' c}
      → (n : d == d' [ (λ x → Cns↓ M↓ x c) ↓ m ])
      → {r : Typ↓ M↓ d == ν} {r' : Typ↓ M↓ d' == ν}
      → (ϕ : (p : Pos M c) → app= r p == ap (λ x → Typ↓ M↓ (snd x) p) (pair= m n) ∙ app= r' p)
      → ⟦ j ∣ d ∣ r ⟧ == ⟦ j' ∣ d' ∣ r' ⟧
    alg-comp-= i c ν {j = j} idp {d = d} idp {r} {r'} ϕ =
      ap (λ x → ⟦ j ∣ d ∣ x ⟧) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r'))

    alg-comp-=-fst-β : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j j' : Idx↓ M↓ i} (m : j == j')
      → {d : Cns↓ M↓ j c} {d' : Cns↓ M↓ j' c}
      → (n : d == d' [ (λ x → Cns↓ M↓ x c) ↓ m ])
      → {r : Typ↓ M↓ d == ν} {r' : Typ↓ M↓ d' == ν}
      → (ϕ : (p : Pos M c) → app= r p == ap (λ x → Typ↓ M↓ (snd x) p) (pair= m n) ∙ app= r' p)
      → ap idx (alg-comp-= i c ν m n ϕ) == m
    alg-comp-=-fst-β i c ν {j = j} idp {d = d} idp {r} {r'} ϕ =
      ap idx (ap (λ x → ⟦ j ∣ d ∣ x ⟧) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r')))
        =⟨ ! (ap-∘ idx (λ x → ⟦ j ∣ d ∣ x ⟧) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r'))) ⟩
      ap (λ x → j) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r'))
        =⟨ ap-cst j (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r')) ⟩ 
      idp =∎

    alg-comp-Σ-eqv : (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → alg-comp i c ν ≃ Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))
    alg-comp-Σ-eqv i c ν = equiv to from to-from from-to 

      where to : alg-comp i c ν → Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))
            to ⟦ j ∣ d ∣ t ⟧ = j , d , t

            from : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν)) → alg-comp i c ν
            from (j , d , t) = ⟦ j ∣ d ∣ t ⟧ 

            to-from : (β : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))) → to (from β) == β
            to-from (j , d , t) = idp

            from-to : (α : alg-comp i c ν) → from (to α) == α
            from-to ⟦ j ∣ d ∣ t ⟧ = idp

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) where

    is-alg' : (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν)))
    is-alg' i c ν = equiv-preserves-level (alg-comp-Σ-eqv M M↓ i c ν) ⦃ is-alg i c ν ⦄  

    -- Here is the general statement ....
    gen-ft : (i : Idx M) (j : Idx↓ M↓ i) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν) ≃ (fst (contr-center (is-alg' i c ν)) == j)
    gen-ft i j c ν = fundamental-thm A P (is-alg' i c ν) (fst (contr-center (is-alg' i c ν))) (snd (contr-center (is-alg' i c ν))) j 

      where A : Type₀
            A = Idx↓ M↓ i
      
            P : A → Type₀
            P j' = Σ (Cns↓ M↓ j' c) (λ d → Typ↓ M↓ d == ν)

    -- So, if I sum this now over *ν*, then I get:
    --
    --   Cns↓ M↓ j c ≃ Σ ((p : Pos M c) → Idx↓ M↓ (Typ M c p)) (λ ν → (fst (contr-center (is-alg' i c ν)) == j))
    --
    -- I see.  Yeah, so this more general statement might be useful as well.  For the μ case, for
    -- example ....
    -- 

    from-ft : (i : Idx M) (j j' : Idx↓ M↓ i)
      → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j) ≃ (j == j')
    from-ft i j j' = fundamental-thm A P (is-alg' i (η M i) (cst j)) j (η↓ M↓ j , λ= (cst idp)) j' 

      where A : Type₀
            A = Idx↓ M↓ i
      
            P : A → Type₀
            P j' = Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j)

    module _ (i : Idx M) (j' : Idx↓ M↓ i) where
    
      equiv₁ : Σ (Idx↓ M↓ i) (λ j → j == j') ≃
               Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j))
      equiv₁ = Σ-emap-r (λ j → (from-ft i j j') ⁻¹) 

      equiv₂ : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j)) ≃
               Σ (Cns↓ M↓ j' (η M i)) (λ d → Σ (Idx↓ M↓ i) (λ j → Typ↓ M↓ d == cst j))
      equiv₂ = equiv to from to-from from-to

        where to : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j)) → 
                   Σ (Cns↓ M↓ j' (η M i)) (λ d → Σ (Idx↓ M↓ i) (λ j → Typ↓ M↓ d == cst j))
              to (j , d , t) = (d , j , t) 

              from : Σ (Cns↓ M↓ j' (η M i)) (λ d → Σ (Idx↓ M↓ i) (λ j → Typ↓ M↓ d == cst j)) → 
                     Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j))
              from (d , j , t) = (j , d , t) 

              to-from : (β : Σ (Cns↓ M↓ j' (η M i)) (λ d → Σ (Idx↓ M↓ i) (λ j → Typ↓ M↓ d == cst j))) → to (from β) == β
              to-from (d , j , t) = idp 

              from-to : (α : Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j))) → from (to α) == α
              from-to (j , d , t) = idp 

      typing-lem : (d : Cns↓ M↓ j' (η M i)) (j : Idx↓ M↓ i)
        → (Typ↓ M↓ d == cst j) ≃ (Typ↓ M↓ d (η-pos M i) == j)
      typing-lem d j = equiv to from to-from from-to 

        where to : (Typ↓ M↓ d == cst j) → (Typ↓ M↓ d (η-pos M i) == j)
              to ϕ = app= ϕ (η-pos M i)

              from : (Typ↓ M↓ d (η-pos M i) == j) → (Typ↓ M↓ d == cst j)
              from ψ = λ= (η-pos-elim M i (λ p → Typ↓ M↓ d p == j) ψ) 
              
              to-from : (ψ : Typ↓ M↓ d (η-pos M i) == j) → to (from ψ) == ψ
              to-from ψ = app=-β (η-pos-elim M i (λ p → Typ↓ M↓ d p == j) ψ) (η-pos M i) 

              from-to : (ϕ : Typ↓ M↓ d == cst j) → from (to ϕ) == ϕ
              from-to ϕ = λ= (η-pos-elim M i (λ p → Typ↓ M↓ d p == j) (app= ϕ (η-pos M i)))
                            =⟨ ap λ= (λ= (η-pos-elim M i (λ p → η-pos-elim M i (λ p' → Typ↓ M↓ d p' == j) (app= ϕ (η-pos M i)) p == app= ϕ p) idp)) ⟩
                          λ= (app= ϕ)
                            =⟨ ! (λ=-η ϕ) ⟩ 
                          ϕ =∎

      contr-lem : (d : Cns↓ M↓ j' (η M i))
        → is-contr (Σ (Idx↓ M↓ i) (λ j → Typ↓ M↓ d == cst j))
      contr-lem d = equiv-preserves-level ((Σ-emap-r (typing-lem d)) ⁻¹) ⦃ pathfrom-is-contr (Typ↓ M↓ d (η-pos M i)) ⦄ 

      equiv₃ : Σ (Cns↓ M↓ j' (η M i)) (λ d → Σ (Idx↓ M↓ i) (λ j → Typ↓ M↓ d == cst j)) ≃
               Cns↓ M↓ j' (η M i)
      equiv₃ = Σ₂-Unit ∘e Σ-emap-r (λ d → contr-equiv-Unit (contr-lem d)) 

      singleton-equiv : Σ (Idx↓ M↓ i) (λ j → j == j') ≃ Cns↓ M↓ j' (η M i)
      singleton-equiv = equiv₃ ∘e equiv₂ ∘e equiv₁  

      is-contr-cns↓ : is-contr (Cns↓ M↓ j' (η M i))
      is-contr-cns↓ = equiv-preserves-level singleton-equiv ⦃ pathto-is-contr j' ⦄  

