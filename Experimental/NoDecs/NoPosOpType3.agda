{-# OPTIONS --no-positivity-check --no-termination-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.NoDecs.NoPosOpType3 where

  --
  --  Opetopic Types
  --

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  postulate

    Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → Frm X → Type ℓ

    Dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ 

    zip : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (s : Src P f) (δ : Dec Q s)
      → Src (λ f → Σ (P f) Q) f

    unzip : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X}
      → (s : Src (λ f → Σ (P f) Q) f)
      → Σ (Src P f) (Dec Q)

    -- 
    --  Monadic Structure
    --

    η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → Src Q f 

    -- What if μ simply has a decoration also as a parameter?  Then
    -- bind takes an extra argument and zipping is definable, right? 

    --
    --  Decomposing Decorations
    --

    -- INCOMPLETE : there should be compatibility conditions with the
    -- monad and naturality laws.

    η-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (x : P f)
      → Dec Q (η P x) → Q x

    μ-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → Q f → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → Dec R (μ s ϕ) → Dec (λ p → Dec R (ϕ p)) s 

    zip-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {R : {f : Frm X} → Σ (P f) Q → Type ℓ}
      → {f : Frm X} (s : Src P f) (δ : Dec Q s)
      → Dec R (zip s δ) → Dec (λ p → Σ[ q ∈ Q p ] R (p , q)) s

    --
    --  Zipping laws
    --

    zip-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (x : P f) (δ : Dec Q (η P x))
      → zip (η P x) δ ↦ η _ (x , η-dec x δ)
    {-# REWRITE zip-η #-}

    zip-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → Q f → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → (δ : Dec R (μ s ϕ))
      → zip (μ s ϕ) δ ↦ μ (zip s (μ-dec s ϕ δ)) (λ p → zip (ϕ (fst p)) (snd p))
    {-# REWRITE zip-μ #-}

    zip-zip : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {R : {f : Frm X} → Σ (P f) Q → Type ℓ}
      → {f : Frm X} (s : Src P f) (δ : Dec Q s)
      → (ϵ : Dec R (zip s δ))
      → zip (zip s δ) ϵ ↦ {!zip s!} 

    --
    --  Monad Laws
    --

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q : Frm X → Type ℓ)
      → (f : Frm X) (x : P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → μ (η P x) ϕ ↦ ϕ x
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ s (η P) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q R : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → (ψ : {f : Frm X} → Q f → Src R f)
      → μ (μ s ϕ) ψ ↦ μ s (λ p → μ (ϕ p) ψ)
    {-# REWRITE μ-assoc #-}

  --
  --  Definitions of opeotpic types and frames
  --

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ src ∈ Src P f ] 
    P f

  --
  --  Pasting Diagrams and their Positions 
  --

  module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ} (U : Frm (X , P) → Type ℓ) where

    data Pd : Frm (X , P) → Type ℓ

    record Branch {f : Frm X} (x : P f) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        lvs : Src P f
        br : Pd (f , lvs , x)

    open Branch public
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (src : Src P f) (tgt : P f)
         → (flr : U (f , src , tgt))
         → (brs : Dec Branch src) 
         → Pd (f , μ (zip src brs) (lvs ∘ snd) , tgt)

    γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (brs : Dec Branch src)
      → Pd (frm , μ (zip src brs) (lvs ∘ snd) , tgt)
    γ (lf tgt) brs = br (η-dec tgt brs)
    γ (nd src tgt flr lbrs) brs = {!nd src tgt flr ?!}

      where brs' : Dec (λ p → Dec Branch (lvs (snd p))) (zip src lbrs)
            brs' = μ-dec (zip src lbrs) (lvs ∘ snd) brs


--       where brs' : Dec (λ p → Dec (λ {f} t → Σ-syntax (Src P f) (λ s → Pd (f , s , t))) (lvs p)) lbrs
--             brs' = μ-dec lbrs lvs brs 

--             lbrs' : Src (λ f → Σ (Branch f) (λ p →  Dec (λ {f = f₁} t → Σ-syntax (Src P f₁) (λ s → Pd (f₁ , s , t))) (lvs p))) _
--             lbrs' = zip lbrs brs' 

--             lbrs'' : Src Branch _
--             lbrs'' = μ lbrs' (λ { {f} (b , δ) →
--               η Branch [ stm b , μ (zip (lvs b) δ) (λ tsp → tsp .snd .fst) , γ (br b) δ ] })


-- --   module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ} (U : Frm (X , P) → Type ℓ) where

-- --     data Pd : Frm (X , P) → Type ℓ

-- --     record Branch {f : Frm X} (x : P f) : Type ℓ where
-- --       inductive
-- --       eta-equality
-- --       constructor [_,_,_]
-- --       field
-- --         lvs : Src P f
-- --         br : Pd (f , lvs , x)

-- --     open Branch public
    
-- --     data Pd where

-- --       lf : {f : Frm X} (tgt : P f)
-- --          → Pd (f , η P tgt , tgt) 

-- --       nd : {f : Frm X} (src : Src P f) (tgt : P f)
-- --          → (flr : U (f , src , tgt))
-- --          → (brs : Dec Branch src) 
-- --          → Pd (f , μ P (ν₂ (λ p → lvs) src brs) , tgt)

-- --     γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
-- --       → (pd : Pd (frm , src , tgt ))
-- --       → (brs : Dec Branch src)
-- --       → Pd (frm , μ P (ν₂ (λ p → lvs) src brs) , tgt)
-- --     γ (lf tgt) brs = br (η-dec tgt brs)
-- --     γ (nd src tgt flr lbrs) brs = {!lbrs!}

-- --       where lbrs' : Dec (Dec Branch) (ν₂ (λ p → lvs) src lbrs)
-- --             lbrs' = μ-dec (ν₂ (λ p → lvs) src lbrs) brs

-- --             lbrs'' : Dec (λ p → Σ-syntax (Branch p) (λ r → Dec Branch (lvs r))) src
-- --             lbrs'' = ν₂-dec (λ p → lvs) src lbrs lbrs' 

-- --             lbrs''' : Dec Branch src
-- --             lbrs''' = {!!} 

-- --     -- γ (lf tgt) ϕ = snd (η-dec tgt ϕ) 
-- --     -- γ (nd {f} tgt brs flr) ϕ = {!nd tgt brs' flr!}

-- --     --   where ϕ' : Dec (Src P) (Dec P (λ {f} t → Σ-syntax (Src P f) (λ s → Pd (f , s , t)))) (ν lvs brs)
-- --     --         ϕ' = μ-dec (ν lvs brs) ϕ

-- --     --         ϕ'' : Dec Branch (λ br → Dec P (λ {f} t → Σ[ s ∈ Src P f ] Pd (f , s , t)) (lvs br)) brs 
-- --     --         ϕ'' = ν-dec lvs brs ϕ'

-- --     --         brs' : Src Branch f
-- --     --         brs' = ν₂ (λ b ψ → [ _ , _ , γ (br b) ψ ]) brs ϕ'' 

-- -- -- (ν stm brs) != (ν₂ (λ p r → stm p) brs (ν-dec lvs brs ϕ')) of type

-- --   -- Pd (f , μ P (ν lvs brs') , tgt)
-- --   -- Pd (f , μ P (ν₂ (λ t → fst) (μ P (ν lvs brs)) ϕ) , tgt)

-- -- -- Pd (f , μ P (ν (μ P) (ν₂ (λ o {f = f₁} → ν₂ (λ r p {f = f₂} → fst f₂) (lvs o) f₁) brs (ν-dec (λ _ {f = f₁} → lvs f₁) brs (μ-dec (ν lvs brs) ϕ)))) , tgt)
-- -- -- Pd (f , μ P (ν₂ (λ p r → μ P (ν₂ (λ r₁ p₁ {f = f₁} → fst f₁) (lvs p) r)) brs (ν-dec (λ _ {f = f₁} → lvs f₁) brs (μ-dec (ν lvs brs) ϕ))) , tgt)
