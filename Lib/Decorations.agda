--
--  Decorations.agda - Lemmas about Decorations
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Core.OpetopicType
open import Core.Universe

module Lib.Decorations where

  -- These additional rewrites are necessary because of the problem
  -- of reducing over the identity.  Not sure why this doesn't work ...
  -- postulate

  postulate
  
    Typ↓-ν↓-id : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P Q : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → (ψ : (p : Pos X S) → Q (S ⊚ p) (Typ↓ P s p))
      → (p : Pos X S)
      → Typ↓ Q (ν↓ s ψ) p ↦ Typ↓ P s p
    {-# REWRITE Typ↓-ν↓-id #-}

    ⊚↓-ν↓-id : ∀ {n ℓ} 
      → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P Q : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → (ψ : (p : Pos X S) → Q (S ⊚ p) (Typ↓ P s p))
      → (p : Pos X S)
      → ν↓ {Q = Q} s ψ ⊚↓ p ↦ ψ p
    {-# REWRITE ⊚↓-ν↓-id #-}      

    ν↓-comp-id : ∀ {n ℓ} 
      → {X Z : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
      → {P Q : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
      → {R : {F : Frm (𝕆U n ℓ)} → Z F → (f : Frm↓ F) → Type ℓ}
      → {F : Frm (𝕆U n ℓ)} {S : Src X F}
      → {ϕ' : (p : Pos X S) → Z (Typ X S p)}
      → {f : Frm↓ F} (s : Src↓ P S f)
      → (ψ : (p : Pos X S) → Q (S ⊚ p) (Typ↓ P s p))
      → (ψ' : (p : Pos X S) → R (ϕ' p) (Typ↓ Q (ν↓ s ψ) p))
      → ν↓ {Q = R} (ν↓ {Q = Q} s ψ) ψ' ≡ ν↓ {Q = R} s ψ'

  --
  --  Decorations are equivalent to functions
  --

  Dec-fun-iso : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Iso (Dec Q {f} s) ((p : Pos P s) → Q (s ⊚ p))
  Dec-fun-iso P Q {f} s = iso (λ d p → d ⊛ p) (λ-dec {P = P} Q {f} s)
                              (λ ϕ → refl) (λ d → refl)

  Dec-fun-equiv : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Dec Q {f} s
    ≃ ((p : Pos P s) → Q (s ⊚ p))
  Dec-fun-equiv P Q {f} s = isoToEquiv (Dec-fun-iso P Q s)

  --
  --  Equality of decorations can be computed pointwise
  --

  Dec-≡ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (d₀ d₁ : Dec Q {f} s)
    → (ϕ : (p : Pos P s) → d₀ ⊛ p ≡ d₁ ⊛ p) → d₀ ≡ d₁
  Dec-≡ P Q s d₀ d₁ ϕ = isoFunInjective
    (Dec-fun-iso P Q s) d₀ d₁ (λ i p → ϕ p i) 

  --
  --  Equivalence of families induces and equivalence on Src's
  --

  Src-emap : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → {P Q : Frm X → Type ℓ}
    → (ϕ : {f : Frm X} → P f ≃ Q f)
    → {f : Frm X} → Src P f ≃ Src Q f
  Src-emap {P = P} {Q} ϕ {f} = isoToEquiv
    (iso (λ s → ν {Q = Q} {f} s (λ p → fst (ϕ {_}) (s ⊚ p)))
         (λ s → ν {Q = P} {f} s (λ p → invEq (ϕ {_}) (s ⊚ p)))
         (λ s i → ν {Q = Q} {f} s (λ p → secEq (ϕ {_}) (s ⊚ p) i))
         (λ s i → ν {Q = P} {f} s (λ p → retEq (ϕ {_}) (s ⊚ p) i)))

  --
  --  Src↓ version of previous
  --

  -- This should in principle be doable without the induction, but it
  -- looks like we have a rewrite which is refusing to fire ....

  Src↓-emap-to : ∀ {n ℓ} 
    → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src P F)
    → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
    → (f : Frm↓ F) → Src↓ U S f → Src↓ V S f
  Src↓-emap-to P U V {F} S ϕ f s =
    ν↓ {Q = V} {F} {S} {λ p → S ⊚ p} s
      (λ p → fst (ϕ p (Typ↓ U s p)) (s ⊚↓ p)) 

  Src↓-emap-from : ∀ {n ℓ} 
    → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src P F)
    → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
    → (f : Frm↓ F) → Src↓ V S f → Src↓ U S f 
  Src↓-emap-from P U V {F} S ϕ f s =
    ν↓ {Q = U} {F} {S} {λ p → S ⊚ p} s
      (λ p → invEq (ϕ p (Typ↓ V s p)) (s ⊚↓ p))  

  postulate
  
    Src↓-emap-sec' : ∀ {n ℓ} 
      → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F)
      → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
      → (f : Frm↓ F) (s : Src↓ V S f)
      → Src↓-emap-to P U V S ϕ f (Src↓-emap-from P U V S ϕ f s) ≡ s
    -- Src↓-emap-sec' P U V {F} S ϕ f s = {!!}
      -- ν↓ {Q = V} {F} {S} {λ p → S ⊚ p} s 
      --   (λ p → secEq (ϕ p (Typ↓ V s p)) (s ⊚↓ p) i) 

      -- where want : Src↓ V S f
      --       want = ν↓ {Q = V} {F} {S} {λ p → S ⊚ p} s (λ p → fst (ϕ p (Typ↓ V s p)) (invEq (ϕ p (Typ↓ V s p)) (s ⊚↓ p)))

      --       have : Src↓ V S f
      --       have = Src↓-emap-to P U V S ϕ f (Src↓-emap-from P U V S ϕ f s)

      --       claim : have ≡ want
      --       claim = {!ν↓-comp-≡ P P P V U V!}

    Src↓-emap-ret' : ∀ {n ℓ} 
      → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F)
      → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
      → (f : Frm↓ F) (s : Src↓ U S f)
      → Src↓-emap-from P U V S ϕ f (Src↓-emap-to P U V S ϕ f s) ≡ s
    -- Src↓-emap-ret' P U V {F} S ϕ f s = {!!} 
      -- ν↓ {Q = U} {F} {S} {λ p → S ⊚ p} s 
      --   (λ p → retEq (ϕ p (Typ↓ U s p)) (s ⊚↓ p) i) 


  -- {-# TERMINATING #-}
  -- Src↓-emap-sec : ∀ {n ℓ} 
  --   → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
  --   → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
  --   → {F : Frm (𝕆U n ℓ)} (S : Src P F)
  --   → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
  --   → (f : Frm↓ F) (s : Src↓ V S f)
  --   → Src↓-emap-to P U V S ϕ f (Src↓-emap-from P U V S ϕ f s) ≡ s
  -- Src↓-emap-sec {zero} P U V S ϕ f s = secEq (ϕ tt* tt*) s 
  -- Src↓-emap-sec {suc n} P U V (lf C) ϕ ._ (lf↓ c) = refl 
  -- Src↓-emap-sec {suc n} P U V (nd {F} S T C Brs) ϕ ._ (nd↓ {frm} src tgt flr brs) i = 
  --   nd↓ src tgt (secEq (ϕ nd-here (frm , src , tgt)) flr i)
  --     (λ-dec↓ {Y = Branch P} (Branch↓ P V) {F = F} {S} Brs {frm} {src}
  --       (λ p → [ lvs↓ (brs ⊛↓ p)
  --              , Src↓-emap-sec P U V (br (Brs ⊛ p)) (λ q → ϕ (nd-there p q)) _ (br↓ (brs ⊛↓ p)) i
  --              ]↓))

  -- {-# TERMINATING #-}
  -- Src↓-emap-ret : ∀ {n ℓ} 
  --   → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
  --   → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
  --   → {F : Frm (𝕆U n ℓ)} (S : Src P F)
  --   → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
  --   → (f : Frm↓ F) (s : Src↓ U S f)
  --   → Src↓-emap-from P U V S ϕ f (Src↓-emap-to P U V S ϕ f s) ≡ s
  -- Src↓-emap-ret {zero} P U V S ϕ f s = retEq (ϕ tt* tt*) s 
  -- Src↓-emap-ret {suc n} P U V (lf C) ϕ ._ (lf↓ c) = refl 
  -- Src↓-emap-ret {suc n} P U V (nd {F} S T C Brs) ϕ ._ (nd↓ {frm} src tgt flr brs) i = 
  --   nd↓ src tgt (retEq (ϕ nd-here (frm , src , tgt)) flr i)
  --     (λ-dec↓ {Y = Branch P} (Branch↓ P U) {F = F} {S} Brs {frm} {src}
  --       (λ p → [ lvs↓ (brs ⊛↓ p)
  --              , Src↓-emap-ret P U V (br (Brs ⊛ p)) (λ q → ϕ (nd-there p q)) _ (br↓ (brs ⊛↓ p)) i
  --              ]↓))

  Src↓-emap : ∀ {n ℓ} 
    → (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (U V : {F : Frm (𝕆U n ℓ)} → P F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src P F)
    → (ϕ : (p : Pos P S) (f : Frm↓ (Typ P S p)) → U (S ⊚ p) f ≃ V (S ⊚ p) f)
    → (f : Frm↓ F) → Src↓ U S f ≃ Src↓ V S f
  Src↓-emap P U V {F} S ϕ f = isoToEquiv
    (iso (Src↓-emap-to P U V S ϕ f)
         (Src↓-emap-from P U V S ϕ f)
         (Src↓-emap-sec' P U V S ϕ f)
         (Src↓-emap-ret' P U V S ϕ f)) 


  Src↓-base-map-to : ∀ {n ℓ} 
    → (P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (ϕ : {F : Frm (𝕆U n ℓ)} → P F → Q F)
    → (U : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src P F)
    → (f : Frm↓ F) → Src↓ (λ p → U (ϕ p)) S f → Src↓ U (ν {Q = Q} S (λ p → ϕ (S ⊚ p))) f
  Src↓-base-map-to P Q ϕ U {F} S f s =
    ν↓ {Q = U} {F} {S} {λ p → ϕ (S ⊚ p)} {f} s (λ p → s ⊚↓ p)
    
  postulate
  
    Src↓-base-map-from : ∀ {n ℓ} 
      → (P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (ϕ : {F : Frm (𝕆U n ℓ)} → P F → Q F)
      → (U : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F)
      → (f : Frm↓ F) → Src↓ U (ν {Q = Q} S (λ p → ϕ (S ⊚ p))) f → Src↓ (λ p → U (ϕ p)) S f

    Src↓-base-map-sec : ∀ {n ℓ} 
      → (P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (ϕ : {F : Frm (𝕆U n ℓ)} → P F → Q F)
      → (U : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F)
      → (f : Frm↓ F) (s : Src↓ U (ν {Q = Q} S (λ p → ϕ (S ⊚ p))) f)
      → Src↓-base-map-to P Q ϕ U S f (Src↓-base-map-from P Q ϕ U S f s) ≡ s

    Src↓-base-map-ret : ∀ {n ℓ} 
      → (P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
      → (ϕ : {F : Frm (𝕆U n ℓ)} → P F → Q F)
      → (U : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
      → {F : Frm (𝕆U n ℓ)} (S : Src P F)
      → (f : Frm↓ F) (s : Src↓ (λ p → U (ϕ p)) S f)
      → Src↓-base-map-from P Q ϕ U S f (Src↓-base-map-to P Q ϕ U S f s) ≡ s 

  Src↓-base-map : ∀ {n ℓ} 
    → (P Q : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    → (ϕ : {F : Frm (𝕆U n ℓ)} → P F → Q F)
    → (U : {F : Frm (𝕆U n ℓ)} → Q F → Frm↓ F → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src P F)
    → (f : Frm↓ F) → Src↓ (λ p → U (ϕ p)) S f ≃ Src↓ U (ν {Q = Q} S (λ p → ϕ (S ⊚ p))) f 
  Src↓-base-map P Q ϕ U S f = isoToEquiv
    (iso (Src↓-base-map-to P Q ϕ U S f)
         (Src↓-base-map-from P Q ϕ U S f)
         (Src↓-base-map-sec P Q ϕ U S f)
         (Src↓-base-map-ret P Q ϕ U S f)) 

  --
  --  Src and Dec is equivalent to a Src with Σ's
  --

  module DecΣEquiv {n ℓ}
    {X : 𝕆Type n ℓ}
    (P : Frm X → Type ℓ)
    (Q : {f : Frm X} → P f → Type ℓ) where

    ΣPQ : Frm X → Type ℓ
    ΣPQ f = Σ (P f) (Q {f})

    to : {f : Frm X} → Σ[ s ∈ Src P f ] (Dec Q {f} s) → Src ΣPQ f
    to (s , d) = ν {Q = ΣPQ} s (λ p → s ⊚ p , d ⊛ p) 

    from : {f : Frm X} → Src ΣPQ f → Σ[ s ∈ Src P f ] (Dec Q {f} s)
    from {f} ss = let s = ν {Q = P} ss (λ p → fst (ss ⊚ p))
                  in (s , λ-dec Q {f} s (λ p → snd (ss ⊚ ν-lift ss (λ p → fst (ss ⊚ p)) p)))

    eqv : {f : Frm X} → (Σ[ s ∈ Src P f ] (Dec Q {f} s)) ≃ Src ΣPQ f
    eqv {f} = isoToEquiv (iso to from (λ ss → refl {x = ss}) λ sd → refl {x = sd}) 

  --
  --  Dependent Verison of Dec-Σ-equiv
  --

  module Dec↓ΣEquiv {n ℓ} 
    (P : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ))
    (Q : {F : Frm (𝕆U n ℓ)} → P F → Type (ℓ-suc ℓ))
    (U : {F : Frm (𝕆U n ℓ)} → P F → (f : Frm↓ F) → Type ℓ)
    (V : {F : Frm (𝕆U n ℓ)} {C : P F} → Q C → {f : Frm↓ F} → U C f → Type ℓ) where

    module D = DecΣEquiv {X = 𝕆U n ℓ} P Q

    ΣUV : {F : Frm (𝕆U n ℓ)} → Σ (P F) Q → Frm↓ F → Type ℓ 
    ΣUV {F} (x , y) f' = Σ (U x f') (V y)
    
    to : {F : Frm (𝕆U n ℓ)} (S : Src P F) (D : Dec {X = 𝕆U n ℓ} Q S)
      → {f : Frm↓ F}
      → Σ[ s ∈ Src↓ U S f ] (Dec↓ Q V S D s)
      → Src↓ ΣUV (D.to (S , D)) f
    to {F} S D (s , d) = ν↓ {Q = ΣUV} {F} {S} {λ p → S ⊚ p , D ⊛ p} s
                           (λ p → s ⊚↓ p , d ⊛↓ p)

    from : {F : Frm (𝕆U n ℓ)} (s : Src D.ΣPQ F)
      → {f : Frm↓ F} (ss : Src↓ ΣUV s f)
      → Σ[ s↓ ∈ Src↓ U (D.from s .fst) f ] (Dec↓ Q V (D.from s .fst) (D.from s .snd) s↓)
    from {F} s {f} ss =
      let s↓ = ν↓ {Q = U} {F} {s} {λ p → fst (s ⊚ p)} {f} ss (λ p → fst (ss ⊚↓ p))
      in s↓ , λ-dec↓ {X = P} {Q} {U} V {F} {D.from s .fst} (D.from s .snd) {f} {s↓}
                 (λ p → snd (ss ⊚↓ ν-lift s (λ q → fst (s ⊚ q)) p))

    sec' : {F : Frm (𝕆U n ℓ)} (s : Src D.ΣPQ F)
      → {f : Frm↓ F} (ss : Src↓ ΣUV s f)
      → (to (D.from s .fst) (D.from s .snd) (from s ss)) ≡ ss
    sec' s ss = refl 

    eqv : {F : Frm (𝕆U n ℓ)} (S : Src P F) (D : Dec {X = 𝕆U n ℓ} Q S)
      → {f : Frm↓ F} 
      → (Σ[ s ∈ Src↓ U S f ] (Dec↓ Q V S D s))
      ≃ Src↓ ΣUV (D.to (S , D)) f
    eqv S D = isoToEquiv (iso (to S D) (from (D.to (S , D)))
                (sec' (D.to (S , D))) (λ sd → refl {x = sd})) 
