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

module Core.OpetopicType where

  --
  --  Opetopic Types
  --

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → Frm X → Type ℓ

  Pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Type ℓ 

  Typ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s) → Frm X 

  _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s)
    → P (Typ P s p)

  --
  --  Decorations
  --
  
  Dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Type ℓ 

  _⊛_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {Q : {f : Frm X} → P f → Type ℓ}
    → {f : Frm X} {s : Src P f} (δ : Dec Q s)
    → (p : Pos P s) → Q (s ⊚ p) 

  λ-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : {f : Frm X} → P f → Type ℓ)
    → {f : Frm X} (s : Src P f) 
    → (δ : (p : Pos P s) → Q (s ⊚ p))
    → Dec Q s 

  --
  --  Monadic Structure
  --

  ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ P s p))
    → Src Q f

  η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Src P f 

  
  μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src (Src P) f) → Src P f 

  --
  --  Position Intro 
  --

  ν-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ P s p))
    → Pos P s → Pos Q (ν s ϕ)

  η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Pos P (η P x)

  μ-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src (Src P) f)
    → (p : Pos (Src P) s)
    → (q : Pos P (s ⊚ p))
    → Pos P (μ P s)

  --
  --  Position Elim
  --

  ν-lift : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ P s p))
    → Pos Q (ν s ϕ) → Pos P s

  η-pos-elim : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (x : P f)
    → (Q : Pos P (η P x) → Type ℓ')
    → (q : Q (η-pos P x))
    → (p : Pos P (η P x)) → Q p

  μ-fst : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src (Src P) f)
    → (p : Pos P (μ P s))
    → Pos (Src P) s

  μ-snd : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src (Src P) f)
    → (p : Pos P (μ P s))
    → Pos P (s ⊚ μ-fst P s p)

  postulate
  
    --
    --  Decoration Computation
    --
    
    λ-dec-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f) 
      → (δ : (p : Pos P s) → Q (s ⊚ p))
      → (p : Pos P s)
      → λ-dec Q s δ ⊛ p ↦ δ p
    {-# REWRITE λ-dec-β #-} 

    λ-dec-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f) 
      → (δ : Dec Q s)
      → λ-dec Q s (λ p → δ ⊛ p) ↦ δ
    {-# REWRITE λ-dec-η #-} 

    --
    --  Position Computation
    --

    η-pos-elim-β : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → η-pos-elim x Q q (η-pos P x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

    ν-lift-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos P s)
      → ν-lift {Q = Q} s ϕ (ν-pos s ϕ p) ↦ p
    {-# REWRITE ν-lift-β #-} 

    ν-lift-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s ϕ))
      → ν-pos {Q = Q} s ϕ (ν-lift s ϕ p) ↦ p
    {-# REWRITE ν-lift-η #-} 

    μ-fst-β : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos (Src P) s)
      → (q : Pos P (s ⊚ p))
      → μ-fst P s (μ-pos P s p q) ↦ p
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos (Src P) s)
      → (q : Pos P (s ⊚ p))
      → μ-snd P s (μ-pos P s p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → μ-pos P s (μ-fst P s p) (μ-snd P s p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Typing and Inhabitants
    --

    Typ-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s ϕ))
      → Typ Q (ν s ϕ) p ↦ Typ P s (ν-lift s ϕ p)
    {-# REWRITE Typ-ν #-}

    ⊚-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s ϕ))
      → ν s ϕ ⊚ p ↦ ϕ (ν-lift s ϕ p)
    {-# REWRITE ⊚-ν #-}

    Typ-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → Typ P (η P x) p ↦ f
    {-# REWRITE Typ-η #-}

    ⊚-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → η P x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    Typ-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → Typ P (μ P s) p ↦ Typ P (s ⊚ μ-fst P s p) (μ-snd P s p)
    {-# REWRITE Typ-μ #-}

    ⊚-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → μ P s ⊚ p ↦ (s ⊚ (μ-fst P s p)) ⊚ (μ-snd P s p)
    {-# REWRITE ⊚-μ #-}

    --
    --  Functoriality of ν 
    --

    ν-id : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → ν {Q = P} s (_⊚_ s) ↦ s
    {-# REWRITE ν-id #-}
    
    ν-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q R : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (ψ : (p : Pos Q (ν s ϕ)) → R (Typ Q (ν s ϕ) p))
      → ν {Q = R} (ν s ϕ) ψ ↦ ν s (λ p → ψ (ν-pos s ϕ p))
    {-# REWRITE ν-ν #-} 

    -- 
    -- Naturality Laws
    --
      
    ν-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Q f)
      → ν (η P x) ϕ ↦ η Q (ϕ (η-pos P x))
    {-# REWRITE ν-η #-}

    ν-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (ϕ : (p : Pos P (μ P s)) → Q (Typ P (μ P s) p))
      → ν (μ P s) ϕ ↦ μ Q (ν s (λ p → ν (s ⊚ p) (λ q → ϕ (μ-pos P s p q))))
    {-# REWRITE ν-μ #-}

    --
    -- Monad Laws
    --

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (η (Src P) s) ↦ s 
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (ν s (λ p → η P (s ⊚ p))) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src (Src (Src P)) f)
      → μ P (μ (Src P) s) ↦ μ P (ν s (λ p → μ P (s ⊚ p))) 
    {-# REWRITE μ-assoc #-}

  --
  --  Bind form of monad
  --

  bind : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P Q : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
    → Src Q f
  bind P Q f s ϕ = μ Q (ν s ϕ) 

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

    record Branch {f : Frm X} (stm : P f) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_]
      field
        lvs : Src P f
        br : Pd (f , lvs , stm)

    open Branch public

    -- Note: this could be more general as P is not used ...
    canopy : {f : Frm X} {s : Src P f}
      → Dec Branch s → Src P f
    canopy {s = s} δ = μ P (ν s (λ p → lvs (δ ⊛ p)))

    canopy-pos : {f : Frm X} {s : Src P f}
      → (brs : Dec Branch s)
      → (p : Pos P s) (q : Pos P (lvs (brs ⊛ p)))
      → Pos P (canopy brs) 
    canopy-pos {s = s} brs p q =
      μ-pos P (ν s (λ q → lvs (brs ⊛ q)))
        (ν-pos s (λ q → lvs (brs ⊛ q)) p) q

    canopy-fst : {f : Frm X} {s : Src P f}
      → (brs : Dec Branch s) (p : Pos P (canopy brs))
      → Pos P s 
    canopy-fst {s = s} brs p =
      ν-lift s (λ p → lvs (brs ⊛ p))
        (μ-fst P (ν s (λ p → lvs (brs ⊛ p))) p)  

    canopy-snd : {f : Frm X} {s : Src P f}
      → (brs : Dec Branch s) (p : Pos P (canopy brs))
      → Pos P (lvs (brs ⊛ canopy-fst brs p))
    canopy-snd {s = s} brs p = μ-snd P (ν s (λ p → lvs (brs ⊛ p))) p

    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (src : Src P f) (tgt : P f) 
         → (flr : U (f , src , tgt))
         → (brs : Dec Branch src)
         → Pd (f , μ P (ν src (λ p → lvs (brs ⊛ p))) , tgt)


    data PdPos : {f : Frm (X , P)} → Pd f → Type ℓ where

      nd-here : {f : Frm X} {src : Src P f} {tgt : P f}
         → {flr : U (f , src , tgt)}
         → {brs : Dec Branch src}
         → PdPos (nd src tgt flr brs)

      nd-there : {f : Frm X} {src : Src P f} {tgt : P f}
         → {flr : U (f , src , tgt)}
         → {brs : Dec Branch src}
         → (p : Pos P src) (q : PdPos (br (brs ⊛ p)))
         → PdPos (nd src tgt flr brs)

    γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (brs : (p : Pos P src) → Branch (src ⊚ p))
      → Pd (frm , μ P (ν src λ p → lvs (brs p)) , tgt)

    γ-brs : {frm : Frm X} {src : Src P frm} (lbrs : Dec Branch src)
      → (brs : (p : Pos P (canopy lbrs)) → Branch (canopy lbrs ⊚ p))
      → (p : Pos P src) → Branch (src ⊚ p)
    γ-brs lbrs brs p = [ μ P (ν (lvs (lbrs ⊛ p)) (λ q → lvs (brs (canopy-pos lbrs p q))))
                       , γ (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q))
                       ]

    γ (lf tgt) brs = br (brs (η-pos P tgt))
    γ (nd src tgt flr lbrs) brs =
      nd src tgt flr (λ-dec Branch src (γ-brs lbrs brs))

    γ-inl : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (brs : (p : Pos P src) → Branch (src ⊚ p))
      → (p : PdPos pd) → PdPos (γ pd brs)
    γ-inl (nd src tgt flr lbrs) brs nd-here = nd-here
    γ-inl (nd src tgt flr lbrs) brs (nd-there p q) =
      nd-there p (γ-inl (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q)) q) 

    γ-inr : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (brs : (p : Pos P src) → Branch (src ⊚ p))
      → (p : Pos P src) (q : PdPos (br (brs p)))
      → PdPos (γ pd brs)
    γ-inr (lf tgt) brs p q = 
      η-pos-elim tgt (λ p → PdPos (br (brs p)) → PdPos (br (brs (η-pos P tgt)))) (λ x → x) p q
    γ-inr (nd src tgt flr lbrs) brs pq r = 
      let p = canopy-fst lbrs pq
          q = canopy-snd lbrs pq
      in nd-there p (γ-inr (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q)) q r)

    γ-pos-elim : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (brs : (p : Pos P src) → Branch (src ⊚ p))
      → ∀ {ℓ'} (B : PdPos (γ pd brs) → Type ℓ')
      → (inl* : (p : PdPos pd) → B (γ-inl pd brs p))
      → (inr* : (p : Pos P src) (q : PdPos (br (brs p))) → B (γ-inr pd brs p q))
      → (p : PdPos (γ pd brs)) → B p
    γ-pos-elim (lf tgt) brs B inl* inr* p = inr* (η-pos P tgt) p
    γ-pos-elim (nd src tgt flr lbrs) brs B inl* inr* nd-here = inl* nd-here
    γ-pos-elim (nd src tgt flr lbrs) brs B inl* inr* (nd-there u v) = 
      γ-pos-elim (br (lbrs ⊛ u)) (λ q → brs (canopy-pos lbrs u q))
         (λ v' → B (nd-there u v')) (λ q → inl* (nd-there u q))
         (λ q → inr* (canopy-pos lbrs u q)) v
    
    postulate

      γ-pos-elim-inl-β : {frm : Frm X} {src : Src P frm} {tgt : P frm}
        → (pd : Pd (frm , src , tgt ))
        → (brs : (p : Pos P src) → Branch (src ⊚ p))
        → ∀ {ℓ'} (B : PdPos (γ pd brs) → Type ℓ')
        → (inl* : (p : PdPos pd) → B (γ-inl pd brs p))
        → (inr* : (p : Pos P src) (q : PdPos (br (brs p))) → B (γ-inr pd brs p q))
        → (p : PdPos pd)
        → γ-pos-elim pd brs B inl* inr* (γ-inl pd brs p) ↦ inl* p
      {-# REWRITE γ-pos-elim-inl-β #-}
        
      γ-pos-elim-inr-β : {frm : Frm X} {src : Src P frm} {tgt : P frm}
        → (pd : Pd (frm , src , tgt ))
        → (brs : (p : Pos P src) → Branch (src ⊚ p))
        → ∀ {ℓ'} (B : PdPos (γ pd brs) → Type ℓ')
        → (inl* : (p : PdPos pd) → B (γ-inl pd brs p))
        → (inr* : (p : Pos P src) (q : PdPos (br (brs p))) → B (γ-inr pd brs p q))
        → (p : Pos P src) (q : PdPos (br (brs p)))
        → γ-pos-elim pd brs B inl* inr* (γ-inr pd brs p q) ↦ inr* p q
      {-# REWRITE γ-pos-elim-inr-β #-}

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U pd = PdPos U pd 

  Typ {zero} P s p = tt*
  Typ {suc n} U (nd src tgt flr brs) nd-here = _ , src , tgt
  Typ {suc n} U (nd src tgt flr brs) (nd-there p q) = Typ U (br (brs ⊛ p)) q

  _⊚_ {zero} s p = s
  _⊚_ {suc n} {P = U} (nd src tgt flr brs) nd-here = flr
  _⊚_ {suc n} {P = U} (nd src tgt flr brs) (nd-there p q) = _⊚_ {P = U} (br (brs ⊛ p)) q

  Dec {zero} Q s = Q s
  Dec {suc n} Q (lf tgt) = Unit*
  Dec {suc n} {X = X , P} {U} Q (nd src tgt flr brs) =
    Q flr × Dec {P = λ f → Σ (P f) (Branch U)} (λ pb → Dec {X = X , P} Q (br (snd pb)))
      (ν {Q = λ f → Σ (P f) (Branch U)} src (λ p → src ⊚ p , brs ⊛ p))

  _⊛_ {zero} {s = s} δ p = δ
  _⊛_ {suc n} {s = nd src tgt flr brs} (q , _) nd-here = q
  _⊛_ {suc n} {s = nd src tgt flr brs} (_ , δ) (nd-there p q) = 
    (δ ⊛ (ν-pos src (λ p₁ → (src ⊚ p₁) , (brs ⊛ p₁)) p)) ⊛ q 

  λ-dec {zero} Q s δ = δ tt*
  λ-dec {suc n} Q (lf tgt) δ = tt*
  λ-dec {suc n} {X = X , P} {U} Q (nd src tgt flr brs) δ = 
    δ nd-here , (λ-dec {X = X} {P = λ f → Σ (P f) (Branch U)} (λ pb → Dec {X = X , P} Q (br (snd pb)))
      (ν {Q = λ f → Σ (P f) (Branch U)} src (λ p → (src ⊚ p) , (brs ⊛ p)))
      (λ p → λ-dec {X = X , P} {U} Q (br (brs ⊛ ν-lift src (λ p₁ → (src ⊚ p₁) , (brs ⊛ p₁)) p))
              λ q → δ (nd-there (ν-lift src (λ p₁ → (src ⊚ p₁) , (brs ⊛ p₁)) p) q)))

  ν {zero} s ϕ = ϕ tt*
  ν {suc n} (lf tgt) ϕ = lf tgt
  ν {suc n} {X = X , P} (nd src tgt flr brs) ϕ =
    nd src tgt (ϕ nd-here) (λ-dec (Branch _) src λ p →
      [ lvs (brs ⊛ p) , (ν {suc n} (br (brs ⊛ p)) (λ q → ϕ (nd-there p q))) ])

  ν-pos {zero} s ϕ p = tt*
  ν-pos {suc n} (nd src tgt flr brs) ϕ nd-here = nd-here
  ν-pos {suc n} (nd src tgt flr brs) ϕ (nd-there p q) =
    nd-there p (ν-pos (br (brs ⊛ p)) (λ q → ϕ (nd-there p q)) q)

  ν-lift {zero} s ϕ p = tt*
  ν-lift {suc n} (nd src tgt flr brs) ϕ nd-here = nd-here
  ν-lift {suc n} (nd src tgt flr brs) ϕ (nd-there p q) =
    nd-there p (ν-lift (br (brs ⊛ p)) (λ q → ϕ (nd-there p q)) q)

  η-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Dec {X = X} (Branch U) s
  η-dec {X = X} {P} U s =
    λ-dec {X = X} {P} (Branch U) s
      (λ p → [ η P (s ⊚ p) , lf (s ⊚ p) ])

  η {zero} P x = x
  η {suc n} {X = X , P} U {f = _ , src , tgt} x =
    nd src tgt x (η-dec U src)

  η-pos {zero} P x = tt*
  η-pos {suc n} {X = X , P} U {f = _ , src , tgt} x = nd-here

  η-pos-elim {zero} x Q q p = q
  η-pos-elim {suc n} x Q q nd-here = q
  
  μ-brs : ∀ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ)
    → {f : Frm X} {src : Src P f}
    → (brs : Dec {P = P} (Branch (Pd U)) src)
    → (p : Pos P src) → Branch U (src ⊚ p)
  μ-brs U brs p = [ lvs (brs ⊛ p) , μ U (br (brs ⊛ p)) ] 

  μ {zero} P s = s
  μ {suc n} U (lf tgt) = lf tgt
  μ {suc n} U (nd src tgt flr brs) =
    γ U flr (μ-brs U brs) 

  μ-pos {zero} P s p q = tt*
  μ-pos {suc n} U (nd src tgt flr brs) nd-here r =
    γ-inl U flr (μ-brs U brs) r
  μ-pos {suc n} U (nd src tgt flr brs) (nd-there p q) r =
    γ-inr U flr (μ-brs U brs) p (μ-pos U (br (brs ⊛ p)) q r)
  
  μ-fst {zero} P s p = tt*
  μ-fst {suc n} U (nd src tgt flr brs) =
    γ-pos-elim U flr (μ-brs U brs) _ (λ _ → nd-here)
      (λ p q → nd-there p (μ-fst U (br (brs ⊛ p)) q))
  
  μ-snd {zero} P s p = tt*
  μ-snd {suc n} U (nd src tgt flr brs) = 
    γ-pos-elim U flr (μ-brs U brs) _ (λ p → p)
      (λ p q → μ-snd U (br (brs ⊛ p)) q)
      
