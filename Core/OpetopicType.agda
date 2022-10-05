{-# OPTIONS --no-positivity-check --no-termination-check --lossy-unification #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Core.Prelude

module Core.OpetopicType where

  --
  --  Opetopic Types
  --

  𝕆Type : (n : ℕ) (ℓ : Level)
    → Type (ℓ-suc ℓ)

  Frm : (n : ℕ) (ℓ : Level)
    → 𝕆Type n ℓ → Type ℓ 

  Pd : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → Frm n ℓ X → Type ℓ

  --
  --  Definitions of opeotpic types and frames
  --

  𝕆Type zero ℓ = 𝟙 (ℓ-suc ℓ)
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm n ℓ X) → Type ℓ)

  Frm zero ℓ X = 𝟙 ℓ
  Frm (suc n) ℓ (X , P) = 
    Σ[ f ∈ Frm n ℓ X ]
    Σ[ src ∈ Pd n ℓ X P f ] 
    P f

  --
  --  Positions, their types and inhabitants 
  --
  
  Pos : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    → Type ℓ 

  Typ : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    → (p : Pos n ℓ X P f s) → Frm n ℓ X 

  Ihb : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    → (p : Pos n ℓ X P f s)
    → P (Typ n ℓ X P f s p)

  --
  --  Monadic Structure
  --

  ν : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P Q : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
    → Pd n ℓ X Q f

  η : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (x : P f)
    → Pd n ℓ X P f 

  μ : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
    → Pd n ℓ X P f

  mapₒ : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P Q : Frm n ℓ X → Type ℓ)
    → (ϕ : {f : Frm n ℓ X} → P f → Q f)
    → (f : Frm n ℓ X) → Pd n ℓ X P f → Pd n ℓ X Q f
  mapₒ n ℓ X P Q ϕ f s =
    ν n ℓ X P Q f s
      (λ p → ϕ (Ihb n ℓ X P f s p))

  bindₒ : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P Q : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    → (ϕ : (p : Pos n ℓ X P f s) → Pd n ℓ X Q (Typ n ℓ X P f s p))
    → Pd n ℓ X Q f
  bindₒ n ℓ X P Q f s ϕ = μ n ℓ X Q f (ν n ℓ X P (Pd n ℓ X Q) f s ϕ)

  --
  --  Position Intro 
  --

  ν-pos : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P Q : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
    → Pos n ℓ X P f s → Pos n ℓ X Q f (ν n ℓ X P Q f s ϕ)

  η-pos : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (x : P f)
    → Pos n ℓ X P f (η n ℓ X P f x)

  μ-pos : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
    → (p : Pos n ℓ X (Pd n ℓ X P) f s)
    → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s p)
                       (Ihb n ℓ X (Pd n ℓ X P) f s p))
    → Pos n ℓ X P f (μ n ℓ X P f s)

  postulate

    γ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (t : P f)
      → (τ : Pd (suc n) ℓ (X , P) U (f , s , t))
      → (brs : (p : Pos n ℓ X P f s) → Σ[ lvs ∈ Pd n ℓ X P (Typ n ℓ X P f s p) ]
             Pd (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , lvs , Ihb n ℓ X P f s p))
      → Pd (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)

    γ-inl : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (t : P f)
      → (τ : Pd (suc n) ℓ (X , P) U (f , s , t))
      → (brs : (p : Pos n ℓ X P f s) → Σ[ lvs ∈ Pd n ℓ X P (Typ n ℓ X P f s p) ]
             Pd (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , lvs , Ihb n ℓ X P f s p))
      → (p : Pos (suc n) ℓ (X , P) U (f , s , t) τ)
      → Pos (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)
          (γ n ℓ X P U f s t τ brs)

    γ-inr : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (t : P f)
      → (τ : Pd (suc n) ℓ (X , P) U (f , s , t))
      → (brs : (p : Pos n ℓ X P f s) → Σ[ lvs ∈ Pd n ℓ X P (Typ n ℓ X P f s p) ]
             Pd (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , lvs , Ihb n ℓ X P f s p))
      → (p : Pos n ℓ X P f s)
      → (q : Pos (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , fst (brs p) , Ihb n ℓ X P f s p) (snd (brs p)))
      → Pos (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)
          (γ n ℓ X P U f s t τ brs)

    --
    --  Position Elim
    --

    ν-lift : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
      → Pos n ℓ X Q f (ν n ℓ X P Q f s ϕ) → Pos n ℓ X P f s

    η-pos-elim : (n : ℕ) (ℓ ℓ' : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (Q : Pos n ℓ X P f (η n ℓ X P f x) → Type ℓ')
      → (q : Q (η-pos n ℓ X P f x))
      → (p : Pos n ℓ X P f (η n ℓ X P f x)) → Q p

    μ-fst : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f s))
      → Pos n ℓ X (Pd n ℓ X P) f s

    μ-snd : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f s))
      → Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s (μ-fst n ℓ X P f s p))
                    (Ihb n ℓ X (Pd n ℓ X P) f s (μ-fst n ℓ X P f s p))

    γ-pos-elim : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (t : P f)
      → (τ : Pd (suc n) ℓ (X , P) U (f , s , t))
      → (brs : (p : Pos n ℓ X P f s) → Σ[ lvs ∈ Pd n ℓ X P (Typ n ℓ X P f s p) ]
             Pd (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , lvs , Ihb n ℓ X P f s p))
      → (ℓ' : Level)
      → (B : Pos (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)
                (γ n ℓ X P U f s t τ brs) → Type ℓ')
      → (inl* : (p : Pos (suc n) ℓ (X , P) U (f , s , t) τ) → B (γ-inl n ℓ X P U f s t τ brs p))
      → (inr* :   (p : Pos n ℓ X P f s)
                → (q : Pos (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , fst (brs p) , Ihb n ℓ X P f s p) (snd (brs p)))
                → B (γ-inr n ℓ X P U f s t τ brs p q))
      → (p : Pos (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)
                (γ n ℓ X P U f s t τ brs)) → B p

  --
  --  Pasting Diagrams and their Positions 
  --
  module _ (n : ℕ) (ℓ : Level)
    (X : 𝕆Type n ℓ)
    (P : Frm n ℓ X → Type ℓ)
    (U : Frm (suc n) ℓ (X , P) → Type ℓ) where

    data Tr : Frm (suc n) ℓ (X , P) → Type ℓ

    Branch : Frm n ℓ X → Type ℓ
    Branch f = Σ[ t ∈ P f ]
               Σ[ s ∈ Pd n ℓ X P f ]
               Tr (f , s , t)

    Forest : Frm n ℓ X → Type ℓ
    Forest = Pd n ℓ X Branch

    branch-stm : (frm : Frm n ℓ X) (brs : Forest frm)
      → (p : Pos n ℓ X Branch frm brs)
      → P (Typ n ℓ X Branch frm brs p)
    branch-stm frm brs p = Ihb n ℓ X Branch frm brs p .fst

    branch-lvs : (frm : Frm n ℓ X) (brs : Forest frm)
      → (p : Pos n ℓ X Branch frm brs)
      → Pd n ℓ X P (Typ n ℓ X Branch frm brs p)
    branch-lvs frm brs p = Ihb n ℓ X Branch frm brs p .snd .fst
      
    branch-frm : (frm : Frm n ℓ X) (brs : Forest frm)
      → (p : Pos n ℓ X Branch frm brs)
      → Frm (suc n) ℓ (X , P)
    branch-frm frm brs p =
      (Typ n ℓ X Branch frm brs p ,
       branch-lvs frm brs p , 
       branch-stm frm brs p)
       
    branch-tr : (frm : Frm n ℓ X) (brs : Forest frm)
      → (p : Pos n ℓ X Branch frm brs)
      → Tr (branch-frm frm brs p)
    branch-tr frm brs p = 
      Ihb n ℓ X Branch frm brs p .snd .snd

    understory : (frm : Frm n ℓ X) → Forest frm → Pd n ℓ X P frm
    understory frm brs = mapₒ n ℓ X Branch P fst frm brs

    understory-lift : (frm : Frm n ℓ X) (brs : Forest frm)
      → (p : Pos n ℓ X P frm (understory frm brs))
      → Pos n ℓ X Branch frm brs
    understory-lift frm brs p =
      ν-lift n ℓ X Branch P frm brs
        (λ q → fst (Ihb n ℓ X Branch frm brs q)) p 

    canopy : (frm : Frm n ℓ X) → Forest frm → Pd n ℓ X P frm
    canopy frm brs = μ n ℓ X P frm (ν n ℓ X Branch (Pd n ℓ X P) frm brs
      (λ p → fst (snd (Ihb n ℓ X Branch frm brs p))))

    data Tr where

      lf : (frm : Frm n ℓ X) (tgt : P frm)
         → Tr (frm , η n ℓ X P frm tgt , tgt) 

      nd : (frm : Frm n ℓ X) (tgt : P frm)
         → (brs : Pd n ℓ X Branch frm)
         → (flr : U (frm , understory frm brs , tgt)) 
         → Tr (frm , canopy frm brs , tgt)

    data TrPos : (f : Frm (suc n) ℓ (X , P)) → Tr f → Type ℓ where

      nd-here : {frm : Frm n ℓ X} {tgt : P frm}
        → {brs : Pd n ℓ X Branch frm}
        → {flr : U (frm , understory frm brs , tgt)}
        → TrPos (frm , canopy frm brs , tgt) (nd frm tgt brs flr)

      nd-there : {frm : Frm n ℓ X} {tgt : P frm}
        → {brs : Pd n ℓ X Branch frm}
        → {flr : U (frm , understory frm brs , tgt)}
        → (p : Pos n ℓ X Branch frm brs)
        → (q : TrPos (branch-frm frm brs p) (branch-tr frm brs p))
        → TrPos (frm , canopy frm brs , tgt) (nd frm tgt brs flr)

  Pd zero ℓ X P f = P ●
  Pd (suc n) ℓ (X , P) U = Tr n ℓ X P U

  Pos zero ℓ X P f s = 𝟙 ℓ
  Pos (suc n) ℓ (X , P) U = TrPos n ℓ X P U
  
  Typ zero ℓ X P f s p = ●
  Typ (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) nd-here =
    frm , understory n ℓ X P U frm brs , tgt 
  Typ (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) (nd-there p q) = 
    Typ (suc n) ℓ (X , P) U
      (branch-frm n ℓ X P U frm brs p)
      (branch-tr n ℓ X P U frm brs p) q
  
  Ihb zero ℓ X P f s p = s
  Ihb (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) nd-here = flr
  Ihb (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) (nd-there p q) = 
    Ihb (suc n) ℓ (X , P) U
      (branch-frm n ℓ X P U frm brs p)
      (branch-tr n ℓ X P U frm brs p) q

  postulate

    --
    --  Position Computation
    --

    η-pos-elim-β : (n : ℕ) (ℓ ℓ' : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (Q : Pos n ℓ X P f (η n ℓ X P f x) → Type ℓ')
      → (q : Q (η-pos n ℓ X P f x))
      → η-pos-elim n ℓ ℓ' X P f x Q q (η-pos n ℓ X P f x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

    ν-lift-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
      → (p : Pos n ℓ X P f s)
      → ν-lift n ℓ X P Q f s ϕ (ν-pos n ℓ X P Q f s ϕ p) ↦ p
    {-# REWRITE ν-lift-β #-} 

    ν-lift-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
      → (p : Pos n ℓ X Q f (ν n ℓ X P Q f s ϕ))
      → ν-pos n ℓ X P Q f s ϕ (ν-lift n ℓ X P Q f s ϕ p) ↦ p
    {-# REWRITE ν-lift-η #-} 

    μ-fst-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X (Pd n ℓ X P) f s)
      → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s p)
                         (Ihb n ℓ X (Pd n ℓ X P) f s p))
      → μ-fst n ℓ X P f s (μ-pos n ℓ X P f s p q) ↦ p
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X (Pd n ℓ X P) f s)
      → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s p)
                         (Ihb n ℓ X (Pd n ℓ X P) f s p))
      → μ-snd n ℓ X P f s (μ-pos n ℓ X P f s p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f s))
      → μ-pos n ℓ X P f s (μ-fst n ℓ X P f s p)
                          (μ-snd n ℓ X P f s p) ↦ p
    {-# REWRITE μ-pos-η #-}

    γ-pos-elim-inl-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (t : P f)
      → (τ : Pd (suc n) ℓ (X , P) U (f , s , t))
      → (brs : (p : Pos n ℓ X P f s) → Σ[ lvs ∈ Pd n ℓ X P (Typ n ℓ X P f s p) ]
             Pd (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , lvs , Ihb n ℓ X P f s p))
      → (ℓ' : Level)
      → (B : Pos (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)
                (γ n ℓ X P U f s t τ brs) → Type ℓ')
      → (inl* : (p : Pos (suc n) ℓ (X , P) U (f , s , t) τ) → B (γ-inl n ℓ X P U f s t τ brs p))
      → (inr* :   (p : Pos n ℓ X P f s)
                → (q : Pos (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , fst (brs p) , Ihb n ℓ X P f s p) (snd (brs p)))
                → B (γ-inr n ℓ X P U f s t τ brs p q))
      → (p : Pos (suc n) ℓ (X , P) U (f , s , t) τ)
      → γ-pos-elim n ℓ X P U f s t τ brs ℓ' B inl* inr* (γ-inl n ℓ X P U f s t τ brs p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (t : P f)
      → (τ : Pd (suc n) ℓ (X , P) U (f , s , t))
      → (brs : (p : Pos n ℓ X P f s) → Σ[ lvs ∈ Pd n ℓ X P (Typ n ℓ X P f s p) ]
             Pd (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , lvs , Ihb n ℓ X P f s p))
      → (ℓ' : Level)
      → (B : Pos (suc n) ℓ (X , P) U (f , bindₒ n ℓ X P P f s (λ p → fst (brs p)) , t)
                (γ n ℓ X P U f s t τ brs) → Type ℓ')
      → (inl* : (p : Pos (suc n) ℓ (X , P) U (f , s , t) τ) → B (γ-inl n ℓ X P U f s t τ brs p))
      → (inr* :   (p : Pos n ℓ X P f s)
                → (q : Pos (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , fst (brs p) , Ihb n ℓ X P f s p) (snd (brs p)))
                → B (γ-inr n ℓ X P U f s t τ brs p q))
      → (p : Pos n ℓ X P f s)
      → (q : Pos (suc n) ℓ (X , P) U (Typ n ℓ X P f s p , fst (brs p) , Ihb n ℓ X P f s p) (snd (brs p)))
      → γ-pos-elim n ℓ X P U f s t τ brs ℓ' B inl* inr* (γ-inr n ℓ X P U f s t τ brs p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}

    --
    --  Typing and Inhabitants
    --

    Typ-ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
      → (p : Pos n ℓ X Q f (ν n ℓ X P Q f s ϕ))
      → Typ n ℓ X Q f (ν n ℓ X P Q f s ϕ) p ↦
        Typ n ℓ X P f s (ν-lift n ℓ X P Q f s ϕ p)
    {-# REWRITE Typ-ν #-}

    Ihb-ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
      → (p : Pos n ℓ X Q f (ν n ℓ X P Q f s ϕ))
      → Ihb n ℓ X Q f (ν n ℓ X P Q f s ϕ) p ↦ ϕ (ν-lift n ℓ X P Q f s ϕ p)
    {-# REWRITE Ihb-ν #-}

    Typ-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (p : Pos n ℓ X P f (η n ℓ  X P f x))
      → Typ n ℓ X P f (η n ℓ X P f x) p ↦ f
    {-# REWRITE Typ-η #-}

    Ihb-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (p : Pos n ℓ X P f (η n ℓ X P f x))
      → Ihb n ℓ X P f (η n ℓ X P f x) p ↦ x
    {-# REWRITE Ihb-η #-}

    Typ-μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f s))
      → Typ n ℓ X P f (μ n ℓ X P f s) p ↦
        Typ n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s (μ-fst n ℓ X P f s p))
                (Ihb n ℓ X (Pd n ℓ X P) f s (μ-fst n ℓ X P f s p)) (μ-snd n ℓ X P f s p) 
    {-# REWRITE Typ-μ #-}

    Ihb-μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f s))
      → Ihb n ℓ X P f (μ n ℓ X P f s) p ↦
        Ihb n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s (μ-fst n ℓ X P f s p))
                  (Ihb n ℓ X (Pd n ℓ X P) f s (μ-fst n ℓ X P f s p)) (μ-snd n ℓ X P f s p) 
    {-# REWRITE Ihb-μ #-}

    --
    --  Functoriality of ν 
    --

    ν-id : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → ν n ℓ X P P f s (Ihb n ℓ X P f s) ↦ s
    {-# REWRITE ν-id #-}
    
    ν-ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q R : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f s) → Q (Typ n ℓ X P f s p))
      → (ψ : (p : Pos n ℓ X Q f (ν n ℓ X P Q f s ϕ))
               → R (Typ n ℓ X Q f (ν n ℓ X P Q f s ϕ) p))
      → ν n ℓ X Q R f (ν n ℓ X P Q f s ϕ) ψ ↦
        ν n ℓ X P R f s (λ p → ψ (ν-pos n ℓ X P Q f s ϕ p))
    {-# REWRITE ν-ν #-} 

    -- 
    -- Naturality Laws
    --
      
    ν-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (ϕ : (p : Pos n ℓ X P f (η n ℓ X P f x)) → Q f)
      → ν n ℓ X P Q f (η n ℓ X P f x) ϕ ↦
        η n ℓ X Q f (ϕ (η-pos n ℓ X P f x)) 
    {-# REWRITE ν-η #-}

    ν-μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
      → (ϕ : (p : Pos n ℓ X P f (μ n ℓ X P f s))
           → Q (Typ n ℓ X P f (μ n ℓ X P f s) p))
      → ν n ℓ X P Q f (μ n ℓ X P f s) ϕ ↦
        μ n ℓ X Q f (ν n ℓ X (Pd n ℓ X P) (Pd n ℓ X Q) f s
          (λ p → ν n ℓ X P Q (Typ n ℓ X (Pd n ℓ X P) f s p)
                         (Ihb n ℓ X (Pd n ℓ X P) f s p)
            (λ q → ϕ (μ-pos n ℓ X P f s p q)))) 
    {-# REWRITE ν-μ #-}

    --
    -- Monad Laws
    --

    μ-unit-l : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → μ n ℓ X P f (η n ℓ X (Pd n ℓ X P) f s) ↦ s
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
      → μ n ℓ X P f (ν n ℓ X P (Pd n ℓ X P) f s
          (λ p → η n ℓ X P (Typ n ℓ X P f s p) (Ihb n ℓ X P f s p))) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X (Pd n ℓ X P)) f)
      → μ n ℓ X P f (μ n ℓ X (Pd n ℓ X P) f s) ↦
        μ n ℓ X P f (ν n ℓ X (Pd n ℓ X (Pd n ℓ X P)) (Pd n ℓ X P) f s
          (λ p → μ n ℓ X P (Typ n ℓ X (Pd n ℓ X (Pd n ℓ X P)) f s p)
                       (Ihb n ℓ X (Pd n ℓ X (Pd n ℓ X P)) f s p))) 
    {-# REWRITE μ-assoc #-}

    --
    -- Position Compatibilities
    --

    -- In fact, I now realize that there are really a lot of these
    -- that you are missing: for every equation involving μ, η and ν,
    -- there needs to be a corresponding equation for both the intro
    -- and the elim of their positions.

    -- You could put these additional equalities in another module,
    -- seeing as how they are not needed to finish the definition.

    --   ν-pos-id : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (p : Pos n ℓ X P s)
    --     → ν-pos {Q = P} s (_⊚_ s) p ↦ p
    --   {-# REWRITE ν-pos-id #-}

    --   ν-lift-id : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (p : Pos n ℓ X P s)
    --     → ν-lift {Q = P} s (_⊚_ s) p ↦ p 
    --   {-# REWRITE ν-lift-id #-}

    --   ν-pos-comp : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P Q R : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    --     → (ϕ : (p : Pos n ℓ X P s) → Q (Typ n ℓ X P f s p))
    --     → (ψ : (p : Pos Q (ν X P Q f s ϕ)) → R (Typ Q (ν X P Q f s ϕ) p))
    --     → (p : Pos n ℓ X P s)
    --     → ν-pos {Q = R} (ν {Q = Q} s ϕ) ψ (ν-pos s ϕ p) ↦
    --       ν-pos {Q = R} s (λ p → ψ (ν-pos s ϕ p)) p 
    --   {-# REWRITE ν-pos-comp #-}

    --   ν-lift-comp : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P Q R : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    --     → (ϕ : (p : Pos n ℓ X P s) → Q (Typ n ℓ X P f s p))
    --     → (ψ : (p : Pos Q (ν X P Q f s ϕ)) → R (Typ Q (ν X P Q f s ϕ) p))
    --     → (p : Pos R (ν {Q = R} (ν X P Q f s ϕ) ψ))
    --     → ν-lift {Q = Q} s ϕ (ν-lift (ν X P Q f s ϕ) ψ p) ↦
    --       ν-lift {Q = R} s (λ p → ψ (ν-pos s ϕ p)) p 
    --   {-# REWRITE ν-lift-comp #-}


  canopy-pos : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (U : Frm (suc n) ℓ (X , P) → Type ℓ)
    → (frm : Frm n ℓ X) (brs : Forest n ℓ X P U frm)
    → (p : Pos n ℓ X (Branch n ℓ X P U) frm brs)
    → (q : Pos n ℓ X P (Typ n ℓ X (Branch n ℓ X P U) frm brs p) (branch-lvs n ℓ X P U frm brs p))
    → Pos n ℓ X P frm (canopy n ℓ X P U frm brs)
  canopy-pos n ℓ X P U frm brs p q =
    μ-pos n ℓ X P frm (ν n ℓ X (Branch n ℓ X P U) (Pd n ℓ X P) frm brs (branch-lvs n ℓ X P U frm brs))
                      (ν-pos n ℓ X (Branch n ℓ X P U) (Pd n ℓ X P) frm brs (branch-lvs n ℓ X P U frm brs) p) q 


  --
  --  Monadic operator definitions 
  --

  ν zero ℓ X P Q f s ϕ = ϕ ●
  ν (suc n) ℓ X P Q ._ (lf frm tgt) ϕ = lf frm tgt
  ν (suc n) ℓ (X , P) U V ._ (nd frm tgt brs flr) ϕ =
    nd frm tgt (ν n ℓ X (Branch n ℓ X P U) (Branch n ℓ X P V) frm brs
                 (λ p → branch-stm n ℓ X P U frm brs p , 
                        branch-lvs n ℓ X P U frm brs p ,
                        ν (suc n) ℓ (X , P) U V
                          (branch-frm n ℓ X P U frm brs p)
                          (branch-tr n ℓ X P U frm brs p)
                          (λ q → ϕ (nd-there p q)))) (ϕ nd-here)

  η zero ℓ X P f x = x
  η (suc n) ℓ (X , P) U (frm , src , tgt) u =
    nd frm tgt (ν n ℓ X P (Branch n ℓ X P U) frm src
                  (λ p → Ihb n ℓ X P frm src p ,
                         η n ℓ X P (Typ n ℓ X P frm src p)
                                   (Ihb n ℓ X P frm src p) ,
                         lf (Typ n ℓ X P frm src p)
                            (Ihb n ℓ X P frm src p))) u

  μ zero ℓ X P f s = s
  μ (suc n) ℓ X P       ._ (lf frm tgt) = lf frm tgt
  μ (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) =
    γ n ℓ X P U frm (understory n ℓ X P (Tr n ℓ X P U) frm brs) tgt flr
      (λ p → let p' = understory-lift n ℓ X P (Tr n ℓ X P U) frm brs p in
             branch-lvs n ℓ X P (Tr n ℓ X P U) frm brs p' ,
             μ (suc n) ℓ (X , P) U 
               (branch-frm n ℓ X P (Tr n ℓ X P U) frm brs p')                                       
               (branch-tr n ℓ X P (Tr n ℓ X P U) frm brs p'))


  -- γ n ℓ X P U frm .(η n ℓ X P frm tgt) tgt (lf .frm .tgt) brs =
  --   brs (η-pos n ℓ X P frm tgt) .snd
  -- γ n ℓ X P U frm .(canopy n ℓ X P U frm lbrs) tgt (nd .frm .tgt lbrs flr) brs =
  --   nd frm tgt (ν n ℓ X (Branch n ℓ X P U) (Branch n ℓ X P U) frm lbrs
  --                 (λ p → branch-stm n ℓ X P U frm lbrs p ,
  --                        μ n ℓ X P (Typ n ℓ X (Branch n ℓ X P U) frm lbrs p)
  --                          (ν n ℓ X P (Pd n ℓ X P) (Typ n ℓ X (Branch n ℓ X P U) frm lbrs p)
  --                                                  (branch-lvs n ℓ X P U frm lbrs p)
  --                                                  (λ q → fst (brs (canopy-pos n ℓ X P U frm lbrs p q)))) ,
  --                        γ n ℓ X P U (Typ n ℓ X (Branch n ℓ X P U) frm lbrs p)
  --                                    (branch-lvs n ℓ X P U frm lbrs p)
  --                                    (branch-stm n ℓ X P U frm lbrs p)
  --                                    (branch-tr n ℓ X P U frm lbrs p)
  --                                    (λ q → brs (canopy-pos n ℓ X P U frm lbrs p q)))) flr

  --
  --  Position intro definitions
  --

  ν-pos zero ℓ X P Q f s ϕ p = p
  ν-pos (suc n) ℓ (X , P) U V ._ (nd frm tgt brs flr) ϕ nd-here = nd-here
  ν-pos (suc n) ℓ (X , P) U V ._ (nd frm tgt brs flr) ϕ (nd-there p q) =
    nd-there (ν-pos n ℓ X (Branch n ℓ X P U) (Branch n ℓ X P V) frm brs
                -- name the recursive call? 
                (λ p₁ → branch-stm n ℓ X P U frm brs p₁ ,
                        branch-lvs n ℓ X P U frm brs p₁ ,
                        ν (suc n) ℓ (X , P) U V (branch-frm n ℓ X P U frm brs p₁)
                        (branch-tr n ℓ X P U frm brs p₁) (λ q₁ → ϕ (nd-there p₁ q₁))) p)
             (ν-pos (suc n) ℓ (X , P) U V  (branch-frm n ℓ X P U frm brs p)
                                           (branch-tr n ℓ X P U frm brs p)
                                           (λ q → ϕ (nd-there p q)) q)


  η-pos zero ℓ X P f x = ●
  η-pos (suc n) ℓ (X , P) U f x = nd-here

  -- μ-pos : (n : ℕ) (ℓ : Level)
  --   → (X : 𝕆Type n ℓ)
  --   → (P : Frm n ℓ X → Type ℓ)
  --   → (f : Frm n ℓ X) (s : Pd n ℓ X (Pd n ℓ X P) f)
  --   → (p : Pos n ℓ X (Pd n ℓ X P) f s)
  --   → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f s p)
  --                      (Ihb n ℓ X (Pd n ℓ X P) f s p))
  --   → Pos n ℓ X P f (μ n ℓ X P f s)
  μ-pos zero ℓ X P f s p q = ●
  μ-pos (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) nd-here r = {!!}
  μ-pos (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) (nd-there p q) r = {!!}
  
  -- μ-pos {zero} P s p q = tt*
  -- μ-pos {suc n} U (nd src tgt flr brs) nd-here r =
  --   γ-inl U flr (μ-brs U brs) r
  -- μ-pos {suc n} U (nd src tgt flr brs) (nd-there p q) r =
  --   γ-inr U flr (μ-brs U brs) p (μ-pos U (br (brs ⊛ p)) q r)

  -- γ-inl (nd src tgt flr lbrs) brs nd-here = nd-here
  -- γ-inl (nd src tgt flr lbrs) brs (nd-there p q) =
  --   nd-there p (γ-inl (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q)) q) 

  -- γ-inr (lf tgt) brs p q = 
  --   η-pos-elim tgt (λ p → TrPos (br (brs p)) → TrPos (br (brs (η-pos P tgt)))) (λ x → x) p q
  -- γ-inr (nd src tgt flr lbrs) brs pq r = 
  --   let p = canopy-fst lbrs pq
  --       q = canopy-snd lbrs pq
  --   in nd-there p (γ-inr (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q)) q r)

  --
  --  Position elim definitions 
  --
  
  -- ν-lift {zero} s ϕ p = tt*
  -- ν-lift {suc n} (nd src tgt flr brs) ϕ nd-here = nd-here
  -- ν-lift {suc n} (nd src tgt flr brs) ϕ (nd-there p q) =
  --   nd-there p (ν-lift (br (brs ⊛ p)) (λ q → ϕ (nd-there p q)) q)

  -- η-pos-elim {zero} x Q q p = q
  -- η-pos-elim {suc n} x Q q nd-here = q
  
  -- μ-fst {zero} P s p = tt*
  -- μ-fst {suc n} U (nd src tgt flr brs) =
  --   γ-pos-elim U flr (μ-brs U brs) _ (λ _ → nd-here)
  --     (λ p q → nd-there p (μ-fst U (br (brs ⊛ p)) q))

  -- μ-snd {zero} P s p = tt*
  -- μ-snd {suc n} U (nd src tgt flr brs) = 
  --   γ-pos-elim U flr (μ-brs U brs) _ (λ p → p)
  --     (λ p q → μ-snd U (br (brs ⊛ p)) q)

  -- γ-pos-elim (lf tgt) brs B inl* inr* p = inr* (η-pos P tgt) p
  -- γ-pos-elim (nd src tgt flr lbrs) brs B inl* inr* nd-here = inl* nd-here
  -- γ-pos-elim (nd src tgt flr lbrs) brs B inl* inr* (nd-there u v) = 
  --   γ-pos-elim (br (lbrs ⊛ u)) (λ q → brs (canopy-pos lbrs u q))
  --      (λ v' → B (nd-there u v')) (λ q → inl* (nd-there u q))
  --      (λ q → inr* (canopy-pos lbrs u q)) v

