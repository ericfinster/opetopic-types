{-# OPTIONS --no-positivity-check #-}
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

module Experimental.LessPositions.OpetopicType where

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)

  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ
  
  Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → Frm X → Type ℓ 

  {-# TERMINATING #-}
  Pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Type ℓ 

  Typ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s) → Frm X 

  _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s)
    → P (Typ s p)

  η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Src P f 

  η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Pos P (η P x)

  η-pos-elim : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (x : P f)
    → (Q : Pos P (η P x) → Type ℓ')
    → (q : Q (η-pos P x))
    → (p : Pos P (η P x)) → Q p

  μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → Src Q f 

  μ-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → (p : Pos P s)
    → (q : Pos Q (ϕ p))
    → Pos Q (μ Q s ϕ) 

  postulate

    μ-fst : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → Pos P s  

    μ-snd : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → Pos Q (ϕ (μ-fst Q s ϕ p))

  postulate

    -- Typing and Inhabitants of μ and η
    Typ-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → Typ (η P x) p ↦ f
    {-# REWRITE Typ-η #-}

    ⊚-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → η P x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    Typ-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → Typ (μ Q s ϕ) p ↦ Typ (ϕ (μ-fst Q s ϕ p)) (μ-snd Q s ϕ p)
    {-# REWRITE Typ-μ #-}

    ⊚-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → μ Q s ϕ ⊚ p ↦ ϕ (μ-fst Q s ϕ p) ⊚ μ-snd Q s ϕ p
    {-# REWRITE ⊚-μ #-}

    -- Laws for positions
    η-pos-elim-β : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → η-pos-elim x Q q (η-pos P x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

    μ-fst-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-fst Q s ϕ (μ-pos Q s ϕ p q) ↦ p 
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-snd Q s ϕ (μ-pos Q s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → μ-pos Q s ϕ (μ-fst Q s ϕ p) (μ-snd Q s ϕ p) ↦ p
    {-# REWRITE μ-pos-η #-}
    
    -- Monad Laws
    unit-left : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q : Frm X → Type ℓ)
      → (f : Frm X) (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Src Q f)
      → μ Q (η P x) ϕ ↦ ϕ (η-pos P x)
    {-# REWRITE unit-left #-}
    
    unit-right : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P s (λ p → η P (s ⊚ p)) ↦ s
    {-# REWRITE unit-right #-}
    
    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q R : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (ψ : (pq : Pos Q (μ Q s ϕ)) → Src R (Typ (μ Q s ϕ) pq))
      → μ R (μ Q s ϕ) ψ ↦ μ R s (λ p → μ R (ϕ p) (λ q → ψ (μ-pos Q s ϕ p q)))
    {-# REWRITE μ-assoc #-}

  smap : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ s p))
    → Src Q f
  smap Q s ϕ = μ Q s (λ p → η Q (ϕ p)) 

  smap-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ s p))
    → (p : Pos P s) → Pos Q (smap Q s ϕ)
  smap-pos Q s ϕ p = μ-pos Q s (λ p → η Q (ϕ p)) p (η-pos Q (ϕ p)) 

  smap-pos-inv : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ s p))
    → Pos Q (smap Q s ϕ) → Pos P s
  smap-pos-inv Q s ϕ p = μ-fst Q s (λ p → η Q (ϕ p)) p 

  -- Hmmm.  So the roundtrip is only definitionally the identity in
  -- one direction.  How could you fix this? 

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ tgt ∈ P f ] 
    Src P f

  module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
           (U : Frm (X , P) → Type ℓ) where

    data Pd : Frm (X , P) → Type ℓ

    record Branch (f : Frm X) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        stm : P f
        lvs : Src P f
        br : Pd (f , stm , lvs)

    open Branch public
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , tgt , η P tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , tgt , μ P brs (λ p → η P (stm (brs ⊚ p)))))
         → Pd (f , tgt , μ P brs (λ p → lvs (brs ⊚ p)))

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U (lf tgt) = Lift ⊥
  Pos {suc n} U (nd tgt brs flr) =
    Unit ⊎ (Σ[ p ∈ Pos (Branch U) brs ]
            Pos U (br (brs ⊚ p)))

  Typ {zero} s p = tt*
  Typ {suc n} {X = X , P} {P = U} (nd tgt brs flr) (inl _) =
    _ , tgt , μ P brs (λ p → η P (stm (brs ⊚ p)))
  Typ {suc n} (nd tgt brs flr) (inr (p , q)) = Typ (br (brs ⊚ p)) q

  _⊚_ {zero} s p = s
  _⊚_ {suc n} (nd tgt brs flr) (inl _) = flr
  _⊚_ {suc n} (nd tgt brs flr) (inr (p , q)) = br (brs ⊚ p) ⊚ q

  η {zero} P x = x
  η {suc n} {X = X , P} U {f = f , t , s} x = 
    let brs = μ (Branch U) s (λ p → η (Branch U)
          [ s ⊚ p , η P (s ⊚ p) , lf (s ⊚ p) ])
    in nd t brs x
    
  η-pos {zero} P x = tt*
  η-pos {suc n} U x = inl tt

  η-pos-elim {zero} x Q q p = q
  η-pos-elim {suc n} x Q q (inl tt) = q

  γ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ) 
    → {f : Frm X} {t : P f} {s : Src P f}
    → Pd U (f , t , s)
    → (ϕ : (p : Pos P s) → Σ[ lvs ∈ Src P (Typ s p) ]
                           Pd U (Typ s p , s ⊚ p , lvs))
    → Pd U (f , t , μ P s (λ p → fst (ϕ p)))
  γ {P = P} U (lf tgt) ϕ = snd (ϕ (η-pos P tgt))
  γ {P = P} U (nd tgt brs flr) ϕ =
    let ψ p = [ stm (brs ⊚ p)
              , μ P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q)))
              , γ U  (br (brs ⊚ p)) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q))
              ]                            
    in nd tgt (smap (Branch U) brs ψ) flr

  γ-inl : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ) 
    → {f : Frm X} {t : P f} {s : Src P f}
    → (θ : Pd U (f , t , s))
    → (ϕ : (p : Pos P s) → Σ[ lvs ∈ Src P (Typ s p) ]
                           Pd U (Typ s p , s ⊚ p , lvs))
    → Pos U θ → Pos U (γ U θ ϕ)
  γ-inl {P = P} U (nd tgt brs flr) ϕ (inl tt) = inl tt
  γ-inl {P = P} U (nd tgt brs flr) ϕ (inr (p , q)) =
    let ψ p = [ stm (brs ⊚ p)
              , μ P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q)))
              , γ U  (br (brs ⊚ p)) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q))
              ]
        p' = smap-pos (Branch U) brs ψ p 
    in inr (p' , γ-inl U (br (brs ⊚ p)) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q)) q)

  γ-inr : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ) 
    → {f : Frm X} {t : P f} {s : Src P f}
    → (θ : Pd U (f , t , s))
    → (ϕ : (p : Pos P s) → Σ[ lvs ∈ Src P (Typ s p) ]
                           Pd U (Typ s p , s ⊚ p , lvs))
    → (p : Pos P s) (q : Pos U (snd (ϕ p)))
    → Pos U (γ U θ ϕ)
  γ-inr {P = P} U (lf tgt) ϕ p q =
    η-pos-elim tgt (λ p → Pos U (snd (ϕ p)) → Pos U (snd (ϕ (η-pos P tgt)))) (λ x → x) p q
  γ-inr {P = P} U (nd tgt brs flr) ϕ pq r = 
    let p = μ-fst P brs (λ p' → lvs (brs ⊚ p')) pq
        q = μ-snd P brs (λ p' → lvs (brs ⊚ p')) pq
        ψ p = [ stm (brs ⊚ p)
              , μ P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q)))
              , γ U  (br (brs ⊚ p)) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q))
              ]
        p' = smap-pos (Branch U) brs ψ p 
    in inr (p' , γ-inr U (br (brs ⊚ p)) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q)) q r) 

  γ-pos-elim : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ) 
    → {f : Frm X} {t : P f} {s : Src P f}
    → (θ : Pd U (f , t , s))
    → (ϕ : (p : Pos P s) → Σ[ lvs ∈ Src P (Typ s p) ]
                           Pd U (Typ s p , s ⊚ p , lvs))
    → (X : Pos U (γ U θ ϕ) → Type ℓ')
    → (inl* : (p : Pos U θ) → X (γ-inl U θ ϕ p))
    → (inr* : (p : Pos P s) (q : Pos U (snd (ϕ p))) → X (γ-inr U θ ϕ p q))
    → (p : Pos U (γ U θ ϕ)) → X  p
  γ-pos-elim {P = P} U (lf tgt) ϕ X inl* inr* p = inr* (η-pos P tgt) p
  γ-pos-elim {P = P} U (nd tgt brs flr) ϕ X inl* inr* (inl tt) = inl* (inl tt)
  γ-pos-elim {P = P} U (nd tgt brs flr) ϕ X inl* inr* (inr (u , v)) = 
    let ψ p = [ stm (brs ⊚ p)
              , μ P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q)))
              , γ U  (br (brs ⊚ p)) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) p q))
              ]
        u' = smap-pos-inv (Branch U) brs ψ u
    in γ-pos-elim U (br (brs ⊚ u')) (λ q → ϕ (μ-pos P brs (λ p' → lvs (brs ⊚ p')) u' q))
        (λ q' → X (inr (u , q'))) {!!} {!!} v  

    -- (λ q' → inl* (inr (p' , q')))
    -- (λ p q → inr* (μ-pos P brs (λ p' → lvs (brs ⊚ p')) u' p) q)

  -- Ech.  The lack of η expansion at unit positions bites us again ....
  -- I guess this could be helped with a special rewrite for smap.
  -- But it's pretty icky, isn't it .... ?
  
  -- graftₒ-pos-elim (ndₒ 𝑝 𝑞 𝑟) 𝑡 X inl* inr* (inl tt)  = inl* (inl tt)
  -- graftₒ-pos-elim (ndₒ 𝑝 𝑞 𝑟) 𝑡 X inl* inr* (inr (u , v)) = 
  --   graftₒ-pos-elim (𝑟 u) (λ q → 𝑡 (pairₚ 𝑝 𝑞 u q)) 
  --     (λ q → X (inr (u , q)))
  --     (λ q → inl* (inr (u , q)))
  --     (λ p q → inr* (pairₚ 𝑝 𝑞 u p) q) v

  μ {zero} Q s ϕ = ϕ tt*
  μ {suc n} Q (lf tgt) ϕ = lf tgt
  μ {suc n} {X = X , P} {P = U₀} U (nd tgt brs flr) ϕ = 
    let w = ϕ (inl tt)
        δ p = η P (stm (brs ⊚ p))
    in γ U w (λ p → lvs (brs ⊚ (μ-fst P brs δ p)) ,
                    μ U (br (brs ⊚ (μ-fst P brs δ p)))
                        (λ q → ϕ (inr (μ-fst P brs δ p , q))))
                 
  -- Old version of μ
  μ' : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} {f : Frm Xₙ}
    → Src (Src Xₛₙ) f → Src Xₛₙ f
  μ' {Xₛₙ = Q} s = μ Q s (s ⊚_ )
