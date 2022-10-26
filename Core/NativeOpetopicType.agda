{-# OPTIONS --opetopic-types --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Core.Prelude

module Core.NativeOpetopicType where

  --
  --  Opetopic Types
  --

  𝕆Type : (ℓ : Level) (n : ℕ) 
    → Type (ℓ-suc ℓ)
    
  {-# BUILTIN OPETOPICTYPE 𝕆Type #-}
    
  --
  --  Polynomial Structure
  --

  Frm : (ℓ : Level) (n : ℕ) 
    → 𝕆Type ℓ n → Type ℓ 

  {-# BUILTIN FRM Frm #-}

  Cns : (ℓ : Level) (n : ℕ) 
    → (X : 𝕆Type ℓ n)
    → Frm ℓ n X → Type ℓ

  {-# BUILTIN SRC Cns #-}

  Pos : (ℓ : Level) (n : ℕ)
    → (X : 𝕆Type ℓ n)
    → (i : Frm ℓ n X) (c : Cns ℓ n X i)
    → Type ℓ

  {-# BUILTIN POS Pos #-}

  Typ : (ℓ : Level) (n : ℕ)
    → (X : 𝕆Type ℓ n)
    → (i : Frm ℓ n X) (c : Cns ℓ n X i)
    → (p : Pos ℓ n X i c) → Frm ℓ n X 

  {-# BUILTIN TYP Typ #-}

  postulate

    --
    --  Monadic Structure
    --

    η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X)
      → Cns ℓ n X i

    μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → Cns ℓ n X i 

    --
    --  Position Intro
    --

    η-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X)
      → Pos ℓ n X i (η ℓ n X i)

    μ-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → Pos ℓ n X i (μ ℓ n X i c δ)

    --
    --  Position Elim
    --
    
    μ-fst : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Pos ℓ n X i c
      
    μ-snd : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Pos ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p))
          (δ (μ-fst ℓ n X i c δ p)) 

  --
  --  Native Bindings 
  --
  
  {-# BUILTIN UNT η #-}
  {-# BUILTIN SUBST μ #-}
  {-# BUILTIN UNTPOS η-pos #-}
  {-# BUILTIN SUBSTPOS μ-pos #-}
  {-# BUILTIN SUBSTFST μ-fst #-}
  {-# BUILTIN SUBSTSND μ-snd #-}

  postulate

    --
    --  Position Computation Rules 
    --
    
    μ-fst-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → μ-fst ℓ n X i c δ (μ-pos ℓ n X i c δ p q) ↦ p
    {-# REWRITE μ-fst-β #-}
    
    μ-snd-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → μ-snd ℓ n X i c δ (μ-pos ℓ n X i c δ p q) ↦ q
    {-# REWRITE μ-snd-β #-}


    --
    --  Position Typing Rules
    --

    Typ-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X)
      → (p : Pos ℓ n X i (η ℓ n X i))
      → Typ ℓ n X i (η ℓ n X i) p ↦ i
    {-# REWRITE Typ-η #-}

    Typ-μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Typ ℓ n X i (μ ℓ n X i c δ) p ↦
        Typ ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p))
          (δ (μ-fst ℓ n X i c δ p)) (μ-snd ℓ n X i c δ p)
    {-# REWRITE Typ-μ #-}

    --
    --  Left Unit Law
    --

    μ-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Cns ℓ n X i)
      → μ ℓ n X i (η ℓ n X i) δ ↦ δ (η-pos ℓ n X i)
    {-# REWRITE μ-unit-l #-}

    μ-pos-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Cns ℓ n X i)
      → (p : Pos ℓ n X i (η ℓ n X i)) (q : Pos ℓ n X i (δ (η-pos ℓ n X i)))
      → μ-pos ℓ n X i (η ℓ n X i) δ p q ↦ q
    {-# REWRITE μ-pos-unit-l #-}

    μ-fst-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Cns ℓ n X i)
      → (p : Pos ℓ n X i (μ ℓ n X i (η ℓ n X i) δ))
      → μ-fst ℓ n X i (η ℓ n X i) δ p ↦ η-pos ℓ n X i
    {-# REWRITE μ-fst-unit-l #-}

    μ-snd-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Cns ℓ n X i)
      → (p : Pos ℓ n X i (μ ℓ n X i (η ℓ n X i) δ))
      → μ-snd ℓ n X i (η ℓ n X i) δ p ↦ p
    {-# REWRITE μ-snd-unit-l #-}

    --
    --  Right Unit Law
    --

    μ-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → μ ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) ↦ c
    {-# REWRITE μ-unit-r #-} 

    μ-pos-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i) (p : Pos ℓ n X i c)
      → (q : Pos ℓ n X (Typ ℓ n X i c p) (η ℓ n X (Typ ℓ n X i c p)))
      → μ-pos ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) p q ↦ p
    {-# REWRITE μ-pos-unit-r #-}

    μ-fst-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i) 
      → (p : Pos ℓ n X i (μ ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p))))
      → μ-fst ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) p ↦ p 
    {-# REWRITE μ-fst-unit-r #-}

    μ-snd-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i) 
      → (p : Pos ℓ n X i (μ ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p))))
      → μ-snd ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) p ↦
        η-pos ℓ n X (Typ ℓ n X i c p)
    {-# REWRITE μ-snd-unit-r #-}

    --
    --  Associative Law
    --

    μ-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Cns ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → μ ℓ n X i (μ ℓ n X i c δ) ϵ ↦
        μ ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                    (λ q → ϵ (μ-pos ℓ n X i c δ p q)))
    {-# REWRITE μ-assoc #-} 

    μ-pos-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Cns ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → (q : Pos ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p) (ϵ p))
      → μ-pos ℓ n X i (μ ℓ n X i c δ) ϵ p q ↦
        μ-pos ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                        (λ q → ϵ (μ-pos ℓ n X i c δ p q)))
                        (μ-fst ℓ n X i c δ p)
                        (μ-pos ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p)) (δ (μ-fst ℓ n X i c δ p))
                            (λ q → ϵ (μ-pos ℓ n X i c δ (μ-fst ℓ n X i c δ p) q))
                            (μ-snd ℓ n X i c δ p) q)
    {-# REWRITE μ-pos-assoc #-}

    μ-fst-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Cns ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → (pqr : Pos ℓ n X i (μ ℓ n X i (μ ℓ n X i c δ) ϵ))
      → μ-fst ℓ n X i (μ ℓ n X i c δ) ϵ pqr ↦
        let p = μ-fst ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr 
            qr = μ-snd ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr
            q = μ-fst ℓ n X (Typ ℓ n X i c p) (δ p) (λ q → ϵ (μ-pos ℓ n X i c δ p q)) qr
        in μ-pos ℓ n X i c δ p q 
    {-# REWRITE μ-fst-assoc #-} 

    μ-snd-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Cns ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → (pqr : Pos ℓ n X i (μ ℓ n X i (μ ℓ n X i c δ) ϵ))
      → μ-snd ℓ n X i (μ ℓ n X i c δ) ϵ pqr ↦
        let p = μ-fst ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr 
            qr = μ-snd ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr
        in μ-snd ℓ n X (Typ ℓ n X i c p) (δ p) (λ q → ϵ (μ-pos ℓ n X i c δ p q)) qr
    {-# REWRITE μ-snd-assoc #-} 
  
  --
  --  Implementations 
  --

  𝕆Type ℓ zero = 𝟙 (ℓ-suc ℓ)
  𝕆Type ℓ (suc n) =
    Σ[ X ∈ 𝕆Type ℓ n ]
    (Frm ℓ n X → Type ℓ)

  Src : (ℓ : Level) (n : ℕ) 
    → (X : 𝕆Type ℓ n)
    → (P : Frm ℓ n X → Type ℓ)
    → Frm ℓ n X → Type ℓ
  Src ℓ n X P f =
    Σ[ c ∈ Cns ℓ n X f ]
    ((p : Pos ℓ n X f c) → P (Typ ℓ n X f c p))

  Frm ℓ zero X = 𝟙 ℓ 
  Frm ℓ (suc n) (X , P) =
    Σ[ f ∈ Frm ℓ n X ]
    Σ[ t ∈ P f ] 
    Src ℓ n X P f 

  Forest : ∀ {ℓ n X}
    → (P : Frm ℓ n X → Type ℓ)
    → (f : Frm ℓ n X)
    → Src ℓ n X P f → Type ℓ
  Forest {ℓ} {n} {X} P f (c , δ) =
    (p : Pos ℓ n X f c) → 
      Σ[ s ∈ Src ℓ n X P (Typ ℓ n X f c p) ]
      Cns ℓ (suc n) (X , P) (Typ ℓ n X f c p , δ p , s)

  ηs : ∀ {ℓ n X}
    → (P : Frm ℓ n X → Type ℓ)
    → (f : Frm ℓ n X) (t : P f)
    → Src ℓ n X P f
  ηs {ℓ} {n} {X} P f t =
    η ℓ n X f , λ _ → t 

  μs : ∀ {ℓ n X}
    → (P : Frm ℓ n X → Type ℓ)
    → (f : Frm ℓ n X) (c : Cns ℓ n X f)
    → (ψ : (p : Pos ℓ n X f c) → Src ℓ n X P (Typ ℓ n X f c p))
    → Src ℓ n X P f
  μs {ℓ} {n} {X} P f c ψ =
    μ ℓ n X f c (λ p → fst (ψ p)) ,
    (λ p → snd (ψ (μ-fst ℓ n X f c (λ p → fst (ψ p)) p))
                  (μ-snd ℓ n X f c (λ p → fst (ψ p)) p))

  data Web (ℓ : Level) (n : ℕ) 
      (X : 𝕆Type ℓ n)
      (P : Frm ℓ n X → Type ℓ)
    : Frm ℓ (suc n) (X , P) → Type ℓ where

    lf : (f : Frm ℓ n X) (t : P f)
       → Web ℓ n X P (f , t , ηs P f t)

    nd : (f : Frm ℓ n X) (t : P f) 
       → (s : Src ℓ n X P f) (φ : Forest P f s)
       → Web ℓ n X P (f , t , μs P f (fst s) (λ p → fst (φ p)))

  Cns ℓ zero X f = 𝟙 ℓ
  Cns ℓ (suc n) (X , P) f = Web ℓ n X P f

  data WebPos (ℓ : Level) (n : ℕ) 
      (X : 𝕆Type ℓ n)
      (P : Frm ℓ n X → Type ℓ)
    : (f : Frm ℓ (suc n) (X , P)) → Web ℓ n X P f → Type ℓ where

    nd-here : (f : Frm ℓ n X) (t : P f) 
      → (s : Src ℓ n X P f) (φ : Forest P f s)
      → WebPos ℓ n X P (f , t , μs P f (fst s) (λ p → fst (φ p))) (nd f t s φ)

    nd-there : (f : Frm ℓ n X) (t : P f) 
      → (s : Src ℓ n X P f) (φ : Forest P f s)
      → (p : Pos ℓ n X f (fst s))
      → (q : WebPos ℓ n X P (Typ ℓ n X f (fst s) p , snd s p , fst (φ p)) (snd (φ p)))
      → WebPos ℓ n X P (f , t , μs P f (fst s) (λ p → fst (φ p))) (nd f t s φ)
      
  Pos ℓ zero X f c = 𝟙 ℓ
  Pos ℓ (suc n) (X , P) f c = WebPos ℓ n X P f c

  Typ ℓ zero X f c p = ●
  Typ ℓ (suc n) (X , P) ._ ._ (nd-here f t s φ) = f , t , s
  Typ ℓ (suc n) (X , P) ._ ._ (nd-there f t s φ p q) =
    Typ ℓ (suc n) (X , P) (Typ ℓ n X f (fst s) p , snd s p , fst (φ p)) (snd (φ p)) q

  graft : (ℓ : Level) (n : ℕ) 
    → (X : 𝕆Type ℓ n) (P : Frm ℓ n X → Type ℓ)
    → (f : Frm ℓ n X) (t : P f) (s : Src ℓ n X P f)
    → (ω : Web ℓ n X P (f , t , s)) (φ : Forest P f s)
    → Web ℓ n X P (f , t , μs P f (fst s) (λ p → fst (φ p)))
  graft ℓ n X P .f .t ._ (lf f t) φ = snd (φ (η-pos ℓ n X f))
  graft ℓ n X P .f .t ._ (nd f t s φ) φ' = {!!} 
    -- nd f t s (λ p → {!!} , graft ℓ n X P (Typ ℓ n X f (fst s) p) (snd s p) (fst (φ p)) (snd (φ p)) (λ q → {!!} , (snd (φ' (μ-pos ℓ n X f (fst s) (λ p → fst (fst (φ p))) p q)))))
