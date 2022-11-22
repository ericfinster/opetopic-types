{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Native.NewOpetopes
open import Native.NewOpetopicType
open import Native.NewTerm 
-- open import Native.Fibrancy

open import Cubical.Foundations.Everything

module Native.NewGroupoid where

  Grp : ∀ {ℓ} → Type ℓ → (n : ℕ) → 𝕆Type ℓ n

  GrpTerm : ∀ {ℓ} (X : Type ℓ) (x : X)
    → (n : ℕ) → 𝕆Term (Grp X n)

  {-# NO_POSITIVITY_CHECK #-}
  data GrpCell {ℓ n} (X : Type ℓ) : Idx (Grp X n) → Type ℓ where

    reflₒ : (x : X) (ο : 𝕆 n) → GrpCell X (ο , TermFrm (Grp X n) (GrpTerm X x n) ο)

  Grp X zero = ■
  Grp X (suc n) = Grp X n ∥ GrpCell X
  
  GrpTerm X x zero = □
  GrpTerm X x (suc n) = GrpTerm X x n ▸ reflₒ x

  --
  --  The eliminator for cells
  --
  
  cell-elim : ∀ {n} {X : Type}
    → (P : {i : Idx (Grp X n)} → GrpCell X i → Type)
    → (r : (x : X) (ο : 𝕆 n) → P (reflₒ x ο))
    → {i : Idx (Grp X n)} (c : GrpCell X i) → P c
  cell-elim P r (reflₒ x ο) = r x ο

  --
  --  Shorthand for our canonical frames and webs
  --
  
  canon-frm : ∀ {n} (X : Type) (x : X) (ο : 𝕆 n) → Frm (Grp X n) ο
  canon-frm {n} X x ο = TermFrm (Grp X n) (GrpTerm X x n) ο

  canon-web : ∀ {n} (X : Type) (x : X) {ο : 𝕆 n} (ρ : ℙ ο) → Web (Grp X n) (canon-frm X x ο) ρ
  canon-web {n} X x ρ = TermWeb (Grp X n) (GrpTerm X x n) ρ 

  canon-dec : ∀ {n} (X : Type) (x : X) {ο : 𝕆 n} (ρ : ℙ ο)
    → (p : Pos ρ) → GrpCell X (Typ ρ p , canon-frm X x (Typ ρ p))
  canon-dec X x ρ p = reflₒ x (Typ ρ p) 

  canon-dec' : ∀ {n} (X : Type) 
    → (x : X) {ο : 𝕆 n} {ρ : ℙ ο} (τ : ℙ (ο ∣ ρ))
    → (p : Pos τ) → GrpCell {n = suc n} X (Typ τ p , Shp (Grp X n ∥ GrpCell X) (canon-web X x τ) p)
  canon-dec' X x (ndₒ ρ δ) here = reflₒ x (_ ∣ ρ)
  canon-dec' X x (ndₒ ρ δ) (there p q) = canon-dec' X x (br (δ p)) q

  --
  --  First, some lemmas about the uniqueness of cells
  -- 

  underlying : ∀ {n} (X : Type)
    → {i : Idx (Grp X n)}
    → GrpCell X i → X
  underlying X (reflₒ x ο) = x

  cell-determines-frame : ∀ {n} (X : Type)
    → {ο : 𝕆 n} {f : Frm (Grp X n) ο}
    → (c : GrpCell X (ο , f))
    → f ≡ TermFrm (Grp X n) (GrpTerm X (underlying X c) n) ο
  cell-determines-frame X (reflₒ x ο) = refl

  cell-is-refl : ∀ {n} (X : Type)
    → {ο : 𝕆 n} {f : Frm (Grp X n) ο}
    → (c : GrpCell X (ο , f))
    → (λ j → GrpCell X (ο , cell-determines-frame X c j))
      [ c ≡ reflₒ (underlying X c) ο ]
  cell-is-refl X (reflₒ x ο) = refl
  
  fib : ∀ {n} (X : Type)
    → {ο : 𝕆 n} (ρ : ℙ ο) (τ : ℙ (ο ∣ ρ))
    → (f : Frm (Grp X n) ο) (c : GrpCell X (ο , f))
    → Type 
  fib {n = n} X ρ τ f c =
    Σ[ s ∈ Web (Grp X n) f ρ ]
    Σ[ δ ∈ ((p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) s p)) ]
    Σ[ ω ∈ Web (Grp X (suc n)) (f ►[ c , ⟪ s , δ ⟫ ]) τ ]
    ((p : Pos τ) → GrpCell X (Typ τ p , Shp (Grp X (suc n)) ω p))

  canon-fib : ∀ {n} (X : Type) (x : X)
    → {ο : 𝕆 n} (ρ : ℙ ο) (τ : ℙ (ο ∣ ρ))
    → fib X ρ τ (canon-frm X x ο) (reflₒ x ο)
  canon-fib {n = n} X x ρ τ = 
    canon-web X x ρ ,
    canon-dec X x ρ ,
    canon-web X x τ ,
    canon-dec' X x τ
  
  -- -- normalize : ∀ {ℓ n} (X : Type ℓ)
  -- --   → {ο : 𝕆 n} {ρ : ℙ ο} {τ : Tr (ο , ρ)}
  -- --   → {f : Frm (Grp X n) ο} {s : Web (Grp X n) f ρ}
  -- --   → {δ : (p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) s p)}
  -- --   → {c : GrpCell X (ο , f)}
  -- --   → (ω : Web (Grp X (suc n)) (f , s , δ , c) τ)
  -- --   → (ϵ : (p : Pos τ) → GrpCell X (Typ τ p , Shp (Grp X (suc n)) ω p))
  -- --   → (λ j → fib X ρ τ (cell-determines-frame X c j) (cell-is-refl X c j))
  -- --      [ (s , δ , ω , ϵ) ≡ canon-fib X (underlying X c) ρ τ ]
  -- -- normalize {n = n} X (lf t) ϵ = {! !}
  -- -- normalize {n = n} X (nd t s δ) ϵ with ϵ here 
  -- -- normalize {n = n} X (nd ._ ._ δ) ϵ | reflₒ x (ο , ρ) = ? 

  -- claim : ∀ {ℓ n} (X : Type ℓ)
  --   → {ο : 𝕆 n} {ρ : ℙ ο} {τ : Tr (ο , ρ)}
  --   → {f : Frm (Grp X n) ο} {s : Web (Grp X n) f ρ}
  --   → {δ : (p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) s p)}
  --   → {c : GrpCell X (ο , f)}
  --   → (ω : Web (Grp X (suc n)) (f , s , δ , c) τ)
  --   → (ϵ : (p : Pos τ) → GrpCell X (Typ τ p , Shp (Grp X (suc n)) ω p))
  --   → (λ j → Σ[ σ ∈ Web (Grp X n) (cell-determines-frame X c j) ρ ]
  --            ((p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) σ p)))
  --       [ (s , δ) ≡ (TermWeb (Grp X n) (GrpTerm X (underlying X c) n) ρ
  --                   , λ p → reflₒ (underlying X c) (Typ ρ p)) ]
  -- claim {n = n} X (nd t s δ) ϵ with ϵ here 
  -- claim {n = n} X (nd ._ ._ δ) ϵ | reflₒ x (ο , ρ) =
  --   λ j → μ (Grp X n) (TermWeb (Grp X n) (GrpTerm X x n) ρ) (λ p → fst (ih p j))
  --       , λ p → snd (ih (fstₒ ρ (λ p₁ → pd (lvs (δ p₁))) p) j) (sndₒ ρ (λ p₁ → pd (lvs (δ p₁))) p)

  --   where ih : (p : Pos ρ) → (λ j → Σ-syntax (Web (Grp X n) (TermFrm (Grp X n) (GrpTerm X x n) (Typ ρ p)) (pd (lvs (δ p))))
  --                                   (λ σ → (p₁ : Pos (pd (lvs (δ p)))) → GrpCell X (Typ (pd (lvs (δ p))) p₁ , Shp (Grp X n) σ p₁)))
  --                                   [ web (lvs (δ p)) , dec (lvs (δ p)) ≡ TermWeb (Grp X n) (GrpTerm X x n) (pd (lvs (δ p))) ,
  --                                                 (λ p₁ → reflₒ x (Typ (pd (lvs (δ p))) p₁)) ]
  --         ih p = claim X (trnk (δ p)) (λ q → ϵ (there p q)) 
  -- claim {n = n} X (lf (reflₒ x ο)) ϵ = refl

  -- target : ∀ {ℓ n} (X : Type ℓ)
  --   → {i : Idx (Grp X n)}
  --   → Src (Grp X n) (GrpCell X) i → X
  -- target {n = zero} X s = underlying X (dec s ●)
  -- target {n = suc n} X {(ο , ρ) , (f , ω , δ , t)} s = underlying X t

  -- src-is-canonical : ∀ {ℓ n} (X : Type ℓ)
  --   → (i : Idx (Grp X n))
  --   → (s : Src (Grp X n) (GrpCell X) i)
  --   → Path (Σ[ i ∈ Idx (Grp X n) ] Src (Grp X n) (GrpCell X) i)
  --       (i , s) ((fst i , canon-frm X (target X s) (fst i)) ,
  --                 ⟪ canon-web X (target X s) (pd s)
  --                 , (λ p → reflₒ (target X s) (Typ (pd s) p)) ⟫)
  -- src-is-canonical X i s = {!!} 

  -- composite : ∀ {ℓ n} (X : Type ℓ)
  --   → (i : Idx (Grp X n))
  --   → (s : Src (Grp X n) (GrpCell X) i)
  --   → Σ[ t ∈ GrpCell X i ]
  --     GrpCell X (as-frm (i , s , t))
  -- composite X i s =
  --   transport⁻ (λ j → Σ[ t ∈ GrpCell X (fst (src-is-canonical X i s j)) ]
  --                     GrpCell X (as-frm (fst (src-is-canonical X i s j) ,
  --                     snd (src-is-canonical X i s j) , t)))
  --              (reflₒ (target X s) (fst i) , reflₒ (target X s) (fst i , pd s)) 

  -- composite-unique : ∀ {ℓ n} (X : Type ℓ)
  --   → (i : Idx (Grp X n))
  --   → (s : Src (Grp X n) (GrpCell X) i)
  --   → (p : Σ[ t ∈ GrpCell X i ]
  --          GrpCell X (as-frm (i , s , t)))
  --   → composite X i s ≡ p 
  -- composite-unique X (._ , ._) ._ (._ , reflₒ x (ο , ρ)) = {!!}

  -- grp-cell-is-fibrant : ∀ {n ℓ} (X : Type ℓ)
  --   → is-fibrant-rel (Grp X n) (GrpCell X) (GrpCell X)
  -- grp-cell-is-fibrant X i s = composite X i s , composite-unique X i s  



  -- -- -- first-step : ∀ {ℓ n} (X : Type ℓ)
  -- -- --   → {ο : 𝕆 n} {ρ : ℙ ο}
  -- -- --   → {f : Frm (Grp X n) ο}
  -- -- --   → (ω : Web (Grp X n) f ρ)
  -- -- --   → (ϵ : (p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) ω p))
  -- -- --   → f ≡ TermFrm (Grp X n) (GrpTerm X (target X ⟪ ω , ϵ ⟫) n) ο 
  -- -- -- first-step {n = zero} X ω ϵ = refl
  -- -- -- first-step {n = suc n} X (lf (reflₒ x ο)) ϵ = refl
  -- -- -- first-step {n = suc n} X (nd t s δ) ϵ with ϵ here
  -- -- -- first-step {n = suc n} X (nd ._ ._ δ) ϵ | reflₒ x (ο , ρ) = {!!}

  -- -- --   where ih : (p : Pos ρ) → (TermFrm (Grp X n) (GrpTerm X x n) (Typ ρ p) ,
  -- -- --                             web (lvs (δ p)) ,
  -- -- --                             dec (lvs (δ p)) ,
  -- -- --                             reflₒ x (Typ ρ p))  ≡
  -- -- --                            (TermFrm (Grp X n) (GrpTerm X x n) (Typ ρ p) ,
  -- -- --                             TermWeb (Grp X n) (GrpTerm X x n) (pd (lvs (δ p))) ,
  -- -- --                             (λ r → reflₒ x (Typ (pd (lvs (δ p))) r)) ,
  -- -- --                             reflₒ x (Typ ρ p))
                              
  -- -- --         ih p = first-step X (trnk (δ p)) (λ q → ϵ (there p q)) 

      
  -- -- -- source-part {n = n} X (nd t s δ) ϵ j with ϵ here
  -- -- -- source-part {n = n} X (nd ._ ._ δ) ϵ j | (reflₒ x (ο , ρ)) = 
  -- -- --   μ (Grp X n) (TermWeb (Grp X n) (GrpTerm X x n) ρ)
  -- -- --   (λ p → source-part X (trnk (δ p)) (λ q → ϵ (there p q)) j) 
  -- -- -- source-part X (lf (reflₒ x ο)) ϵ = refl

  -- -- -- dec-part : ∀ {ℓ n} (X : Type ℓ)
  -- -- --   → {ο : 𝕆 n} {ρ : ℙ ο} {τ : Tr (ο , ρ)}
  -- -- --   → {f : Frm (Grp X n) ο} {s : Web (Grp X n) f ρ}
  -- -- --   → {δ : (p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) s p)}
  -- -- --   → {c : GrpCell X (ο , f)}
  -- -- --   → (ω : Web (Grp X (suc n)) (f , s , δ , c) τ)
  -- -- --   → (ϵ : (p : Pos τ) → GrpCell X (Typ τ p , Shp (Grp X (suc n)) ω p))
  -- -- --   → (λ j → (p : Pos ρ) → GrpCell X (Typ ρ p , Shp (Grp X n) (source-part X ω ϵ j) p))
  -- -- --     [ δ ≡ (λ p → reflₒ (underlying X c) (Typ ρ p)) ]
  -- -- -- dec-part X (lf (reflₒ x ο)) ϵ = refl
  -- -- -- dec-part X (nd t s δ) ϵ with ϵ here
  -- -- -- dec-part X (nd ._ ._ δ) ϵ | reflₒ x (ο , ρ) = {!!}
  
  -- -- -- dec-part {n = n} X (nd t s δ) ϵ j with ϵ here
  -- -- -- dec-part {n = n} X (nd ._ ._ δ) ϵ j | (reflₒ x (ο , ρ)) =  ? 
  -- -- -- dec-part X (lf (reflₒ x ο)) ϵ = ?

  -- -- -- src-is-in-base : ∀ {ℓ n} (X : Type ℓ)
  -- -- --   → {i : Idx (Grp X n)}
  -- -- --   → (s : Src (Grp X n) (GrpCell X) i)
  -- -- --   → i ≡ (fst i , TermFrm (Grp X n) (GrpTerm X (target X s) n) (fst i))

  -- -- -- src-is-in-base {n = zero} X s = refl
  -- -- -- src-is-in-base {n = suc n} X ⟪ lf (reflₒ x ο) , δ ⟫ = refl
  -- -- -- src-is-in-base {n = suc n} X ⟪ nd t s δ , ϵ ⟫ with ϵ here
  -- -- -- src-is-in-base {n = suc n} X ⟪ nd ._ ._ δ , ϵ ⟫ | reflₒ x (ο , ρ) = {!!}

  -- -- --   where ih : (p : Pos ρ) → {!!}
  -- -- --         ih p = {!src-is-in-base X ⟪ trnk (δ p) , ? ⟫!} 

  -- -- -- src-is-in-base {n = zero} X s = refl
  -- -- -- src-is-in-base {n = suc n} X ⟪ lf (reflₒ x ο) , δ ⟫ = refl
  -- -- -- src-is-in-base {n = suc n} X ⟪ nd (reflₒ x ο) s δ , ϵ ⟫ j =
  -- -- --   refl j , (refl j , (blorp j , (λ p → bleep p j) , refl {x = reflₒ x ο} j))
  
  -- -- --   where blorp : μ (Grp X n) (web s) (λ p → web (lvs (δ p))) ≡
  -- -- --                 μ (Grp X n) (TermWeb (Grp X n) (GrpTerm X x n) (pd s))
  -- -- --                             (λ p → TermWeb (Grp X n) (GrpTerm X x n) (pd (lvs (δ p))))
  -- -- --         blorp = {!!} 

  -- -- --         bleep : (p : Pos (μₒ (pd s) (λ p₁ → pd (lvs (δ p₁)))))
  -- -- --           → (λ k → GrpCell X
  -- -- --                (Typ (pd (lvs (δ (fstₒ (pd s) (λ p₁ → pd (lvs (δ p₁))) p))))
  -- -- --                (sndₒ (pd s) (λ p₁ → pd (lvs (δ p₁))) p) , Shp (Grp X n) (blorp k) p))
  -- -- --             [ dec (lvs (δ (fstₒ (pd s) (λ p₁ → pd (lvs (δ p₁))) p))) (sndₒ (pd s) (λ p₁ → pd (lvs (δ p₁))) p) ≡
  -- -- --               reflₒ x (Typ (pd (lvs (δ (fstₒ (pd s) (λ p₁ → pd (lvs (δ p₁))) p)))) (sndₒ (pd s) (λ p₁ → pd (lvs (δ p₁))) p)) ]

  -- -- --         bleep = {!s!}

  -- -- --         -- Yes, I see.  You don't want ih here.  You want to match on (ϵ here).  This
  -- -- --         -- will *force* s to be as you say.

  -- -- --         ih : (λ j₁ → Src (Grp X n) (GrpCell X) (src-is-in-base X s j₁))
  -- -- --              [ s ≡ ⟪ TermWeb (Grp X n) (GrpTerm X (target X s) n) (pd s) ,
  -- -- --                    (λ p → reflₒ (target X s) (Typ (pd s) p)) ⟫ ]
  -- -- --         ih = src-is-canonical X s 

  -- -- -- src-is-canonical : ∀ {ℓ n} (X : Type ℓ)
  -- -- --   → {i : Idx (Grp X n)}
  -- -- --   → (s : Src (Grp X n) (GrpCell X) i)
  -- -- --   → (λ j → Src (Grp X n) (GrpCell X) (src-is-in-base X s j))
  -- -- --     [ s ≡ ⟪ TermWeb (Grp X n) (GrpTerm X (target X s) n) (pd s) , (λ p → reflₒ (target X s) (Typ (pd s) p)) ⟫ ]
  -- -- -- src-is-canonical X s = {!!} 
  
  -- -- --
  -- -- --  Yep.  And now we need to go by induction to know that s is in
  -- -- --  fact actually term web and whatnot.... but the subtlety is that
  -- -- --  if we do a naive mutual induction, we only get this about s up
  -- -- --  to a coherence.  Whereas we need an absolute equality at this
  -- -- --  point.  So can you show this stronger equality as a separate
  -- -- --  lemma?
  -- -- --
  
  -- -- -- claim : ∀ {ℓ n} (X : Type ℓ) → is-fibrant-rel (Grp X n) (GrpCell X) (GrpCell X)
  -- -- -- claim {n = zero} X (● , ●) ⟪ ● , δ ⟫ = (el , {!!}) , {!!}
  -- -- -- claim {n = suc n} X (ο , f) ⟪ ω , δ ⟫ = {!!}

  -- -- -- Grp-is-fibrant : ∀ {ℓ n} (X : Type ℓ) → is-fibrant (Grp X n)
  -- -- -- Grp-is-fibrant {n = zero} X = ●
  -- -- -- Grp-is-fibrant {n = suc zero} X = ●
  -- -- -- Grp-is-fibrant {n = suc (suc n)} X =
  -- -- --   Grp-is-fibrant {n = suc n} X , claim X

