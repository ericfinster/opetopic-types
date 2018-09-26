{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util

-- 
-- We will try to use the following conventions for naming:
--
--  P, Q, R ... : Poly
--  i, j, k ... : I     (sorts ...)
--  f, g, h ... : Op    (operations ...)
--  p, q, r ... : Param (parameters ...)
--

module Polynomial where

  record Poly {ℓ} (I : Type ℓ) : Type (lsucc ℓ) where
    field
      Op : I → Type ℓ
      Param : {i : I} → Op i → Type ℓ
      Srt : {i : I} {f : Op i} (p : Param f) → I

  open Poly public

  Ops : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → Type ℓ
  Ops {I = I} P = Σ I (Op P)
  
  Decor : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → {i : I} (f : Op P i) (X : I → Type ℓ)
    → Type ℓ
  Decor P f X = (p : Param P f) → X (Srt P p)

  ⟦_⟧ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → (I → Type ℓ) → I → Type ℓ
  ⟦ P ⟧ X i = Σ (Op P i) (λ f → Decor P f X)

  ⟦_⟧f : ∀ {ℓ} {I : Type ℓ} (P : Poly I) {X Y : I → Type ℓ}
    → (ψ : (i : I) → X i → Y i)
    → (i : I) → ⟦ P ⟧ X i → ⟦ P ⟧ Y i
  ⟦ P ⟧f ψ i (f , ϕ) = f , λ p → ψ (Srt P p) (ϕ p)

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    data W : I → Type ℓ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    Leaf : {i : I} (w : W i) → Type ℓ
    Leaf (lf i) = Lift ⊤
    Leaf (nd (f , ϕ)) = Σ (Param P f) (λ p → Leaf (ϕ p))

    LeafSrt : {i : I} (w : W i) (l : Leaf w) → I
    LeafSrt (lf i) (lift tt) = i
    LeafSrt (nd (f , ϕ)) (p , l) = LeafSrt (ϕ p) l

    Node : {i : I} (w : W i) → Type ℓ
    Node (lf i)  = Lift ⊥
    Node (nd (f , ϕ)) = ⊤ ⊔ Σ (Param P f) (λ p → Node (ϕ p))

    NodeSrt : {i : I} (w : W i) (n : Node w) → Ops P
    NodeSrt (lf i) (lift ())
    NodeSrt (nd (f , ϕ)) (inl tt) = _ , f
    NodeSrt (nd (f , ϕ)) (inr (p , n)) = NodeSrt (ϕ p) n

    Frame : {i : I} (w : W i) (f : Op P i) → Type ℓ
    Frame w f = Σ (Leaf w ≃ Param P f) (λ α →
      (l : Leaf w) → LeafSrt w l == Srt P (–> α l)) 
    
    corolla : {i : I} (f : Op P i) → W i
    corolla {i} f = nd (f , λ p → lf (Srt P p))

    corolla-lf-eqv : {i : I} (f : Op P i)
      → Leaf (corolla f) ≃ Param P f 
    corolla-lf-eqv f = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla f) → Param P f
            to (p , lift tt) = p

            from : Param P f → Leaf (corolla f) 
            from p = (p , lift tt) 

            from-to : (l : Leaf (corolla f)) → from (to l) == l
            from-to (p , lift tt) = idp

    corolla-lf-srt : {i : I} (f : Op P i) (l : Leaf (corolla f))
      → LeafSrt (corolla f) l == Srt P (–> (corolla-lf-eqv f) l)
    corolla-lf-srt f (p , lift tt) = idp

    corolla-frm : {i : I} (f : Op P i) → Frame (corolla f) f
    corolla-frm f = corolla-lf-eqv f , corolla-lf-srt f

  --
  --  Grafting of trees
  --
  
  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

  --   graft : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) → W P i
  --   graft (lf i) ψ = ψ i idp
  --   graft (nd (f , ϕ)) ψ = nd (f , λ j p → graft (ϕ j p) (λ k l → ψ k (j , p , l)))

  --   --
  --   --  Leaves in a graft
  --   --

  --   graft-leaf-in : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --     → (j : I) (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
  --     → Leaf P (graft w ψ) j
  --   graft-leaf-in (lf i) ψ j .i idp m = m
  --   graft-leaf-in (nd (f , ϕ)) ψ j k (h , p , l) m =
  --     h , p , graft-leaf-in (ϕ h p) (λ k₁ l₁ → ψ k₁ (h , p , l₁)) j k l m
      
  --   graft-leaf-elim : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) 
  --     → (j : I) (Q : (l : Leaf P (graft w ψ) j) → Type ℓ')
  --     → (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
  --            → Q (graft-leaf-in w ψ j k l m))
  --     → (l : Leaf P (graft w ψ) j) → Q l
  --   graft-leaf-elim (lf i) ψ j Q σ l = σ i idp l
  --   graft-leaf-elim (nd (f , ϕ)) ψ j Q σ (h , p , l) = 
  --     graft-leaf-elim (ϕ h p) (λ j₁ l₁ → ψ j₁ (h , p , l₁)) j
  --       (λ l₁ → Q (h , p , l₁)) (λ k₁ l₁ m₁ → σ k₁ (h , p , l₁) m₁) l

  --   graft-leaf-elim-β : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) 
  --     → (j : I) (Q : (l : Leaf P (graft w ψ) j) → Type ℓ')
  --     → (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
  --            → Q (graft-leaf-in w ψ j k l m))
  --     → (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
  --     → graft-leaf-elim w ψ j Q σ (graft-leaf-in w ψ j k l m) == σ k l m
  --   graft-leaf-elim-β (lf i) ψ j Q σ .i idp m = idp
  --   graft-leaf-elim-β (nd (f , ϕ)) ψ j Q σ k (h , p , l) m =
  --     graft-leaf-elim-β (ϕ h p) (λ j₁ l₁ → ψ j₁ (h , p , l₁)) j
  --       (λ l₁ → Q (h , p , l₁)) (λ k₁ l₁ m₁ → σ k₁ (h , p , l₁) m₁) k l m

  --   graft-leaf-rec : ∀ {ℓ'} {A : Type ℓ'}
  --     → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --     → (j : I) (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j) → A)
  --     → (l : Leaf P (graft w ψ) j) → A
  --   graft-leaf-rec {A = A} w ψ j σ = graft-leaf-elim w ψ j (cst A) σ

  --   graft-leaf-rec-β : ∀ {ℓ'} {A : Type ℓ'}
  --     → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --     → (j : I) (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j) → A)
  --     → (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
  --     → graft-leaf-rec w ψ j σ (graft-leaf-in w ψ j k l m) == σ k l m
  --   graft-leaf-rec-β {A = A} w ψ j σ = graft-leaf-elim-β w ψ j (cst A) σ

  --   module _ {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (j : I) where

  --     graft-leaf-to : Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)) → Leaf P (graft w ψ) j
  --     graft-leaf-to (k , l , m) = graft-leaf-in w ψ j k l m

  --     graft-leaf-from : Leaf P (graft w ψ) j → Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j))
  --     graft-leaf-from = graft-leaf-rec w ψ j (λ k l m → k , l , m) 

  --     abstract
      
  --       graft-leaf-to-from : (l : Leaf P (graft w ψ) j)
  --         → graft-leaf-to (graft-leaf-from l) == l
  --       graft-leaf-to-from = graft-leaf-elim w ψ j (λ l → graft-leaf-to (graft-leaf-from l) == l) 
  --         (λ k l m → ap (graft-leaf-to) (graft-leaf-rec-β w ψ j (λ k l m → k , l , m) k l m))

  --       graft-leaf-from-to : (l : Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)))
  --         → graft-leaf-from (graft-leaf-to l) == l
  --       graft-leaf-from-to (k , l , m) = graft-leaf-rec-β w ψ j (λ k l m → k , l , m) k l m

  --     graft-leaf-eqv : Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)) ≃ Leaf P (graft w ψ) j
  --     graft-leaf-eqv = equiv graft-leaf-to graft-leaf-from
  --                            graft-leaf-to-from graft-leaf-from-to
                                   
  --   --
  --   --  Nodes in a graft
  --   --
    
  --   graft-node-inl : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
  --     → Node P w g → Node P (graft w ψ) g
  --   graft-node-inl (lf i) ψ g (lift ())
  --   graft-node-inl (nd (f , ϕ)) ψ ._ (inl idp) = inl idp
  --   graft-node-inl (nd (f , ϕ)) ψ g (inr (h , p , n)) =
  --     inr (h , p , graft-node-inl (ϕ h p) (λ k l → ψ k (h , p , l)) g n)

  --   graft-node-inr : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
  --     → (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
  --     → Node P (graft w ψ) g
  --   graft-node-inr (lf i) ψ g .i idp n = n
  --   graft-node-inr (nd (f , ϕ)) ψ g k (h , p , l) n =
  --     inr (h , p , graft-node-inr (ϕ h p) (λ k l → ψ k (h , p , l)) g k l n)

  --   graft-node-elim : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --     → (g : Ops P) (Q : Node P (graft w ψ) g → Type ℓ')
  --     → (inl* : (n : Node P w g) → Q (graft-node-inl w ψ g n))
  --     → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
  --             →  Q (graft-node-inr w ψ g k l n))
  --     → (n : Node P (graft w ψ) g) → Q n
  --   graft-node-elim (lf i) ψ g Q inl* inr* n = inr* i idp n
  --   graft-node-elim (nd (f , ϕ)) ψ .(_ , f) Q inl* inr* (inl idp) = inl* (inl idp)
  --   graft-node-elim (nd (f , ϕ)) ψ g Q inl* inr* (inr (h , p , n)) = 
  --     graft-node-elim (ϕ h p) (λ k l → ψ k (h , p , l)) g
  --       (λ n₁ → Q (inr (h , p , n₁))) (λ n₁ → inl* (inr (h , p , n₁)))
  --       (λ k l n₁ → inr* k (h , p , l) n₁) n

  --   graft-node-elim-inl-β : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --     → (g : Ops P) (Q : Node P (graft w ψ) g → Type ℓ')
  --     → (inl* : (n : Node P w g) → Q (graft-node-inl w ψ g n))
  --     → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
  --             →  Q (graft-node-inr w ψ g k l n))
  --     → (n : Node P w g)
  --     → graft-node-elim w ψ g Q inl* inr* (graft-node-inl w ψ g n) == inl* n
  --   graft-node-elim-inl-β (lf i) ψ g Q inl* inr* (lift ())
  --   graft-node-elim-inl-β (nd (f , ϕ)) ψ .(_ , f) Q inl* inr* (inl idp) = idp
  --   graft-node-elim-inl-β (nd (f , ϕ)) ψ g Q inl* inr* (inr (h , p , n)) =
  --     graft-node-elim-inl-β (ϕ h p) (λ k l → ψ k (h , p , l)) g
  --       (λ n₁ → Q (inr (h , p , n₁))) (λ n₁ → inl* (inr (h , p , n₁)))
  --       (λ k l n₁ → inr* k (h , p , l) n₁) n

  --   graft-node-elim-inr-β : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --     → (g : Ops P) (Q : Node P (graft w ψ) g → Type ℓ')
  --     → (inl* : (n : Node P w g) → Q (graft-node-inl w ψ g n))
  --     → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
  --             →  Q (graft-node-inr w ψ g k l n))
  --     → (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
  --     → graft-node-elim w ψ g Q inl* inr* (graft-node-inr w ψ g k l n) == inr* k l n
  --   graft-node-elim-inr-β (lf i) ψ g Q inl* inr* .i idp n = idp
  --   graft-node-elim-inr-β (nd (f , ϕ)) ψ g Q inl* inr* k (h , p , l) n =
  --     graft-node-elim-inr-β (ϕ h p) (λ k l → ψ k (h , p , l)) g
  --       (λ n₁ → Q (inr (h , p , n₁))) (λ n₁ → inl* (inr (h , p , n₁)))
  --       (λ k l n₁ → inr* k (h , p , l) n₁) k l n

  --   graft-node-rec : ∀ {ℓ'} {A : Type ℓ'}
  --     → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
  --     → (inl* : (n : Node P w g) → A)
  --     → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g) → A)
  --     → (n : Node P (graft w ψ) g) → A
  --   graft-node-rec {A = A} w ψ g inl* inr* =
  --     graft-node-elim w ψ g (cst A) inl* inr*  

  --   graft-node-rec-inl-β : ∀ {ℓ'} {A : Type ℓ'}
  --     → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
  --     → (inl* : (n : Node P w g) → A)
  --     → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g) → A)
  --     → (n : Node P w g)
  --     → graft-node-rec w ψ g inl* inr* (graft-node-inl w ψ g n) == inl* n
  --   graft-node-rec-inl-β {A = A} w ψ g inl* inr* =
  --     graft-node-elim-inl-β w ψ g (cst A) inl* inr*

  --   graft-node-rec-inr-β : ∀ {ℓ'} {A : Type ℓ'}
  --     → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
  --     → (inl* : (n : Node P w g) → A)
  --     → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g) → A)
  --     → (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
  --     → graft-node-rec w ψ g inl* inr* (graft-node-inr w ψ g k l n) == inr* k l n
  --   graft-node-rec-inr-β {A = A} w ψ g inl* inr* = 
  --     graft-node-elim-inr-β w ψ g (cst A) inl* inr*

  --   module _ {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P) where

  --     graft-node-to : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)) → Node P (graft w ψ) g
  --     graft-node-to (inl n) = graft-node-inl w ψ g n
  --     graft-node-to (inr (k , l , n)) = graft-node-inr w ψ g k l n
      
  --     graft-node-from : Node P (graft w ψ) g → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
  --     graft-node-from = graft-node-rec w ψ g inl (λ k l n → inr (k , l , n))

  --     abstract
      
  --       graft-node-to-from : (n : Node P (graft w ψ) g)
  --         → graft-node-to (graft-node-from n) == n
  --       graft-node-to-from = graft-node-elim w ψ g (λ n → graft-node-to (graft-node-from n) == n)
  --         (λ n → ap graft-node-to (graft-node-rec-inl-β w ψ g inl (λ k l n → inr (k , l , n)) n))
  --         (λ k l n → ap graft-node-to (graft-node-rec-inr-β w ψ g inl (λ k l n → inr (k , l , n)) k l n))

  --       graft-node-from-to : (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
  --         → graft-node-from (graft-node-to n) == n
  --       graft-node-from-to (inl n) = graft-node-rec-inl-β w ψ g inl (λ k l n → inr (k , l , n)) n
  --       graft-node-from-to (inr (k , l , n)) = graft-node-rec-inr-β w ψ g inl (λ k l n → inr (k , l , n)) k l n
      
  --     graft-node-eqv : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)) ≃ Node P (graft w ψ) g
  --     graft-node-eqv = equiv graft-node-to graft-node-from 
  --                            graft-node-to-from graft-node-from-to 

  --   --
  --   -- Basic laws of grafting
  --   --

  --   -- grafting is unital
  --   graft-unit : {i : I} (w : W P i) → graft w (λ j l → lf j) == w
  --   graft-unit (lf i) = idp
  --   graft-unit (nd (f , ϕ)) =
  --     ap (λ x → nd (f , x)) (λ= (λ j → λ= (λ l → graft-unit (ϕ j l))))

  --   -- grafting is associative
  --   graft-assoc : {i : I} (w : W P i)
  --     → (ψ₀ : ∀ j → Leaf P w j → W P j)
  --     → (ψ₁ : ∀ j k → (l : Leaf P w k) → Leaf P (ψ₀ k l) j → W P j)
  --     → graft (graft w ψ₀) (λ j → graft-leaf-rec w ψ₀ j (ψ₁ j))
  --       == graft w (λ j l → graft (ψ₀ j l) (λ k m → ψ₁ k j l m))
  --   graft-assoc (lf i) ψ₀ ψ₁ = idp
  --   graft-assoc (nd (f , ϕ)) ψ₀ ψ₁ = ap (λ x → nd (f , x))
  --     (λ= (λ h → λ= (λ p → graft-assoc (ϕ h p) (λ k l → ψ₀ k (h , p , l))
  --       (λ j k l m → ψ₁ j k (h , p , l) m))))


