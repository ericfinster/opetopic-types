{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Poly 
open import Inspect

module PolyMonads where

  data Mnd : Type₀

  Idx : Mnd → Type₀

  γ : (M : Mnd) → Idx M → Type₀
  ρ : (M : Mnd) (i : Idx M) → γ M i → Type₀
  τ : (M : Mnd) (i : Idx M) (c : γ M i) → ρ M i c → Idx M

  η : (M : Mnd) (i : Idx M) → γ M i
  μ : (M : Mnd) (i : Idx M) (c : γ M i) (δ : (p : ρ M i c) → γ M (τ M i c p)) → γ M i

  record ηρ (M : Mnd) (i : Idx M) : Type₀ where
    constructor ηρ-unit

  data μρ : (M : Mnd) (i : Idx M) (c : γ M i) (δ : (p : ρ M i c) → γ M (τ M i c p)) → Type₀ where
    μρ-pair : (M : Mnd) (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p : ρ M i c) (q : ρ M (τ M i c p) (δ p))
      → μρ M i c δ

  μρ-fst : (M : Mnd) (i : Idx M) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → μρ M i c δ
    → ρ M i c
  μρ-fst M i c δ (μρ-pair _ _ _ _ p q) = p

  μρ-snd : (M : Mnd) (i : Idx M) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → (p : μρ M i c δ)
    → ρ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p))
  μρ-snd M i c δ (μρ-pair _ _ _ _ p q) = q

  ⟪_⟫ : (M : Mnd) → (Idx M → Type₀) → Idx M → Type₀
  ⟪ M ⟫ X i = Σ (γ M i) (λ c → (p : ρ M i c) → X (τ M i c p))

  module _ (M : Mnd) where
  
    postulate

      ηρ-rw : (i : Idx M) →
        ρ M i (η M i) ↦ ηρ M i

      {-# REWRITE ηρ-rw #-}

      ηp-τ : (i : Idx M) (p : ηρ M i)
        → τ M i (η M i) p ↦ i

      {-# REWRITE ηp-τ #-}

      μρ-rw : (i : Idx M) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p))
        → ρ M i (μ M i c δ) ↦ μρ M i c δ

      {-# REWRITE μρ-rw #-}

      μρ-contract : (i : Idx M) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p))
        → (p : μρ M i c δ)
        → μρ-pair M i c δ (μρ-fst M i c δ p) (μρ-snd M i c δ p) ↦ p

      {-# REWRITE μρ-contract #-}
      
      μρ-τ : (i : Idx M) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p))
        → (p : μρ M i c δ)
        → τ M i (μ M i c δ) p ↦ τ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p)) (μρ-snd M i c δ p)
        -- → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
        -- → τ M i (μ M i c δ) (μρ-pair p₀ p₁) ↦ τ M (τ M i c p₀) (δ p₀) p₁

      {-# REWRITE μρ-τ #-}
      
      unit-l : (i : Idx M) (c : γ M i) 
        → μ M i c (λ p → η M (τ M i c p)) ↦ c

      {-# REWRITE unit-l #-}

      unit-r : (i : Idx M)
        → (δ : (p : ρ M i (η M i)) → γ M (τ M i (η M i) p)) 
        → μ M i (η M i) δ ↦ δ ηρ-unit

      {-# REWRITE unit-r #-}

      assoc : (i : Idx M) (c : γ M i)
              (δ : (p : ρ M i c) → γ M (τ M i c p))
              (ε : (q : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) q)) →
              μ M i (μ M i c δ) ε ↦ μ M i c (λ p → μ M (τ M i c p) (δ p) (λ q → ε (μρ-pair M i c δ p q)))

      {-# REWRITE assoc #-}

  --
  --  Monad constructors
  --
  
  data Mnd where
    id : (I : Type₀) → Mnd 
    slc : Mnd → Mnd
    pb : (M : Mnd) (X : Idx M → Type₀) → Mnd 

  Idx (id I) = ⊤
  Idx (slc M) = Σ (Idx M) (γ M)
  Idx (pb M X) = Σ (Idx M) X

  --
  --  The pullback monad
  --
  
  module _ (M : Mnd) (X : Idx M → Type₀) where

    I-pb : Type₀
    I-pb = Σ (Idx M) X

    γ-pb : I-pb → Type₀
    γ-pb (i , x) = Σ (γ M i) (λ c → (p : ρ M i c) → X (τ M i c p))

    ρ-pb : (i : I-pb) → γ-pb i → Type₀
    ρ-pb (i , x) (c , δ) = ρ M i c

    τ-pb : (i : I-pb) (c : γ-pb i) → ρ-pb i c → I-pb
    τ-pb (i , x) (c , δ) p = τ M i c p , δ p

    η-pb : (i : I-pb) → γ-pb i
    η-pb (i , x) = η M i , λ p → x 

    ηρ-pb : (i : I-pb) → ρ-pb i (η-pb i)
    ηρ-pb (i , x) = ηρ-unit

    μ-pb : (i : I-pb) (c : γ-pb i) (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p)) → γ-pb i
    μ-pb (i , x) (c , δ) ε = μ M i c (fst ∘ ε) , λ p → snd (ε (μρ-fst M i c (fst ∘ ε) p)) (μρ-snd M i c (fst ∘ ε) p) 

  --
  -- The slice monad
  --
  
  module _ (M : Mnd) where

    I-slc : Type₀
    I-slc = Σ (Idx M) (γ M)

    data Nst : (i : Idx M) → (c : γ M i) → Type₀ where
      dot : (i : Idx M) → Nst i (η M i)
      box : (i : Idx M) (c : γ M i)
            (δ : (p : ρ M i c) → γ M (τ M i c p))
            (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p)) →
            Nst i (μ M i c δ)

    γ-slc : I-slc → Type₀
    γ-slc (i , c) = Nst i c

    -- data Node : (i : Idx M) → (c : γ M i) → (n : Nst i c) → Type₀ where
    --   here : (i : Idx M) (c : γ M i)
    --             → (δ : (p : ρ M i c) → γ M (τ M i c p))
    --             → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
    --             → Node i (μ M i c δ) (box i c δ ε)
    --   there : (i : Idx M) (c : γ M i)
    --              → (δ : (p : ρ M i c) → γ M (τ M i c p))
    --              → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
    --              → (p : ρ M i c) (q : Node (τ M i c p) (δ p) (ε p))
    --              → Node i (μ M i c δ) (box i c δ ε)

    ρ-slc : (i : I-slc) (n : γ-slc i) → Type₀
    ρ-slc (i , .(η _ i)) (dot .i) = ⊥
    ρ-slc (i , .(μ _ i c δ)) (box .i c δ ε) = ⊤ ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ p) (ε p))
    -- ρ-slc (i , c) n = Node i c n

    τ-slc : (i : I-slc) (n : γ-slc i) (p : ρ-slc i n) → I-slc
    τ-slc (i , .(η _ i)) (dot .i) ()
    τ-slc (i , .(μ _ i c δ)) (box .i c δ ε) (inl unit) = i , c
    τ-slc (i , .(μ _ i c δ)) (box .i c δ ε) (inr (p , q)) = τ-slc (τ M i c p , δ p) (ε p) q
    -- τ-slc (i , ._) ._ (here .i c δ ε) = i , c
    -- τ-slc (i , ._) ._ (there .i c δ ε p p₁) = τ-slc (τ M i c p , δ p) (ε p) p₁

    η-slc : (i : I-slc) → γ-slc i
    η-slc (i , c) = (box i c (λ p → η M (τ M i c p)) (λ p → dot (τ M i c p)))

    ηρ-slc : (i : I-slc) → ρ-slc i (η-slc i)
    ηρ-slc i = inl unit
    
    -- ηρ-slc (i , c) = here i c (λ p → η M (τ M i c p)) (λ p → dot (τ M i c p))

    --
    --  Grafting
    --
    
    graft-slc : (i : Idx M) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p)) 
      → Nst i (μ M i c δ₁)
    graft-slc i .(η M i) (dot .i) δ₁ ε₁ = ε₁ ηρ-unit
    graft-slc i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ =
      let  δ₁' p q = δ₁ (μρ-pair M i c δ p q)
           ε₁' p q = ε₁ (μρ-pair M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in box i c δ' (λ p → graft-slc (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p))

    -- graft-slc-ρ-to : (i : Idx M) (c : γ M i) (n : Nst i c)
    --   → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
    --   → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p)) 
    --   → ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p))
    --   → ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)
    -- graft-slc-ρ-to i .(η _ i) (dot .i) δ₁ ε₁ (inl ())
    -- graft-slc-ρ-to i .(η _ i) (dot .i) δ₁ ε₁ (inr (p , q)) = q
    -- graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inl (here .i .c .δ .ε)) = 
    --   let δ₁' p q = δ₁ (μρ-pair p q)
    --       ε₁' p q = ε₁ (μρ-pair p q)
    --       δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
    --       ε' p = graft-slc (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
    --   in here i c δ' ε'
    -- graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inl (there .i .c .δ .ε p q)) = {!!}
    -- graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inr (μρ-pair p q , q₁)) = {!!}

    graft-slc-ρ-to : (i : Idx M) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p)) 
      → ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p))
      → ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)
    graft-slc-ρ-to i .(η _ i) (dot .i) δ₁ ε₁ (inl ())
    graft-slc-ρ-to i .(η _ i) (dot .i) δ₁ ε₁ (inr (ηρ-unit , q)) = q
    graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inl unit)) = inl unit
    graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inr (p , q))) = 
      let  δ₁' p q = δ₁ (μρ-pair M i c δ p q) 
           ε₁' p q = ε₁ (μρ-pair M i c δ p q) 
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in inr (p , graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) (inl q))
    graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let  δ₁' p q = δ₁ (μρ-pair M i c δ p q) 
           ε₁' p q = ε₁ (μρ-pair M i c δ p q) 
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           p₀ = μρ-fst M i c δ p
           p₁ = μρ-snd M i c δ p
      in inr (p₀ , graft-slc-ρ-to (τ M i c p₀) (δ p₀) (ε p₀) (δ₁' p₀) (ε₁' p₀) (inr (p₁ , q)))

    graft-slc-ρ-from : (i : Idx M) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p))
      → ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)
      → ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p))

    graft-slc-ρ-from-lcl : (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (δ₁ : (p : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) p))
      → (ε₁ : (p : ρ M i (μ M i c δ)) → Nst (τ M i (μ M i c δ) p) (δ₁ p))
      → (p : ρ M i c)
      → ρ-slc (τ M i c p , δ p) (ε p) ⊔
          Σ (ρ M (τ M i c p) (δ p)) (λ p₁ → ρ-slc (τ M (τ M i c p) (δ p) p₁ , δ₁ (μρ-pair M i c δ p p₁)) (ε₁ (μρ-pair M i c δ p p₁)))
      → (⊤ ⊔ Σ (ρ M i c) (λ p₁ → ρ-slc (τ M i c p₁ , δ p₁) (ε p₁))) ⊔
          Σ (ρ M i (μ M i c δ)) (λ p₁ → ρ-slc (τ M i (μ M i c δ) p₁ , δ₁ p₁) (ε₁ p₁))

    graft-slc-ρ-from i .(η M i) (dot .i) δ₁ ε₁ q = inr (ηρ-unit , q)
    graft-slc-ρ-from i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl unit) = inl (inl unit)
    graft-slc-ρ-from i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let  δ₁' p q = δ₁ (μρ-pair M i c δ p q)
           ε₁' p q = ε₁ (μρ-pair M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p (graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q) 

    graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p (inl q₀) = inl (inr (p , q₀))
    graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p (inr (p₀ , q₀)) = inr (μρ-pair M i c δ p p₀ , q₀)
    
    --
    --  Joining
    --

    μ-slc : (i : I-slc) (n : γ-slc i) (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p)) → γ-slc i
    μ-slc (i , .(η M i)) (dot .i) κ = dot i
    μ-slc (i , .(μ M i c δ)) (box .i c δ ε) κ = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in graft-slc i c (κ (inl unit)) δ ε'
      -- let κ' p q = κ (there i c δ ε p q)
      --     ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      -- in graft-slc i c (κ (here i c δ ε)) δ ε'

    μρ-slc-to : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → Σ (ρ-slc i n) (λ q → ρ-slc (τ-slc i n q) (κ q))
      → ρ-slc i (μ-slc i n κ)
    μρ-slc-to (i , .(η _ i)) (dot .i) κ (() , q₁)
    μρ-slc-to (i , .(μ _ i c δ)) (box .i c δ ε) κ (inl unit , q₁) =
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in graft-slc-ρ-to i c (κ (inl unit)) δ ε' (inl q₁)
    μρ-slc-to (i , .(μ _ i c δ)) (box .i c δ ε) κ (inr (p₀ , q₀) , q₁) = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in graft-slc-ρ-to i c (κ (inl unit)) δ ε'
           (inr (p₀ , (μρ-slc-to (τ M i c p₀ , δ p₀) (ε p₀) (κ' p₀) (q₀ , q₁)))) 
    
    μρ-slc-from : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → ρ-slc i (μ-slc i n κ)
      → Σ (ρ-slc i n) (λ q → ρ-slc (τ-slc i n q) (κ q))

    μρ-slc-from-lcl : (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (κ : (p : ⊤ ⊔ (Σ (ρ M i c) (λ p₁ →
          ρ-slc (τ M i c p₁ , δ p₁) (ε p₁)))) → γ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) p))
      → ρ-slc (i , c) (κ (inl unit)) ⊔ Σ (ρ M i c) (λ p →
          ρ-slc (τ M i c p , δ p) (μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁)))))
      → Σ (⊤ ⊔ (Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ p) (ε p))))
          (λ q → ρ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) q) (κ q))

    μρ-slc-from (i , .(η _ i)) (dot .i) κ ()
    μρ-slc-from (i , .(μ _ i c δ)) (box .i c δ ε) κ q = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in μρ-slc-from-lcl i c δ ε κ (graft-slc-ρ-from i c (κ (inl unit)) δ ε' q)

    μρ-slc-from-lcl i c δ ε κ (inl q₀) = inl unit , q₀
    μρ-slc-from-lcl i c δ ε κ (inr (p₀ , q₀)) =
      let κ' q = κ (inr (p₀ , q))
          ih = μρ-slc-from (τ M i c p₀ , δ p₀) (ε p₀) κ' q₀
      in inr (p₀ , fst ih) , snd ih

  --
  --  Decoding functions
  --
  
  γ (id I) i = ⊤
  -- γ (fr P) = γ-fr P
  γ (slc M) = γ-slc M
  γ (pb M X) = γ-pb M X

  ρ (id I) i unit = ⊤
  -- ρ (fr P) = ρ-fr P
  ρ (slc M) = ρ-slc M
  ρ (pb M X) = ρ-pb M X 

  τ (id I) i unit unit = i
  -- τ (fr P) = τ-fr P
  τ (slc M) = τ-slc M
  τ (pb M X) = τ-pb M X 

  η (id I) _ = unit
  -- η (fr P) = η-fr P
  η (slc M) = η-slc M
  η (pb M X) = η-pb M X

  μ (id I) i unit δ = unit
  -- μ (fr P) = μ-fr P
  μ (slc M) = μ-slc M
  μ (pb M X) = μ-pb M X 

  --
  --  Place compatibility rewrites
  --

  postulate

    ρ-slc-η-compat : (M : Mnd) (i : Idx (slc M))
      → ηρ (slc M) i ↦ ρ-slc M i (η-slc M i)

    {-# REWRITE ρ-slc-η-compat #-}

    ρ-slc-ηρ-compat : (M : Mnd) (i : Idx (slc M))
      → ηρ-unit {M = slc M} {i = i} ↦ inl unit

    {-# REWRITE ρ-slc-ηρ-compat #-}

    ρ-slc-μ-compat : (M : Mnd) (i : Idx (slc M)) (c : γ (slc M) i)
      → (δ : (p : ρ (slc M) i c) → γ (slc M) (τ (slc M) i c p))
      → μρ (slc M) i c δ ↦ ρ-slc M i (μ-slc M i c δ)

    {-# REWRITE ρ-slc-μ-compat #-}

    ρ-slc-μ-pair-compat : (M : Mnd) (i : Idx (slc M)) (c : γ (slc M) i)
      → (δ : (p : ρ (slc M) i c) → γ (slc M) (τ (slc M) i c p))
      → (p : ρ (slc M) i c) (q : ρ (slc M) (τ (slc M) i c p) (δ p))
      → μρ-pair (slc M) i c δ p q ↦ μρ-slc-to M i c δ (p , q)

    {-# REWRITE ρ-slc-μ-pair-compat #-}




