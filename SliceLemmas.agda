{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType

module SliceLemmas where

  -- Just going to accumulate random lemmas that clog the typechecker
  -- here so that we can use them in what follows...

  rotate : ∀ {ℓ} {A : Type ℓ} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₁) (q : a₂ == a₁) (r : a₀ == a₂)
    → p ∙ ! q == r
    → p == r ∙ q
  rotate idp idp r s = s ∙ ! (∙-unit-r r)

  pth-alg₀ : ∀ {ℓ} {A : Set ℓ} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₁) (q : a₂ == a₁) 
    → p == (p ∙ ! q) ∙ q 
  pth-alg₀ idp idp = idp

  pth-alg₁ : ∀ {ℓ} {A : Set ℓ} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₂) (q : a₁ == a₀) 
    → p == (! q ∙ idp) ∙ q ∙ p
  pth-alg₁ idp idp = idp 

  fst=-comm : ∀ {i j} {A : Type i} {B : A → Type j}
    → {x y z : Σ A B} (p : y == x) (q : y == z)
    → fst= (! p ∙ q) == ! (fst= p) ∙ fst= q
  fst=-comm idp idp = idp

  pair=ap-lem : ∀ {i j k l} {A : Type i} {B : A → Type j}
    → {C : Σ A B → Type k} {R : Type l} {D : Σ (Σ A B) C → R}
    → {a : A} {b b' : B a} {c : C (a , b)} {c' : C (a , b')}
    → (p : b == b')
    → (q : c == c' [ C ↓ ap (a ,_) p ])
    → ap D (pair= (ap (a ,_) p) q) == 
      (ap (λ x → D ((a , fst x) , snd x)) (pair= p (↓-ap-out C (a ,_) p q)))
  pair=ap-lem idp idp = idp

  -- Lemma about transporting in constructors
  typ-trans-inv : (M : 𝕄) (M↓ : 𝕄↓ M)
    → {i : Idx M} {c : Cns M i}
    → {j j' : Idx↓ M↓ i} (e : j == j')
    → (d : Cns↓ M↓ j c) (p : Pos M c)
    → Typ↓ M↓ (transport (λ x → Cns↓ M↓ x c) e d) p == Typ↓ M↓ d p
  typ-trans-inv M M↓ idp d p = idp

  Σ-fst-triv-lem₀ : ∀ {i j} {A : Type i} {B : A → Type j}
    → {a : A} {b b' : B a} (p : Path {A = Σ A B} (a , b) (a , b'))
    → (q : fst= p == idp)
    → b == b'
  Σ-fst-triv-lem₀ {B = B} {b = b} {b' = b'} p q =
    transport (λ x → b == b' [ B ↓ x ]) q (snd= p) 
  
  Σ-fst-triv-lem₁ : ∀ {i j k} {A : Type i} {B : A → Type j}
    → {C : Σ A B → Type k}
    → {a : A} {b b' : B a} (p : (a , b) == (a , b'))
    → (q : fst= p == idp)
    → {c : C (a , b)} {c' : C (a , b')}
    → c == c' [ C ↓ p ]
    → c == c' [ (λ b → C (a , b)) ↓ Σ-fst-triv-lem₀ p q ] 
  Σ-fst-triv-lem₁ {B = B} {C = C} {a = a} {b = b} {b' = b'} p q {c} {c'} r =
    ↓-ap-out C (a ,_) (Σ-fst-triv-lem₀ p q) pth-ovr

    where pth : p == pair= idp (Σ-fst-triv-lem₀ p q)
          pth = pair=-η p ∙ (ap (λ z → pair= (fst z) (snd z))
            (pair= q (from-transp (λ z → b == b' [ B ↓ z ]) q {u = snd= p} idp)))

          pth-ovr : c == c' [ C ↓ ap (a ,_) (Σ-fst-triv-lem₀ p q) ]
          pth-ovr = transport (λ z → c == c' [ C ↓ z ]) pth r 

  Σ-fst-triv-lem₂ : ∀ {i j k l} (A : Type i) (B : A → Type j) 
    → (C : Σ A B → Type k) {R : Type l} (D : Σ (Σ A B) C → R)
    → (a : A) (b b' : B a) (c : C (a , b)) (c' : C (a , b'))
    → (p : (a , b) == (a , b'))
    → (q : fst= p == idp)
    → (r : c == c' [ C ↓ p ])
    → ap D (pair= p r) ==
      ap (λ x → D ((a , fst x) , snd x))
         (pair= (Σ-fst-triv-lem₀ p q) (Σ-fst-triv-lem₁ p q r))
  Σ-fst-triv-lem₂ A B C D a b b' c c' p q r = 

    ap D (pair= p r) =⟨ ap (λ x → ap D (pair= (fst x) (snd x))) pth-pair ⟩  
    ap D (pair= (ap (a ,_) (Σ-fst-triv-lem₀ p q)) pth-ovr)
      =⟨ pair=ap-lem (Σ-fst-triv-lem₀ p q) pth-ovr ⟩ 
    ap (λ x → D ((a , fst x) , snd x))
      (pair= (Σ-fst-triv-lem₀ p q) (↓-ap-out C (a ,_) (Σ-fst-triv-lem₀ p q) pth-ovr)) =∎

    where pth : p == pair= idp (Σ-fst-triv-lem₀ p q)
          pth = pair=-η p ∙ (ap (λ z → pair= (fst z) (snd z))
            (pair= q (from-transp (λ z → b == b' [ B ↓ z ]) q {u = snd= p} idp)))

          pth-ovr : c == c' [ C ↓ ap (a ,_) (Σ-fst-triv-lem₀ p q) ]
          pth-ovr = transport (λ z → c == c' [ C ↓ z ]) pth r 

          pth-pair : (p , r) == (pair= idp (Σ-fst-triv-lem₀ p q) , pth-ovr)
          pth-pair = pair= pth (from-transp (λ z → c == c' [ C ↓ z ]) pth {u = r} idp) 

  app=↓ : ∀ {i j k} {A : Type i} {B : A → Type j}
    → {C : (a : A) → B a → Type k}
    → {f f' : (a : A) → B a} (p : f == f')
    → {g : (a : A) → C a (f a)}
    → {g' : (a : A) → C a (f' a)}
    → (q : g == g' [ (λ x → (a : A) → C a (x a)) ↓ p ])
    → (a : A) → g a == g' a [ (λ x → C a x) ↓ app= p a ]
  app=↓ idp idp a = idp 

  λ=↓₀ : ∀ {i j k} {A : Type i} {B : A → Type j}
    → {C : (a : A) → B a → Type k}
    → {f f' : (a : A) → B a} (p : f == f')
    → {g : (a : A) → C a (f a)}
    → {g' : (a : A) → C a (f' a)}
    → (q : (a : A) → g a == g' a [ (λ x → C a x) ↓ app= p a ])
    → g == g' [ (λ x → (a : A) → C a (x a)) ↓ p ]
  λ=↓₀ idp q = λ= q
  
  λ=↓ : ∀ {i j k} {A : Type i} {B : A → Type j}
    → {C : (a : A) → B a → Type k}
    → {f f' : (a : A) → B a} (p : (a : A) → f a == f' a)
    → {g : (a : A) → C a (f a)}
    → {g' : (a : A) → C a (f' a)}
    → (q : (a : A) → g a == g' a [ (λ x → C a x) ↓ p a ])
    → g == g' [ (λ x → (a : A) → C a (x a)) ↓ λ= p ]
  λ=↓ {C = C} p {g = g} {g' = g'} q =
    λ=↓₀ {C = C} (λ= p) (λ a →
      transport (λ z → g a == g' a [ (C a) ↓ z ]) (! (app=-β p a)) (q a))

  postulate
  
    app=↓-β : ∀ {i j k} {A : Type i} {B : A → Type j}
      → {C : (a : A) → B a → Type k}
      → {f f' : (a : A) → B a} (p : (a : A) → f a == f' a)
      → {g : (a : A) → C a (f a)}
      → {g' : (a : A) → C a (f' a)}
      → (q : (a : A) → g a == g' a [ (λ x → C a x) ↓ p a ])
      → (a : A)
      → app=↓ {C = C} (λ= p) (λ=↓ p q) a == q a
          [ (λ z → g a == g' a [ C a ↓ z ]) ↓ app=-β p a ]

  app=-pair : ∀ {i j k} {A : Type i} {B : A → Type j}
    → {C : (a : A) → B a → Type k}
    → {f f' : (a : A) → B a} (p : (a : A) → f a == f' a)
    → {g : (a : A) → C a (f a)}
    → {g' : (a : A) → C a (f' a)}
    → (q : (a : A) → g a == g' a [ (λ x → C a x) ↓ p a ])
    → (a : A)
    → pair= (app= (λ= p) a) (app=↓ (λ= p) (λ=↓ p q) a)
    == pair= (p a) (q a)
  app=-pair p q a = ap (λ x → pair= (fst x) (snd x))
    (pair= (app=-β p a) (app=↓-β p q a)) 


  --
  -- Various generic lemmas about indices and so on in the slice
  -- generated by a monad over ....
  --
  
  module SliceOver (M : 𝕄) (M↓ : 𝕄↓ M) where

    Plbk : 𝕄
    Plbk = Pb M (Idx↓ M↓)

    Plbk↓ : 𝕄↓ Plbk
    Plbk↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)
    
    Slc : 𝕄
    Slc = Slice Plbk

    Slc↓ : 𝕄↓ Slc
    Slc↓ = Slice↓ Plbk↓
  
    -- An explicit description of equalities in Idx↓ Slc↓ 
    slc-idx-lem : (i : Idx M) (j : Idx↓ M↓ i)
      → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j₀ : Idx↓ M↓ i} {e₀ : j₀ == j}
      → {d₀ : Cns↓ M↓ j₀ c} {α₀ : (p : Pos M c) → Typ↓ M↓ d₀ p == ν p}
      → {j₁ : Idx↓ M↓ i} {e₁ : j₁ == j}
      → {d₁ : Cns↓ M↓ j₁ c} {α₁ : (p : Pos M c) → Typ↓ M↓ d₁ p == ν p}
      → (q : j₀ == j₁) (r : e₀ == q ∙ e₁)
      → (s : transport (λ x → Cns↓ M↓ x c) q d₀ == d₁)
      → (t : (p : Pos M c) → α₀ p == (! (typ-trans-inv M M↓ q d₀ p) ∙ ap (λ x → Typ↓ M↓ x p) s) ∙ α₁ p)
      → Path {A = Idx↓ Slc↓ ((i , j) , c , ν)}
        ((j₀ , e₀) , (d₀ , α₀)) ((j₁ , e₁) , (d₁ , α₁)) 
    slc-idx-lem i j c ν idp idp idp t =
      pair= idp (pair= idp (λ= t))

    slc-idx-lem-coh : (i : Idx M) (j : Idx↓ M↓ i)
      → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j₀ : Idx↓ M↓ i} {e₀ : j₀ == j}
      → {d₀ : Cns↓ M↓ j₀ c} {α₀ : (p : Pos M c) → Typ↓ M↓ d₀ p == ν p}
      → {j₁ : Idx↓ M↓ i} {e₁ : j₁ == j}
      → {d₁ : Cns↓ M↓ j₁ c} {α₁ : (p : Pos M c) → Typ↓ M↓ d₁ p == ν p}
      → (q : j₀ == j₁) (r : e₀ == q ∙ e₁)
      → (s : transport (λ x → Cns↓ M↓ x c) q d₀ == d₁)
      → (t : (p : Pos M c) → α₀ p == (! (typ-trans-inv M M↓ q d₀ p) ∙ ap (λ x → Typ↓ M↓ x p) s) ∙ α₁ p)
      → fst= (slc-idx-lem i j c ν q r s t) == pair= q (↓-idf=cst-in r)
    slc-idx-lem-coh i j c ν idp idp idp t = fst=-β idp (pair= idp (λ= t)) 

    module _ where

      the-lemma : {i : Idx Slc} {εp : Cns Slc i}
        → {k k' : Idx↓ Plbk↓ (fst i)} {j : Cns↓ Plbk↓ k (snd i)}
        → {j' j'' : Cns↓ Plbk↓ k' (snd i)}
        → (idx-ih-coh : Path {A = Idx↓ Slc↓ i} (k , j) (k' , j'))
        → (cns-ih : Cns↓ Slc↓ (k , j) εp) (q : Pos Slc εp)
        → (idx-u-ih : Path {A = Idx↓ Slc↓ i} (k , j) (k' , j''))
        → (ε↓ : Cns↓ Slc↓ (k' , j'') εp)
        → (cns-u-ih : cns-ih == ε↓ [ (λ x → Cns↓ Slc↓ x εp) ↓ idx-u-ih ])
        → (ctr : fst= (! idx-ih-coh ∙ idx-u-ih) == idp)
        → typ-trans-inv Slc Slc↓ idx-ih-coh cns-ih q ∙ (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= idx-u-ih cns-u-ih))
          == ap (λ x → Typ↓ Slc↓ (snd x) q)
            (pair= (Σ-fst-triv-lem₀ (! idx-ih-coh ∙ idx-u-ih) ctr)
              (Σ-fst-triv-lem₁ (! idx-ih-coh ∙ idx-u-ih) ctr (!ᵈ (from-transp (λ x → Cns↓ Slc↓ x εp) idx-ih-coh idp) ∙ᵈ cns-u-ih))) 
      the-lemma {i} {εp} {k = k} {j = j} {j'' = j''} idp cns-ih q idx-u-ih ε↓ cns-u-ih ctr =
        transport (λ z → ap (λ x → Typ↓ₛ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) (snd x) q)
                         (pair= idx-u-ih cns-u-ih)
                         ==
                         ap (λ x → Typ↓ₛ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) (snd x) q)
                         (pair= (Σ-fst-triv-lem₀ idx-u-ih ctr)
                          (Σ-fst-triv-lem₁ idx-u-ih ctr z))) 
                  (! (idp◃ cns-u-ih))
                  (Σ-fst-triv-lem₂ (Idx↓ Plbk↓ (fst i)) (λ x → Cns↓ Plbk↓ x (snd i))
                      (λ x → Cns↓ Slc↓ x εp) (λ x → Typ↓ Slc↓ (snd x) q) k j j''
                        cns-ih ε↓ idx-u-ih ctr cns-u-ih)

    module Helpers (i : Idx M) (j : Idx↓ M↓ i)
             (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
             (δ : (p : Pos M c) → Cns Plbk (Typ M c p , ν p))
             (ε : (p : Pos M c) → Cns Slc ((Typ M c p , ν p) , δ p))
             (d : Cns↓ M↓ j c) (typ-d=ν : (p : Pos M c) → Typ↓ M↓ d p == ν p) where

      μf = μ-pos-fst M c (fst ∘ δ)
      μs = μ-pos-snd M c (fst ∘ δ)

      δμ : (pq : Pos M (μ M c (fst ∘ δ)))
        → Idx↓ M↓ (Typ M (fst (δ (μf pq))) (μs pq))
      δμ pq = snd (δ (μf pq)) (μs pq) 

      δ↓μ : (δ↓ : (p : Pos M c) → Cns↓ Plbk↓ (Typ↓ M↓ d p , typ-d=ν p) (δ p))
        → (pq : Pos M (μ M c (fst ∘ δ)))
        → Typ↓ M↓ (fst (δ↓ (μf pq))) (μs pq)
        == snd (δ (μf pq)) (μs pq)
      δ↓μ δ↓ pq = snd (δ↓ (μf pq)) (μs pq) 

      δ-set : Set
      δ-set = (p : Pos M c) → Cns↓ Plbk↓ (Typ↓ M↓ d p , typ-d=ν p) (δ p)

      ε-fib : δ-set → Set
      ε-fib δ↓ = (p : Pos M c) → Cns↓ Slc↓ ((Typ↓ M↓ d p , typ-d=ν p) , δ↓ p) (ε p)

      Σ-δε : Set 
      Σ-δε = Σ δ-set ε-fib

      Idx↓Slc↓Slc↓ : Set
      Idx↓Slc↓Slc↓ = Σ (Idx↓ Slc↓ ((i , j) , (μ M c (fst ∘ δ) , δμ))) (λ i → Cns↓ Slc↓ i (nd (c , ν) δ ε))

      nd↓-map : Σ-δε → Idx↓Slc↓Slc↓
      nd↓-map (δ↓ , ε↓) = ((j , idp) , (μ↓ M↓ d (fst ∘ δ↓) , δ↓μ δ↓)) , nd↓ (d , typ-d=ν) δ↓ ε↓

      -- Some id-elims on decoration types
      module _ (δ↓₀ δ↓₁ : δ-set) (ε↓₀ : ε-fib δ↓₀) (ε↓₁ : ε-fib δ↓₁) where

        ap-nd↓-map : (δ↓= : δ↓₀ == δ↓₁) (ε↓= : ε↓₀ == ε↓₁ [ ε-fib ↓ δ↓= ])
          → nd↓ (d , typ-d=ν) δ↓₀ ε↓₀ == nd↓ (d , typ-d=ν) δ↓₁ ε↓₁
                [ (λ x → Cns↓ Slc↓ x (nd (c , ν) δ ε)) ↓ ap ((j , idp) ,_) (ap (λ x → μ↓ M↓ d (fst ∘ x) , δ↓μ x) δ↓=) ]
        ap-nd↓-map idp idp = idp

        idx-slc-slc-pth : (δ↓= : δ↓₀ == δ↓₁) (ε↓= : ε↓₀ == ε↓₁ [ ε-fib ↓ δ↓= ])
          → nd↓-map (δ↓₀ , ε↓₀) == nd↓-map (δ↓₁ , ε↓₁)
        idx-slc-slc-pth p q = pair= (pair= idp (ap (λ x → μ↓ M↓ d (fst ∘ x) , δ↓μ x) p))
                            (ap-nd↓-map p q) 

        slc-typ-cst : (δ↓= : δ↓₀ == δ↓₁) (ε↓= : ε↓₀ == ε↓₁ [ ε-fib ↓ δ↓= ])
          → Path {A = Path {A = Idx↓ Slc↓ ((i , j) , (c , ν))} ((j , idp) , (d , typ-d=ν)) ((j , idp) , (d , typ-d=ν))}
                 idp (ap (λ x → Typ↓ Slc↓ (snd x) true) (idx-slc-slc-pth δ↓= ε↓=) ∙ idp)
        slc-typ-cst idp idp = idp

        slc-typ-cst-coh : (δ↓= : δ↓₀ == δ↓₁) (ε↓= : ε↓₀ == ε↓₁ [ ε-fib ↓ δ↓= ])
          → (p : Pos M c) (q : Pos Slc (ε p))
          → Path {A = Path {A = Idx↓ Slc↓ (Typₛ (Pb M (Idx↓ M↓)) (ε p) q)} (Typ↓ Slc↓ (ε↓₀ p) q) (Typ↓ Slc↓ (ε↓₁ p) q)}
                 (ap (λ x → Typ↓ Slc↓ (snd x) q) (pair= (app= δ↓= p)
                   (app=↓ {A = Pos M c} {B = λ p → Cns↓ Plbk↓ (Typ↓ M↓ d p , typ-d=ν p) (δ p)}
                          {C = λ p x → Cns↓ Slc↓ ((Typ↓ M↓ d p , typ-d=ν p) , x) (ε p)} δ↓= ε↓= p)))
                 (ap (λ x → Typ↓ Slc↓ (snd x) (inr (p , q))) (idx-slc-slc-pth δ↓= ε↓=)) 
        slc-typ-cst-coh idp idp p q = idp

      module _ (δ↓₀ δ↓₁ : δ-set) (δ-eq : (p : Pos M c) → δ↓₀ p == δ↓₁ p) where

        pb-pth : Path {A = Cns↓ Plbk↓ (j , idp) (μ M c (fst ∘ δ) , δμ)}
                    (μ↓ M↓ d (fst ∘ δ↓₀) , δ↓μ δ↓₀)
                    (μ↓ M↓ d (fst ∘ δ↓₁) , δ↓μ δ↓₁)
        pb-pth = ap (λ x → μ↓ M↓ d (fst ∘ x) , δ↓μ x) (λ= δ-eq)

        module _ (ε↓₀ : ε-fib δ↓₀) (ε↓₁ : ε-fib δ↓₁)
                 (ε-eq : (p : Pos M c) → ε↓₀ p == ε↓₁ p [ (λ x → Cns↓ Slc↓ ((Typ↓ M↓ d p , typ-d=ν p) , x) (ε p)) ↓ δ-eq p ]) where

          nd↓-pth :  nd↓ {i↓ = j , idp} (d , typ-d=ν) δ↓₀ ε↓₀
                == nd↓ {i↓ = j , idp} (d , typ-d=ν) δ↓₁ ε↓₁
                     [ (λ x → Cns↓ Slc↓ x (nd (c , ν) δ ε)) ↓ ap (λ x → (j , idp) , x) pb-pth ] 
          nd↓-pth = ap-nd↓-map δ↓₀ δ↓₁ ε↓₀ ε↓₁ (λ= δ-eq) (λ=↓ δ-eq ε-eq)
