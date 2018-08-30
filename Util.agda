{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Util where

  -- Used for the "inspect idiom" in proofs below
  
  data Graph {ℓ : ULevel} {X : Type ℓ} {Y : X → Type ℓ} (f : ∀ x → Y x) (x : X) (y : Y x) : Type ℓ where
    ingraph : f x == y → Graph f x y

  inspect : ∀ {ℓ} {X : Type ℓ} {Y : X → Type ℓ} (f : ∀ x → Y x) (x : X) → Graph f x (f x)
  inspect f x = ingraph idp

  -- Needed for a lemma.

  apd↓-cst :  ∀ {i j} {A : Type i} {B C : A → Type j} (f : {a : A} → B a → C a)
    {x y : A} {p : x == y} {u : B x} {v : B y}
    → u == v [ B ↓ p ]
    → f u == f v [ C ↓ p ]
  apd↓-cst f {p = idp} idp = idp

  to-transp-↓ : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
    (p : a₁ == a₂) (y : P a₁) → y == transport P p y [ P ↓ p ]
  to-transp-↓ _ idp _ = idp

  ↓-apd-lem : ∀ {i j k} {A : Type i} {B : A → Type j} (C : (a : A) → B a → Type k)
    (f : Π A B) {x y : A} (p : x == y)
    {u : C x (f x)} {v : C y (f y)}
    → u == v [ uncurry C ↓ pair= p (apd f p) ]
    → u == v [ (λ a → C a (f a)) ↓ p ]
  ↓-apd-lem C f idp idp = idp

  any-contr-eqv : ∀ {i j} {A : Type i} {B : Type j}
    → (a-ct : is-contr A)
    → (b-ct : is-contr B)
    → (f : A → B)
    → is-equiv f
  any-contr-eqv {A = A} {B = B} a-ct b-ct f =
    is-eq f (λ _ → contr-center a-ct)
      (λ b → contr-has-all-paths ⦃ b-ct ⦄ (f (contr-center a-ct)) b)
      (λ a → contr-path a-ct a)

  prop-transp : ∀ {i j} {A : Type i} {B : A → Type j}
    → {a₀ a₁ : A} (p : a₀ == a₁)
    → (isp : (a : A) → is-prop (B a))
    → (b₀ : B a₀) (b₁ : B a₁)
    → b₀ == b₁ [ B ↓ p ]
  prop-transp idp isp b₀ b₁ = prop-has-all-paths ⦃ isp _ ⦄ b₀ b₁

  equiv-== : ∀ {i j} {A : Type i} {B : Type j}
    → {f g : A ≃ B} (e : (a : A) → fst f a == fst g a) → f == g
  equiv-== {f = f , f-eq} {g = g , g-eq} e =
    pair= (λ= e) (prop-transp (λ= e)
          (λ ϕ → is-equiv-is-prop {f = ϕ}) f-eq g-eq)

  ↓-equiv-in : ∀ {i j k} {A : Type i}
    → {B : (a : A) → Type j} {C : (a : A) → Type k}
    → {a₀ a₁ : A} {p : a₀ == a₁}
    → {e : B a₀ ≃ C a₀} {f : B a₁ ≃ C a₁}
    → (r : (b₀ : B a₀) (b₁ : B a₁) (s : b₀ == b₁ [ B ↓ p ])
           → fst e b₀ == fst f b₁ [ C ↓ p ])
    → e == f [ (λ a → B a ≃ C a) ↓ p ]
  ↓-equiv-in {p = idp} r = equiv-== (λ b → r b b idp)

  contr-contr-eqv : ∀ {i j} {A : Type i} {B : Type j}
    → (a-ct : is-contr A)
    → (b-ct : is-contr B)
    → A ≃ B
  contr-contr-eqv {A = A} {B = B} a-ct b-ct =
    equiv to from to-from from-to

    where to : A → B
          to a = contr-center b-ct

          from : B → A
          from b = contr-center a-ct

          to-from : (b : B) → to (from b) == b
          to-from b = contr-has-all-paths ⦃ b-ct ⦄ (to (from b)) b

          from-to : (a : A) → from (to a) == a
          from-to a = contr-has-all-paths ⦃ a-ct ⦄ (from (to a)) a

  ⊔-emap : ∀ {i i' j j'} {A : Type i} {A' : Type i'}
    → {B : Type j} {B' : Type j'}
    → A ≃ B → A' ≃ B' → A ⊔ A' ≃ B ⊔ B'
  ⊔-emap {A = A} {A' = A'} {B = B} {B' = B'} e f =
    equiv to from to-from from-to

    where to : A ⊔ A' → B ⊔ B'
          to (inl a) = inl (–> e a)
          to (inr a') = inr (–> f a')

          from : B ⊔ B' → A ⊔ A'
          from (inl b) = inl (<– e b)
          from (inr b') = inr (<– f b')

          to-from : (b : B ⊔ B') → to (from b) == b
          to-from (inl b) = <– (inl=inl-equiv (–> e (<– e b)) b) (<–-inv-r e b)
          to-from (inr b') = <– (inr=inr-equiv (–> f (<– f b')) b') (<–-inv-r f b')

          from-to : (a : A ⊔ A') → from (to a) == a
          from-to (inl a) = <– (inl=inl-equiv (<– e (–> e a)) a) (<–-inv-l e a)
          from-to (inr a') = <– (inr=inr-equiv (<– f (–> f a')) a') (<–-inv-l f a')
