open import Cubical.Foundations.Everything

open import Core.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Fiberwise

open import Core.OpetopicType
open import Core.OpetopicMap
open import Lib.Shapes

module Lib.Structures where

  record 𝕆Type∞ {n ℓ} (Xₙ : 𝕆Type n ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      Fill : Frm Xₙ → Type ℓ
      Hom : 𝕆Type∞ (Xₙ , Fill)
  open 𝕆Type∞ public

  record Map {n ℓ} {Xₙ Yₙ : 𝕆Type n ℓ} (σ : Xₙ ⇒ Yₙ) (X : 𝕆Type∞ Xₙ) (Y : 𝕆Type∞ Yₙ) : Type ℓ where
    coinductive
    field
      Fill⇒ : {f : Frm Xₙ} → (Fill X) f → (Fill Y) (Frm⇒ σ f)
      Hom⇒ : Map (σ , Fill⇒) (Hom X) (Hom Y)
  open Map public

  horn-filler : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ) {f : Frm Xₙ} → Src Xₛₙ f → Type ℓ
  horn-filler {n} {ℓ} {Xₙ} {Xₛₙ} Xₛₛₙ {f} s = Σ[ tgt ∈ Xₛₙ f ] Xₛₛₙ (f , s , tgt)

  is-fibrant : ∀ {n ℓ} → 𝕆Type (suc (suc n)) ℓ → Type ℓ
  is-fibrant ((Xₙ , Xₛₙ) , Xₛₛₙ) = (f : Frm Xₙ) (s : Src Xₛₙ f) → isContr (horn-filler Xₛₛₙ s)

  isProp-is-fibrant : ∀ {n ℓ} {X : 𝕆Type (suc (suc n)) ℓ} → isProp (is-fibrant X)
  isProp-is-fibrant = isPropΠ2 (λ _ _ → isPropIsContr)

  record is-fibrant-ext {n ℓ} {Xₙ : 𝕆Type n ℓ} (X : 𝕆Type∞ Xₙ) : Type ℓ where
    coinductive
    field
      fill-fib : is-fibrant ((Xₙ , (Fill X)) , (Fill (Hom X)))
      hom-fib : is-fibrant-ext (Hom X)

  open is-fibrant-ext public
  
  eta-fib-ext : ∀ {m ℓ} {X : 𝕆Type m ℓ} {X∞ : 𝕆Type∞ X} → X∞ ≡ record { Fill = Fill X∞ ; Hom = Hom X∞ }
  Fill (eta-fib-ext {X∞ = X∞} i) = Fill X∞
  Hom (eta-fib-ext {X∞ = X∞} i) = Hom X∞

  isProp-is-fibrant-ext : ∀ {n ℓ} {X : 𝕆Type n ℓ} {X∞ : 𝕆Type∞ X} → isProp (is-fibrant-ext X∞)
  fill-fib (isProp-is-fibrant-ext x y i) = isProp-is-fibrant (fill-fib x) (fill-fib y) i
  hom-fib (isProp-is-fibrant-ext x y i) = isProp-is-fibrant-ext (hom-fib x) (hom-fib y) i
  
  record is-n-trunc {m ℓ} (n : ℕ) {X : 𝕆Type m ℓ} (X∞ : 𝕆Type∞ X) : Type ℓ where
    coinductive
    field
      hLevel : (f : Frm X) → isOfHLevel n (X∞ .Fill f)
      is-trunc-ext : is-n-trunc (predℕ n) (X∞ .Hom)
  open is-n-trunc

  isProp-is-trunc : ∀ {m ℓ n} {X : 𝕆Type m ℓ} {X∞ : 𝕆Type∞ X} → isProp (is-n-trunc n X∞)
  hLevel (isProp-is-trunc x y i) f = isPropIsOfHLevel _ (hLevel x f) (hLevel y f) i
  is-trunc-ext (isProp-is-trunc x y i) = isProp-is-trunc (is-trunc-ext x) (is-trunc-ext y) i

  src-comp : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) → is-fibrant-ext X∞ → {f : Frm X} → Src (Fill X∞) f → Fill X∞ f
  src-comp X∞ fib s = fib .fill-fib _ s .fst .fst

  src-comp-witness : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib-ext : is-fibrant-ext X∞) {f : Frm X} (s : Src (Fill X∞) f)
    → Fill (Hom X∞) (f , s , src-comp X∞ fib-ext s)
  src-comp-witness X∞ fib s = fib .fill-fib _ s .fst .snd

  -- More general version of the equivalence between hom and path, using the fundamental theorem of identity types
  cell≃path : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} (s : Src (Fill X∞) f) (t : Fill X∞ f)
    → (src-comp X∞ fib s ≡ t) ≃ Fill (Hom X∞) (f , s , t)
  cell≃path X∞ fib s t = recognizeId (λ t → (Fill (Hom X∞)) (_ , s , t)) (fib .fill-fib _ s .fst .snd) (fib .fill-fib _ s) t

  isOfHLevelPathPred : ∀ (n : ℕ) {ℓ} {A : Type ℓ} → isOfHLevel n A → {x y : A} → isOfHLevel (predℕ n) (x ≡ y)
  isOfHLevelPathPred zero h = isContr→isContrPath h _ _
  isOfHLevelPathPred (suc n) h = isOfHLevelPath' n h _ _

  is-n-trunc-fib : ∀ {m ℓ} (n : ℕ) {X : 𝕆Type m ℓ} (X∞ : 𝕆Type∞ X) → is-fibrant-ext X∞ → ((f : Frm X) → isOfHLevel n (X∞ .Fill f)) → is-n-trunc n X∞
  hLevel (is-n-trunc-fib n {X} X∞ fib h) = h
  is-trunc-ext (is-n-trunc-fib n {X} X∞ fib h) = is-n-trunc-fib _ _ (fib .hom-fib) lemma where
    lemma : (f : Frm (X , Fill X∞)) → isOfHLevel (predℕ n) (X∞ .Hom .Fill f)
    lemma (f , s , t) = isOfHLevelRespectEquiv (predℕ n) (cell≃path X∞ fib s t) (isOfHLevelPathPred n (h f))

  total : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) → 𝕆Type∞ {ℓ = ℓ} tt*
  total {zero} X∞ = X∞
  total {suc n} {ℓ} {X , P} X∞ = total (record { Fill = P ; Hom = X∞ })

  𝕆∞Path : ∀ {m ℓ} {X : 𝕆Type m ℓ} {X∞ X∞' : 𝕆Type∞ X} (p : Fill X∞ ≡ Fill X∞') → PathP (λ i → 𝕆Type∞ (X , p i)) (Hom X∞) (Hom X∞') → X∞ ≡ X∞'
  Fill (𝕆∞Path p q i) = p i
  Hom (𝕆∞Path p q i) = q i

  0-trunc-≡ : ∀ {n ℓ} {X : 𝕆Type n ℓ} {X' : 𝕆Type n ℓ} (p : X ≡ X') {X∞ : 𝕆Type∞ X} {X∞' : 𝕆Type∞ X'}
    → is-n-trunc 0 X∞ → is-n-trunc 0 X∞'
    → PathP (λ i → 𝕆Type∞ (p i)) X∞ X∞'
  Fill (0-trunc-≡ p {X∞} {X∞'} trunc trunc' i) = eq i where
    eq : PathP (λ i → Frm (p i) → Type _) (Fill X∞) (Fill X∞')
    eq = toPathP (funExt λ f → isoToPath (isContr→Iso (trunc .hLevel _) (trunc' .hLevel _)))
  Hom (0-trunc-≡ p trunc trunc' i) = 0-trunc-≡ (λ j → p j , Fill (0-trunc-≡ p trunc trunc' j)) (trunc .is-trunc-ext) (trunc' .is-trunc-ext) i

  --
  --  The skeleton of an infinite opetopic type
  --
  
  Skeleton : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type n ℓ

  SkeletonExt : ∀ {ℓ} (X : 𝕆Type∞ {ℓ = ℓ} tt*)
    → (n : ℕ) → 𝕆Type∞ {ℓ = ℓ} (Skeleton X n) 

  Skeleton X zero = lift tt
  Skeleton X (suc n) = Skeleton X n , Fill (SkeletonExt X n)

  SkeletonExt X zero = X
  SkeletonExt X (suc n) = Hom (SkeletonExt X n)
