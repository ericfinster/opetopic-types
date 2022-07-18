open import Cubical.Foundations.Everything

open import Core.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Fiberwise

open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Shapes

module Experimental.Local.Structures where

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

--   hom→path0 : ∀ {ℓ} {X : 𝕆Type∞ (𝕋 {ℓ} 0)} → is-fibrant-ext X → (x y : X .Fill tt*) → X .Hom .Fill (tt* , x , y) → x ≡ y
--   hom→path0 {ℓ} {X} fib x y σ = sym (transportRefl x) ∙ cong fst (isContr→isProp (fib .fill-fib tt* x) (Id x x refl) b) where
--     Id : (x y : X .Fill tt*) → (x ≡ y) → horn-filler (Fill (Hom X)) x
--     Id x y = J (λ y p → horn-filler (Fill (Hom X)) x) (x , fib .hom-fib .fill-fib (tt* , x , x) (lf x) .fst .fst)

--     b : horn-filler (Fill (Hom X)) x
--     b = y , σ

--   Id-cell : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} (t : Fill X∞ f) → Fill (Hom X∞) (globe-Frm _ t t)
--   Id-cell X∞ fib t = fib .hom-fib .fill-fib _ (lf t) .fst .fst

--   path→hom : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} {t u : Fill X∞ f}
--     → t ≡ u → Fill (Hom X∞) (globe-Frm _ t u)
--   path→hom X∞ fib {t = t} {u = u} = J (λ u p → Fill (Hom X∞) (globe-Frm _ t u)) (Id-cell X∞ fib t)

--   hom→path : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} {t u : Fill X∞ f}
--     → Fill (Hom X∞) (globe-Frm _ t u) → t ≡ u
--   hom→path X∞ fib {f} {t} {u} cell = cong fst (isContr→isProp (fib .fill-fib f (η (Fill X∞) t)) (t , Id-cell X∞ fib t) (u , cell))

--   module IsoHomPath {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} {t u : Fill X∞ f} where
--     sec : section (path→hom X∞ fib {f} {t} {u}) (hom→path X∞ fib {f} {t} {u})
--     sec cell = fromPathP (cong snd (isContr→isProp (fib .fill-fib f (η (Fill X∞) t)) (t , Id-cell X∞ fib t) (u , cell)))
--     -- Wow ! Might need to take a look back at this later cause I didn't expect it to be so "simple".

--     ret : retract (path→hom X∞ fib {f} {t} {u}) (hom→path X∞ fib {f} {t} {u})
--     ret = J (λ u p → hom→path X∞ fib (path→hom X∞ fib p) ≡ p)
--       (hom→path X∞ fib (path→hom X∞ fib refl)
--         ≡⟨ cong (hom→path X∞ fib) (transportRefl _) ⟩
--       hom→path X∞ fib (Id-cell X∞ fib t)
--         ≡⟨ (λ i j → fst (test i j)) ⟩
--       refl ∎) where
--         a : horn-filler (Fill (Hom X∞)) (η (Fill X∞) t)
--         a = (t , Id-cell X∞ fib t)

--         test0 : a ≡ a
--         test0 = isContr→isProp (fib .fill-fib f (η (Fill X∞) t)) (t , Id-cell X∞ fib t) (t , Id-cell X∞ fib t)

--         test : test0 ≡ refl
--         test = isProp→isSet (isContr→isProp (fib .fill-fib f (η (Fill X∞) t))) (t , Id-cell X∞ fib t) (t , Id-cell X∞ fib t) test0 refl

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

--   𝕆∞Path : ∀ {m ℓ} {X : 𝕆Type m ℓ} (X∞ X∞' : 𝕆Type∞ X) (p : Fill X∞ ≡ Fill X∞') → PathP (λ i → 𝕆Type∞ (X , p i)) (Hom X∞) (Hom X∞') → X∞ ≡ X∞'
--   Fill (𝕆∞Path X∞ X∞' p q i) = p i
--   Hom (𝕆∞Path X∞ X∞' p q i) = q i

--   -- Trying to prove that fibrant opetopic types with same base-type are equal
-- {-
--   lemma0 : ∀ {m ℓ} {X X' : 𝕆Type m ℓ} (p : X ≡ X')
--     → (P : Frm X → Type ℓ) (P' : Frm X' → Type ℓ)
--     → (q : PathP (λ i → Frm (p i) → Type ℓ) P P')
--     → (P∞ : 𝕆Type∞ (X , P)) (P∞' : 𝕆Type∞ (X' , P'))
--     → is-fibrant-ext (record {Fill = P ; Hom = P∞}) → is-fibrant-ext (record { Fill = P' ; Hom = P∞' })
--     → PathP (λ i → Frm (p i , q i) → Type ℓ) (Fill P∞) (Fill P∞')
--   lemma0 {ℓ = ℓ} {X = X} =
--     J
--       (λ X' p → (P : Frm X → Type ℓ) (P' : Frm X' → Type ℓ)
--         → (q : PathP (λ i → Frm (p i) → Type ℓ) P P')
--         → (P∞ : 𝕆Type∞ (X , P)) (P∞' : 𝕆Type∞ (X' , P'))
--         → is-fibrant-ext (record {Fill = P ; Hom = P∞}) → is-fibrant-ext (record { Fill = P' ; Hom = P∞' })
--         → PathP (λ i → Frm (p i , q i) → Type ℓ) (Fill P∞) (Fill P∞'))
        
--     λ P _ → J

--       (λ P' q → (P∞ : 𝕆Type∞ (X , P)) (P∞' : 𝕆Type∞ (X , P'))
--       → is-fibrant-ext (record {Fill = P ; Hom = P∞}) → is-fibrant-ext (record { Fill = P' ; Hom = P∞' })
--       → PathP (λ i → Frm (refl i , q i) → Type ℓ) (Fill P∞) (Fill P∞'))
 
--     λ P∞ _ fib fib' → funExt λ x → ua (invEquiv (cell≃path _ fib _ _)) ∙ cong (_≡ (snd (snd x))) {!!} ∙ ua (cell≃path _ fib' _ _)
      
--   fibrant→≡ : ∀ {m ℓ} {X X' : 𝕆Type m ℓ} (p : X ≡ X')
--     → (X∞ : 𝕆Type∞ X) (X∞' : 𝕆Type∞ X') → PathP (λ i → Frm (p i) → Type ℓ) (Fill X∞) (Fill X∞')
--     → is-fibrant-ext X∞ → is-fibrant-ext X∞'
--     → PathP (λ i → 𝕆Type∞ (p i)) X∞ X∞'
--   Fill (fibrant→≡ p X∞ X∞' q fib fib' i) = q i
--   Hom (fibrant→≡ {ℓ = ℓ} p X∞ X∞' q fib fib' i) = fibrant→≡ (λ i → (p i , q i)) (Hom X∞) (Hom X∞') lemma (hom-fib fib) (hom-fib fib') i where
--     lemma : PathP (λ i → Frm (p i , q i) → Type ℓ) (Fill (Hom X∞)) (Fill (Hom X∞'))
--     lemma  = lemma0 p _ _ _ (Hom X∞) (Hom X∞') (subst is-fibrant-ext eta-fib-ext fib) (subst is-fibrant-ext eta-fib-ext fib')
-- -}
-- {-
--   is-n-cat : ∀ {m ℓ} (n : ℕ) {X : 𝕆Type m ℓ} (X∞ : 𝕆Type∞ X) → Type ℓ
--   is-n-cat zero X∞ = is-fibrant-ext X∞
--   is-n-cat (suc n) X∞ = Σ (is-n-cat n (Hom X∞)) {!!}
-- -}
