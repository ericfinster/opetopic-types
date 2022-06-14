open import Cubical.Foundations.Everything

open import Core.Prelude
open import Experimental.LessPositions.OpetopicType
open import Experimental.LessPositions.Shapes

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

module Experimental.LessPositions.Structures where
  record 𝕆Type∞ {n ℓ} (Xₙ : 𝕆Type n ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      Fill : Frm Xₙ → Type ℓ
      Hom : 𝕆Type∞ (Xₙ , Fill)

  open 𝕆Type∞ public

  horn-filler : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ) {f : Frm Xₙ} → Src Xₛₙ f → Type ℓ
  horn-filler {n} {ℓ} {Xₙ} {Xₛₙ} Xₛₛₙ {f} s = Σ[ tgt ∈ Xₛₙ f ] Xₛₛₙ (f , tgt , s)

  is-fibrant : ∀ {n ℓ} → 𝕆Type (suc (suc n)) ℓ → Type ℓ
  is-fibrant ((Xₙ , Xₛₙ) , Xₛₛₙ) = (f : Frm Xₙ) (s : Src Xₛₙ f) → isContr (horn-filler Xₛₛₙ s)

  record is-fibrant-ext {n ℓ} {Xₙ : 𝕆Type n ℓ} (X : 𝕆Type∞ Xₙ) : Type ℓ where
    coinductive
    field
      fill-fib : is-fibrant ((Xₙ , (Fill X)) , (Fill (Hom X)))
      hom-fib : is-fibrant-ext (Hom X)

  open is-fibrant-ext

  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Type n ℓ
  𝕋 zero = tt*
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit

  𝕋Ext : ∀ {n ℓ} (X : 𝕆Type n ℓ) → 𝕆Type∞ X
  Fill (𝕋Ext X) = λ _ → Lift Unit
  Hom (𝕋Ext X) = 𝕋Ext _

  is-fib-ext-𝕋Ext : ∀ {n ℓ} {X : 𝕆Type n ℓ} → is-fibrant-ext (𝕋Ext X)
  fill-fib is-fib-ext-𝕋Ext f s = (tt* , tt*) , λ (tt* , tt*) → refl
  hom-fib is-fib-ext-𝕋Ext = is-fib-ext-𝕋Ext





  hom→path : ∀ {ℓ} {X : 𝕆Type∞ (𝕋 {ℓ} 0)} → is-fibrant-ext X → (x y : X .Fill tt*) → X .Hom .Fill (tt* , y , x) → x ≡ y
  hom→path {ℓ} {X} fib x y σ = sym (transportRefl x) ∙ cong fst (isContr→isProp (fib .fill-fib tt* x) (Id x x refl) b) where
    Id : (x y : X .Fill tt*) → (x ≡ y) → horn-filler (Fill (Hom X)) x
    Id x y = J (λ y p → horn-filler (Fill (Hom X)) x) (x , fib .hom-fib .fill-fib (tt* , x , x) (lf x) .fst .fst)

    b : horn-filler (Fill (Hom X)) x
    b = y , σ

  Id-cell : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} (t : Fill X∞ f) → Fill (Hom X∞) (globe-Frm _ t t)
  Id-cell X∞ fib t = fib .hom-fib .fill-fib _ (lf t) .fst .fst

  path→hom : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} {t u : Fill X∞ f} → t ≡ u → Fill (Hom X∞) (globe-Frm _ t u)
  path→hom X∞ fib {t = t} {u = u} = J (λ u p → Fill (Hom X∞) (globe-Frm _ t u)) (Id-cell X∞ fib t)

  record is-n-trunc {m ℓ} (n : ℕ) {X : 𝕆Type m ℓ} (X∞ : 𝕆Type∞ X) : Type ℓ where
    coinductive
    field
      hLevel : (f : Frm X) → isOfHLevel n (X∞ .Fill f)
      is-trunc-ext : is-n-trunc (predℕ n) (X∞ .Hom)
  open is-n-trunc

  src-comp : ∀ {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) → is-fibrant-ext X∞ → {f : Frm X} → Src (Fill X∞) f → Fill X∞ f
  src-comp X∞ fib s = fib .fill-fib _ s .fst .fst

  module Cell-Charac {n ℓ} {X : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (fib : is-fibrant-ext X∞) {f : Frm X} (s : Src (Fill X∞) f) (t : Fill X∞ f) where
    cell→path : Fill (Hom X∞) (f , t , s) → src-comp X∞ fib s ≡ t
    cell→path H = cong fst test where
      test : fib .fill-fib f s .fst ≡ (t , H)
      test = (fib .fill-fib f s) .snd (t , H)

    module Pasting (H : src-comp X∞ fib s ≡ t) where
      cell1 : Fill (Hom X∞) (globe-Frm (Fill X∞) (src-comp X∞ fib s) t)
      cell1 = path→hom X∞ fib H

      cell2 : Fill (Hom X∞) (_ , src-comp X∞ fib s , s)
      cell2 = fib .fill-fib _ s .fst .snd

      src : Src (Fill (Hom X∞)) (_ , t , s)
      src = nd t (η (Branch (Fill (Hom X∞))) [ src-comp X∞ fib s , s , η (Fill (Hom X∞)) cell2 ]) cell1

    path→cell : src-comp X∞ fib s ≡ t → Fill (Hom X∞) (f , t , s)
    path→cell H = src-comp (Hom X∞) (hom-fib fib) (Pasting.src H)

    sec : section cell→path path→cell
    sec H = {!Pasting.src H!}
    
    ret : retract cell→path path→cell
    ret H = cong fst ((hom-fib fib) .fill-fib (f , t , s) (Pasting.src (cell→path H)) .snd (H , {!!}))

  {-lemma-test : ∀ {m ℓ} (n : ℕ) {X : 𝕆Type m ℓ} (X∞ : 𝕆Type∞ X) → ((f : Frm X) → isOfHLevel n (X∞ .Fill f)) → is-fibrant-ext X∞ → is-n-trunc n X∞
  hLevel (lemma-test n {X} X∞ h1 hfib) = h1
  is-trunc-ext (lemma-test n {X} X∞ h1 hfib) = lemma-test _ _ lemma (hfib .hom-fib) where
    lemma : (f : Frm (X , Fill X∞)) → isOfHLevel (predℕ n) (X∞ .Hom .Fill f)
    lemma (f , t , s) = {!!}-}

{-
  is-n-cat : ∀ {m ℓ} (n : ℕ) {X : 𝕆Type m ℓ} (X∞ : 𝕆Type∞ X) → Type ℓ
  is-n-cat zero X∞ = is-fibrant-ext X∞
  is-n-cat (suc n) X∞ = Σ (is-n-cat n (Hom X∞)) {!!}
-}
