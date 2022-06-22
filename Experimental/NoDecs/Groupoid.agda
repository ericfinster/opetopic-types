--
--  Groupoid.agda - Infinity Groupoids
--

open import Cubical.Foundations.Everything renaming (_∙_ to _⊛_ ; rUnit to RUnit ; lUnit to LUnit ; assoc to Assoc)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty 
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.Groupoid where
  Grp : ∀ {ℓ} (X : Type ℓ) → (n : ℕ) → 𝕆Type n ℓ
  Pt : ∀ {n ℓ} {X : Type ℓ} (x : X) → 𝕋 n ⇒ (Grp X n)

  data GrpCell {n ℓ} (X : Type ℓ) : Frm (Grp X n) → Type ℓ where
    reflₒ : (x : X) {f : Frm (𝕋 n)} → GrpCell X (Frm⇒ (Pt x) f)

  Grp X zero = tt*
  Grp X (suc n) = Grp X n , GrpCell X

  Pt {zero} x = tt*
  Pt {suc n} x = Pt x , λ _ → reflₒ x

  GrpJ : ∀ {ℓ ℓ'} (X : Type ℓ) {n : ℕ} (P : (f : Frm (Grp X n)) → GrpCell X f → Type ℓ') →
    ((x : X) (f : Frm (𝕋 n)) → P (Frm⇒ (Pt x) f) (reflₒ x)) →
    {f : Frm (Grp X n)} (t : GrpCell X f) → P f t
  GrpJ X P base-case (reflₒ x) = base-case x _


  Grp∞ : ∀ {ℓ} (X : Type ℓ) (n : ℕ) → 𝕆Type∞ (Grp X n)
  Fill (Grp∞ X n) = GrpCell X
  Hom (Grp∞ X n) = Grp∞ X (suc n)
  {-
  Grp-Comp : ∀ {ℓ} (X : Type ℓ) (n : ℕ) {f : Frm (Grp X (suc n))} (s : Src (GrpCell X) f) → horn-filler {suc n} (GrpCell X) s
  Grp-Comp X n (lf (reflₒ x)) = (reflₒ x {_ , η {n} _ _ , tt*}) , reflₒ x {_ , lf tt* , tt*}
  Grp-Comp X n (nd tgt brs flr) = {!!}
  -}
  {-is-fib-Grp : ∀ {ℓ} (X : Type ℓ) (n : ℕ) → is-fibrant-ext (Grp∞ X n)
  fill-fib (is-fib-Grp X n) f s = {!GrpJ X ? ? {f} !}
  hom-fib (is-fib-Grp X n) = is-fib-Grp X (suc n)-}

  {-GrpJ : ∀ {ℓ ℓ'} (X : Type ℓ) (P : (f : Frm (Grp X 1)) (s : Src (GrpCell X) f) → Type ℓ') →
    ((x : X) (f : Frm (𝕋 1)) → P {!!} {!!}) → --P (Frm⇒ (Pt x) f) {!!}) →
    {f : Frm (Grp X 1)} (s : Src (GrpCell X) f) → P f s
  GrpJ X P base-case {.(_ , η (λ f → GrpCell X tt*) (reflₒ x) , reflₒ x)} (lf (reflₒ x)) = base-case x _
  GrpJ X P base-case (nd (reflₒ x) [ _ , lvs₁ , br₁ ] (reflₒ .x)) = {!!}-}

  module _ {ℓ} (X : Type ℓ) where
    -- Alternative presentation of Grp
    Grp2 : (n : ℕ) → 𝕆Type n ℓ
    Grp2Cell : (n : ℕ) → Frm (Grp2 n) → Type ℓ
    Grp2Comp : (n : ℕ) {f : Frm (Grp2 n)} → Src (Grp2Cell n) f → Grp2Cell n f

    Grp2 zero = tt*
    Grp2 (suc n) = (Grp2 n) , Grp2Cell n

    Grp2Cell zero f = X
    Grp2Cell (suc n) (f , s , t) = Grp2Comp n s ≡ t

    Grp2∞ : (n : ℕ) → 𝕆Type∞ (Grp2 n)
    Fill (Grp2∞ n) = Grp2Cell n
    Hom (Grp2∞ n) = Grp2∞ (suc n)

    lemma : ∀ {ℓ} {A : Type ℓ} {a : A} → isContr (Σ[ b ∈ A ] a ≡ b)
    lemma {a = a} = (a , refl) , (λ (b , p) i → (p i , λ j → p (i ∧ j)))

    is-fib-Grp2 : (n : ℕ) → is-fibrant-ext (Grp2∞ n)
    fill-fib (is-fib-Grp2 n) f s = lemma
    hom-fib (is-fib-Grp2 n) = is-fib-Grp2 (suc n)

    Grp2η : (n : ℕ) {f : Frm (Grp2 n)} (x : Grp2Cell n f) → Grp2Comp n (η (Grp2Cell n) x) ≡ x
    Grp2μ : (n : ℕ) {P : Frm (Grp2 n) → Type ℓ} {f : Frm (Grp2 n)} (brs : Src P f) →
      (m : (p : Pos P brs) → Src (Grp2Cell n) (Frm⇒ (id-map _) (Typ P brs p))) →
      Grp2Comp n (μ (id-map _) P (Grp2Cell n) brs m) ≡
      Grp2Comp n (μ (id-map _) P (Grp2Cell n) brs λ p → η (Grp2Cell n) (Grp2Comp n (m p)))

    abstract
      infixr 30 _∙_
      _∙_ : {l : Level} {A : Type l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      _∙_ = _⊛_

      rUnit : {l : Level} {A : Type l} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
      rUnit = RUnit

      lUnit : {l : Level} {A : Type l} {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
      lUnit = LUnit

      assoc : {l : Level} {A : Type l} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ∙ q ∙ r ≡ (p ∙ q) ∙ r
      assoc = Assoc

    {-# TERMINATING #-}
    Grp2Comp zero {f} x = x
    --Grp2Comp (suc zero) (lf tgt) = refl
    --Grp2Comp (suc zero) (nd tgt brs flr) = Grp2Comp 1 (br brs) ∙ flr
    Grp2Comp (suc n) (lf tgt) = Grp2η n tgt
    Grp2Comp (suc n) (nd tgt brs flr) = (Grp2μ n {Branch (Grp2Cell (suc n))} brs (λ p → lvs (brs ⊚ p)) ∙ ii) ∙ flr where
      i : (p : Pos (Branch (Grp2Cell (suc n))) brs) → Grp2Comp n (lvs (brs ⊚ p)) ≡ (stm (brs ⊚ p))
      i p = Grp2Comp (suc n) (br (brs ⊚ p))

      ii :
        Grp2Comp n (μ (id-map (Grp2 n)) (Branch (Grp2Cell (suc n))) (Grp2Cell n) brs
        (λ p → η (Grp2Cell n) (Grp2Comp n (lvs (brs ⊚ p)))))
        ≡
        Grp2Comp n (μ (id-map (Grp2 n)) (Branch (Grp2Cell (suc n))) (Grp2Cell n) brs
        (λ p → η (snd (Grp2 (suc n))) (stm (brs ⊚ p))))
      ii = cong (λ x → Grp2Comp n (μ (id-map (Grp2 n)) (Branch (Grp2Cell (suc n))) (Grp2Cell n) brs x))
           (funExt λ p → cong (η (Grp2Cell n)) (i p))

    -- Probably need some rewrite rules at some point...
    Grp2μ zero {P} brs m = refl
    Grp2μ (suc n) {P} brs m = {!!}

    Grp2η zero {f} x = refl
    Grp2η (suc zero) {f , s , t} x = sym (lUnit _ ∙ lUnit _ ∙ assoc _ _ _ ∙ refl)
    Grp2η (suc (suc n)) {f} x = {!!}
