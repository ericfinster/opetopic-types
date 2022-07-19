--
--  Category.agda - Equivalence between categories and 1-truncated (∞,1)-categories
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.Shapes
open import Experimental.Local.Structures
open import Experimental.Local.Terminal


module Experimental.Local.Category where

postulate
  {-test-rewrite : ∀ {n ℓ} {X : 𝕆Type n ℓ} (P : Frm X → Type ℓ) (U : Frm (X , P) → Type ℓ)
    → {frm : Frm X} {src : Src P frm} {tgt : P frm}
    → (s : Src U (frm , src , tgt ))
    → γ U s (λ p → [ _ , lf (src ⊚ p) ]) ↦ s
  {-# REWRITE test-rewrite #-}-}

  test-rewrite2 : ∀ {ℓ} {X : 𝕆Type 0 ℓ} (P : Frm X → Type ℓ) (U : Frm (X , P) → Type ℓ)
    → {tgt : P tt*}
    → (lvs : P tt*)
    → (br : Pd U (tt* , lvs , tgt))
    → γ {X = X} {P = P} U {src = lvs} br (λ p → [ lvs , lf (lvs) ]) ↦ br
  {-# REWRITE test-rewrite2 #-}


module Cat-to-∞Cat {ℓ} (C : Category ℓ ℓ) where
  open Category C renaming (id to C-id ; _⋆_ to _⨀_)

  n-comp : {n : ℕ} {t : ob ** (suc n)} → path-chain Hom[_,_] n t → Hom[ last t , fstt t ]
  n-comp {zero} {x} _ = C-id
  n-comp {suc zero} {y , x} f = f
  n-comp {suc (suc n)} {y , x , t} (f , l) = n-comp {suc n} {x , t} l ⨀ f

  X₀ : Frm (𝕋 {ℓ = ℓ} 0) → Type ℓ
  X₀ _ = ob

  X₁ : Frm (tt* , X₀) → Type ℓ
  X₁ (_ , x , y) = Hom[ x , y ]

  C-src-comp : {f : Frm (tt* , X₀)} → Src X₁ f → X₁ f
  C-src-comp (lf tgt) = C-id {x = tgt}
  C-src-comp (nd src tgt flr brs) = C-src-comp (br brs) ⨀ flr

  X₂ : Frm ((tt* , X₀) , X₁) → Type ℓ
  X₂ (f , s , t) = C-src-comp s ≡ t

  {-# TERMINATING #-}
  big-lemma : {f : Frm (tt* , X₀)} (brs : Src (Src X₁) f) →
    C-src-comp (μ X₁ brs) ≡
    C-src-comp (ν {Q = X₁} brs λ p → C-src-comp (brs ⊚ p))
  big-lemma (lf tgt) = refl
  big-lemma (nd src .src (lf .src) brs) = big-lemma (br brs) ∙ sym (⋆IdR _)
  big-lemma (nd ._ tgt (nd src .tgt flr lbrs) brs) =
    cong (_⨀ flr) (big-lemma (nd (lvs lbrs) src (br lbrs) brs)) ∙
    (⋆Assoc _ (C-src-comp (br lbrs)) flr)

  {-# TERMINATING #-}
  C-2-src-comp : {f : Frm ((tt* , X₀) , X₁)} → Src X₂ f → X₂ f
  C-2-src-comp (lf tgt) = ⋆IdL tgt
  C-2-src-comp (nd src tgt flr brs) =
    big-lemma (ν {Q = Pd X₁} src (λ p → lvs (brs ⊛ p))) ∙ IH ∙ flr
                                                               
    where IH : C-src-comp (ν {Q = X₁} src (λ p → C-src-comp (lvs (brs ⊛ p)))) ≡ 
               C-src-comp src
          IH i =  C-src-comp (ν {Q = X₁} src (λ p → C-2-src-comp (br (brs ⊛ p)) i))

  Nerve : 𝕆Type∞ {ℓ = ℓ} tt*
  Fill Nerve = X₀
  Fill (Hom Nerve) = X₁
  Fill (Hom (Hom Nerve)) = X₂
  Hom (Hom (Hom Nerve)) = 𝕋Ext _

  open is-fibrant-ext

  lemma : ∀ {ℓ} {A : Type ℓ} {a : A} → isContr (Σ[ b ∈ A ] a ≡ b)
  lemma {a = a} = (a , refl) , (λ (b , p) i → (p i , λ j → p (i ∧ j)))

  isInfCatCat : is-fibrant-ext (Hom Nerve)
  fill-fib isInfCatCat f s = lemma
  hom-fib (hom-fib isInfCatCat) = is-fib-ext-𝕋Ext
  fill-fib (hom-fib isInfCatCat) (f , s , t) s' = (C-2-src-comp s' , tt*) , λ y → Σ≡Prop (λ _ _ _ → refl) (isSetHom _ _ _ _)

  is-trunc-Nerve : is-n-trunc 2 (Hom Nerve)
  is-trunc-Nerve = is-n-trunc-fib _ _ isInfCatCat (λ _ → isSetHom)

open Cat-to-∞Cat public

module _ {ℓ} (X : 𝕆Type∞ (𝕋 {ℓ} 0)) (infCat : is-fibrant-ext (Hom X)) (hom-trunc : is-n-trunc 2 (Hom X)) where
  obj : Type ℓ
  obj = Fill X tt*

  Mor : obj → obj → Type ℓ
  Mor x y = Fill (Hom X) (_ , x , y)

  Idt : {x : obj} → Mor x x
  Idt {x} = src-comp (Hom X) infCat (lf _)

  Comp : {x y z : obj} → Mor x y → Mor y z → Mor x z
  Comp f g = src-comp (Hom X) infCat (n-path (Fill (Hom X)) 2 (g , f))

  -- There is a lot that can be factored here
  ⋆leftUnit : ∀ {x y} (f : Mor x y) → Comp Idt f ≡ f
  ⋆leftUnit {x} {y} f = cong fst (isContr→isProp (infCat .fill-fib _ _) horn2 horn1) where
    horn1 : horn-filler (Fill (Hom (Hom X))) (η (Fill (Hom X)) f)
    horn1 = f , src-comp (Hom (Hom X)) (infCat .hom-fib) (lf f)

    horn2 : horn-filler (Fill (Hom (Hom X))) (η (Fill (Hom X)) f)
    horn2 = _ , infCat .hom-fib .fill-fib _ src .fst .fst where
      src : Src (Fill (Hom (Hom X))) _
      src = left-unitor-Src _ _ (Fill (Hom (Hom X)))
        x y Idt f (Comp Idt f)
        (src-comp-witness (Hom X) infCat _)
        (src-comp-witness (Hom X) infCat (lf _))

  ⋆rightUnit : ∀ {x y} (f : Mor x y) → Comp f Idt ≡ f
  ⋆rightUnit {x} {y} f = cong fst (isContr→isProp (infCat .fill-fib _ _) horn2 horn1) where
    horn1 : horn-filler (Fill (Hom (Hom X))) (η (Fill (Hom X)) f)
    horn1 = f , src-comp (Hom (Hom X)) (infCat .hom-fib) (lf f)

    horn2 : horn-filler (Fill (Hom (Hom X))) (η (Fill (Hom X)) f)
    horn2 = _ , infCat .hom-fib .fill-fib _ src .fst .fst where
      src : Src (Fill (Hom (Hom X))) _
      src = right-unitor-Src _ _ (Fill (Hom (Hom X)))
        x y Idt f (Comp f Idt)
        (src-comp-witness (Hom X) infCat _)
        (src-comp-witness (Hom X) infCat (lf _))

  ⋆assoc : ∀ {x y z w} (f : Mor x y) (g : Mor y z) (h : Mor z w) → Comp (Comp f g) h ≡ Comp f (Comp g h)
  ⋆assoc {x} {y} {z} {w} f g h = cong fst (isContr→isProp (infCat .fill-fib _ _) horn1 horn2) where
    horn1 : horn-filler (Fill (Hom (Hom X))) _
    horn1 = _ , infCat .hom-fib .fill-fib _ src .fst .fst where
      src : Src (Fill (Hom (Hom X))) _
      src = left-associator-Src _ _ (Fill (Hom (Hom X))) x y z w f g h (Comp f g) (Comp (Comp f g) h)
        (src-comp-witness (Hom X) infCat _)
        (src-comp-witness (Hom X) infCat _)

    horn2 : horn-filler (Fill (Hom (Hom X))) _
    horn2 = _ , infCat .hom-fib .fill-fib _ src .fst .fst where
      src : Src (Fill (Hom (Hom X))) _
      src = right-associator-Src _ _ (Fill (Hom (Hom X))) x y z w f g h (Comp g h) (Comp f (Comp g h))
        (src-comp-witness (Hom X) infCat _)
        (src-comp-witness (Hom X) infCat _)

  CoNerve : Category ℓ ℓ
  Category.ob CoNerve = obj
  Category.Hom[_,_] CoNerve = Mor
  Category.id CoNerve = Idt
  Category._⋆_ CoNerve = Comp
  Category.⋆IdL CoNerve = ⋆leftUnit
  Category.⋆IdR CoNerve = ⋆rightUnit
  Category.⋆Assoc CoNerve = ⋆assoc
  Category.isSetHom CoNerve {x = x} {y = y} = is-n-trunc.hLevel hom-trunc (_ , x , y)


∞Cat : (ℓ : Level) → Type (ℓ-suc ℓ)
∞Cat ℓ = Σ[ X ∈ 𝕆Type∞ (𝕋 {ℓ} 0) ] is-fibrant-ext (Hom X)

1-Cat : (ℓ : Level) → Type (ℓ-suc ℓ)
1-Cat ℓ = Σ[ X ∈ 𝕆Type∞ (𝕋 {ℓ} 0) ] is-fibrant-ext (Hom X) × is-n-trunc 2 (Hom X)

Cat→1-Cat : {ℓ : Level} → Category ℓ ℓ → 1-Cat ℓ
Cat→1-Cat {ℓ} C = Nerve C , isInfCatCat C , is-trunc-Nerve C

1-Cat→Cat : {ℓ : Level} → 1-Cat ℓ → Category ℓ ℓ
1-Cat→Cat {ℓ} (X , infCat , hom-trunc) = CoNerve X infCat hom-trunc

sec : {ℓ : Level} → section (Cat→1-Cat {ℓ}) 1-Cat→Cat
sec (X , infCat , hom-trunc) = Σ≡Prop (λ X → isProp× isProp-is-fibrant-ext isProp-is-trunc) eq where
  eq2 : (f : Frm ((tt* , Fill X) , Fill (Hom X))) → Fill (Hom (Hom (Nerve (CoNerve X infCat hom-trunc)))) f ≡ Fill (Hom (Hom X)) f
  eq2 (f , x , y) = cong (_≡ y) (lemm f x) ∙ ua (cell≃path (Hom X) infCat x y) where
    lemm : (f : Frm (tt* , Fill X)) (x : Src (Fill (Hom X)) f)
      → C-src-comp (CoNerve X infCat hom-trunc) x ≡ src-comp (Hom X) infCat x
    lemm _ (lf tgt) = refl
    lemm _ (nd src tgt flr brs) = cong (λ x → infCat .fill-fib _ x .fst .fst) p1 ∙ p2 where
      p1 :
        nd {U = Fill (Hom X)} src tgt flr ([ lvs brs , nd (lvs brs) src (C-src-comp (CoNerve X infCat hom-trunc) (br brs)) ([ lvs brs , lf (lvs brs) ]) ])
        ≡
        nd src tgt flr ([ lvs brs , nd (lvs brs) src (src-comp _ infCat (br brs)) ([ lvs brs , lf (lvs brs) ]) ])
      p1 = cong (λ t → nd src tgt flr ([ lvs brs , nd (lvs brs) src t ([ lvs brs , lf (lvs brs) ]) ])) (lemm _ (br brs))

      p2 : src-comp _ infCat (n-path (Fill (Hom X)) 2 (flr , src-comp _ infCat (br brs))) ≡ src-comp _ infCat (nd src tgt flr brs)
      p2 = cong fst (isContr→isProp (infCat .fill-fib _ _) horn2 horn1) where
        horn1 : horn-filler (Fill (Hom (Hom X))) _
        horn1 = infCat .fill-fib _ (nd src tgt flr brs) .fst

        horn2 : horn-filler (Fill (Hom (Hom X))) _
        horn2 =
          src-comp _ infCat (n-path (Fill (Hom X)) 2 (flr , src-comp _ infCat (br brs))) ,
          src-comp _ (infCat .hom-fib) (nd
            (n-path (Fill (Hom X)) 2 (flr , src-comp _ infCat (br brs)))
            _
            (src-comp-witness _ infCat _)
            ([ _ , lf flr ] , [ br brs , η (Fill (Hom (Hom X))) (src-comp-witness _ infCat _) ] , tt*))

  eq : Nerve (CoNerve X infCat hom-trunc) ≡ X
  Fill (eq i) _ = Fill X tt*
  Fill (Hom (eq i)) (_ , x , y) = Fill (Hom X) (_ , x , y)
  Fill (Hom (Hom (eq i))) f = {!!}
  Hom (Hom (Hom (eq i))) = {!!}

module _ where
  open Category renaming (id to idt)
  Category≡' : ∀ {ℓ ℓ'} (C C' : Category ℓ ℓ')
    → (p-ob : ob C ≡ ob C')
    → (p-hom : PathP (λ i → p-ob i → p-ob i → Type ℓ') (Hom[_,_] C) (Hom[_,_] C'))
    → (p-id : PathP (λ i → {x : p-ob i} → p-hom i x x) (idt C) (idt C'))
    → (p-⋆ : PathP (λ i → {x y z : p-ob i} → p-hom i x y → p-hom i y z → p-hom i x z) (_⋆_ C) (_⋆_ C'))
    → (p-⋆IdL : PathP (λ i → {x y : p-ob i} → (f : p-hom i x y) → p-⋆ i (p-id i) f ≡ f) (⋆IdL C) (⋆IdL C'))
    → (p-⋆IdR : PathP (λ i → {x y : p-ob i} → (f : p-hom i x y) → p-⋆ i f (p-id i) ≡ f) (⋆IdR C) (⋆IdR C'))
    → (p-⋆Assoc : PathP (λ i → {x y z w : p-ob i} → (f : p-hom i x y) (g : p-hom i y z) (h : p-hom i z w) →
                  p-⋆ i (p-⋆ i f g) h ≡ p-⋆ i f (p-⋆ i g h)) (⋆Assoc C) (⋆Assoc C'))
    → (p-isSetHom : PathP (λ i → {x y : p-ob i} → isSet (p-hom i x y)) (isSetHom C) (isSetHom C'))
    → C ≡ C'
  ob (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-ob i
  Hom[_,_] (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-hom i
  idt (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-id i
  _⋆_ (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-⋆ i
  ⋆IdL (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-⋆IdL i
  ⋆IdR (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-⋆IdR i
  ⋆Assoc (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-⋆Assoc i
  isSetHom (Category≡' C C' p-ob p-hom p-id p-⋆ p-⋆IdL p-⋆IdR p-⋆Assoc p-isSetHom i) = p-isSetHom i

  Category≡ : ∀ {ℓ ℓ'} {C C' : Category ℓ ℓ'}
    → (p-ob : ob C ≡ ob C')
    → (p-hom : PathP (λ i → p-ob i → p-ob i → Type ℓ') (Hom[_,_] C) (Hom[_,_] C'))
    → (p-id : PathP (λ i → {x : p-ob i} → p-hom i x x) (idt C) (idt C'))
    → (p-⋆ : PathP (λ i → {x y z : p-ob i} → p-hom i x y → p-hom i y z → p-hom i x z) (_⋆_ C) (_⋆_ C'))
    → C ≡ C'
  Category≡ {C = C} {C' = C'} p-ob p-hom p-id p-⋆ = Category≡' C C' p-ob p-hom p-id p-⋆
    (toPathP (implicitFunExt (implicitFunExt (funExt λ f → isSetHom C' _ _ _ _))))
    (toPathP (implicitFunExt (implicitFunExt (funExt λ f → isSetHom C' _ _ _ _))))
    (toPathP (implicitFunExt (implicitFunExt (implicitFunExt (implicitFunExt (funExt (λ f → funExt (λ g → funExt (λ h → isSetHom C' _ _ _ _)))))))))
    (toPathP (implicitFunExt (implicitFunExt (isPropIsSet _ _))))


ret : {ℓ : Level} → retract (Cat→1-Cat {ℓ}) 1-Cat→Cat
ret C = Category≡ refl refl refl
  (implicitFunExt (implicitFunExt (implicitFunExt (funExt (λ f → funExt (λ g → ⋆Assoc _ _ _ ∙ ⋆IdL _)))))) where
  open Category C
