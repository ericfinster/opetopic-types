--
--  MappingLemmas.agda
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty 
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.MappingLemmas where

  module _ {n ℓ}
    {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
    (U : Frm (X , P) → Type ℓ)
    where
    
    Cover : Σ[ f₀ ∈ Frm (X , P) ] Pd U f₀ → Σ[ f₁ ∈ Frm (X , P) ] Pd U f₁ → Type ℓ 
    Cover (._ , lf {f₀} tgt₀) (._ , lf {f₁} tgt₁) = (f₀ , tgt₀) ≡ (f₁ , tgt₁)
    Cover (,_ , lf tgt₀) (._ , nd tgt₁ brs₁ flr₁) = Lift ⊥
    Cover (,_ , nd tgt₀ brs₀ flr₀) (._ , lf tgt₁) = Lift ⊥
    Cover (,_ , nd {f₀} tgt₀ brs₀ flr₀) (._ , nd {f₁} tgt₁ brs₁ flr₁) =
      (f₀ , tgt₀ , brs₀ , flr₀) ≡ (f₁ , tgt₁ , brs₁ , flr₁)

    reflCode : (x : Σ[ f ∈ Frm (X , P) ] Pd U f) → Cover x x
    reflCode (._ , lf tgt) = refl
    reflCode (._ , nd tgt brs flr) = refl

    encode : ∀ xs ys → (p : xs ≡ ys) → Cover xs ys
    encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

    encodeRefl : ∀ xs → encode xs xs refl ≡ reflCode xs
    encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

    decode : ∀ xs ys → Cover xs ys → xs ≡ ys
    decode (._ , lf {f₀} tgt₀) (._ , lf {f₁} tgt₁) c i = (c i .fst , η P (c i .snd) , c i .snd) , lf (c i .snd)
    decode (._ , lf tgt₀) (._ , nd tgt₁ brs₁ flr₁) ()
    decode (._ , nd tgt₀ brs₀ flr₀) (._ , lf tgt₁) ()
    decode (._ , nd {f₀} tgt₀ brs₀ flr₀) (._ , nd {f₁} tgt₁ brs₁ flr₁) c i =
      (c i .fst , μ (id-map X) (Branch U) P (c i .snd .snd .fst) (λ p → lvs ((c i .snd .snd .fst) ⊚ p)) , c i .snd .fst) ,
        nd (c i .snd .fst) (c i .snd .snd .fst) (c i .snd .snd .snd) 

    decodeRefl : ∀ xs → decode xs xs (reflCode xs) ≡ refl
    decodeRefl (._ , lf tgt) = refl
    decodeRefl (._ , nd tgt brs flr) = refl

    decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
    decodeEncode xs _ =
      J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
        (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)

    -- A leaf and an endomorphism of some element both sit in the same
    -- fame.  But these diagrams are not equal to each other.
    lf≠nd : (f : Frm X) (x : P f) (u : U (f , η P x , x))
      → lf {U = U} {f = f} x ≡ nd x (η (Branch U) [ x , η P x , lf x ]) u
      → Lift {j = ℓ} ⊥ 
    lf≠nd f x u e = encode _ _ (ΣPathP (refl , e)) 

  eta-lem : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → (q : Q (Frm⇒ σ f))
    → map-src σ P Q s ϕ ≡ η Q q
    → P f
  eta-lem {zero} σ P Q s ϕ q e = s
  eta-lem {suc n} (σₙ , σₛₙ) P Q (lf {f} tgt) ϕ q e = rec* (lf≠nd Q (Frm⇒ σₙ f) (σₛₙ tgt) q e)
  eta-lem {suc n} σ P Q (nd tgt brs flr) ϕ q e = {!encode Q _ _ (ΣPathP (refl , e))!}

 
