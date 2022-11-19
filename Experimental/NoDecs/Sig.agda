--
--  Sigma.agda - Dependent sum of opetopic families
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Universe

module Experimental.NoDecs.Sig where

  Sigma : ∀ {n ℓ} (A : 𝕆Type n ℓ) (B : A ⇒ 𝕆U n ℓ)
    → Σ[ Σₒ ∈ 𝕆Type n ℓ ]
      Σ[ Σ-fst ∈ Σₒ ⇒ A ]
      Σ[ Σ-snd ∈ Σₒ ⇒ 𝕆V n ℓ ]
      𝕆π n ℓ ⊙ Σ-snd ≡ B ⊙ Σ-fst

  Sigma {zero} A B = tt* , tt* , tt* , refl
  Sigma {suc n} {ℓ} (A , A') (B , B') with Sigma {n} A B
  ... | (Σₒ , Σ-fst , Σ-snd , Σ-≡) = 
    (Σₒ , Σₒ') , (Σ-fst , Σ-fst') ,
    (Σ-snd , Σ-snd') , Σ-≡'

    where  Σₒ' : Frm Σₒ → Type ℓ
           Σₒ' F = Σ[ a ∈ A' (Frm⇒ Σ-fst F) ]
                  B' a (Frm⇒ Σ-snd F) (λ i → Frm⇒ (Σ-≡ i) F) 

           Σ-fst' : {f : Frm Σₒ} → Σₒ' f → A' (Frm⇒ Σ-fst f)
           Σ-fst' {f} = fst 

           Σ-snd' : {f : Frm Σₒ} → Σₒ' f
             → Σ[ P ∈ FillingFamily (Frm⇒ (𝕆π n ℓ ⊙ Σ-snd) f) ]
               P (Frm⇒ Σ-snd f) refl
           Σ-snd' {f} (a , b) = (λ f' e → B' a f' (e ∙ λ i → Frm⇒ (Σ-≡ i) f)) ,
                                transp (λ j → B' a (Frm⇒ Σ-snd f) (lUnit (λ i → Frm⇒ (Σ-≡ i) f) j)) i0 b

           Σ-≡' : _⊙_ {X = Σₒ , Σₒ'} {Y = 𝕆V (suc n) ℓ} {Z = 𝕆U (suc n) ℓ} (𝕆π n ℓ , fst) (Σ-snd , Σ-snd') ≡
                  _⊙_ {X = Σₒ , Σₒ'} {Y = A , A'} {Z = 𝕆U (suc n) ℓ} (B , B') (Σ-fst , Σ-fst') 
           Σ-≡' i = Σ-≡ i , λ {f} ab f' e → B' (fst ab) f' {!!} 


  -- So I think we need to use univalence to show that the two B'
  -- families we obtain are equivalent to each other.  But the
  -- cubical primitives are really confusing me here.

  -- B' (fst ab) f' e = ?0 (i = i1) : Type ℓ (blocked on _164)
  -- B' (fst ab) f' (e ∙ (λ j → Frm⇒ (Σ-≡ j) f)) = ?0 (i = i0)

