--
--  Sketch.agda - sketch of cat of types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.OpetopicMap
open import Experimental.Local.Structures
open import Experimental.Local.Terminal
open import Experimental.Local.Universe

open import Experimental.Local.CategoryOfTypes.Lemmas

module Experimental.Local.CategoryOfTypes.Uniqueness where

  ucomp : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → CellFib F
  ucomp {F = F} S ϕ = USrc↓ {F = F} S 

  ufill : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → CellFib (F , S , ucomp S ϕ)
  ufill S ϕ (f , s , t) = s ≡ t 

  ufill-is-fib-rel : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
    → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
    → is-fib-rel (ufill S ϕ)
  ufill-is-fib-rel S ϕ f s = isContrSingl s

  postulate

    ucomp-is-fib-rel : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
      → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
      → is-fib-rel (USrc↓ {F = F} S)                 

  module _ {n ℓ} (F : UFrm n ℓ) (S : USrc F) (T : CellFib F)
    (Pd : Src CellFib (F , S , T))
    (ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib Pd) → is-fib-rel (Pd ⊚ p))
    (C : CellFib (F , S , T)) (C-is-fib-rel : is-fib-rel C)
    (R : CellFib ((F , S , T) , Pd , C)) (R-is-fib-rel : is-fib-rel R) where

    ucomp-comp : (f : Frm↓ F) (s : USrc↓ S f) → T f
    ucomp-comp f s = fst (fst (ucomp-is-fib-rel Pd ϕ f s))
    
    ucomp-fill : (f : Frm↓ F) (s : USrc↓ S f) → USrc↓ Pd (f , s , ucomp-comp f s)
    ucomp-fill f s = snd (fst (ucomp-is-fib-rel Pd ϕ f s))

    ucomp-competitor : (f : Frm↓ F) (s : USrc↓ S f) → C (f , s , ucomp-comp f s)
    ucomp-competitor f s = fst (fst (R-is-fib-rel (f , s , ucomp-comp f s) (ucomp-fill f s)))
    
    C-hf-unique : {f : Frm↓ F} {s : USrc↓ S f}
      → (t₀ : T f) (c₀ : C (f , s , t₀))
      → (t₁ : T f) (c₁ : C (f , s , t₁))
      → Path (Σ[ t ∈ T f ] C (f , s , t)) (t₀ , c₀) (t₁ , c₁)
    C-hf-unique {f} {s} t₀ c₀ t₁ c₁ = isContr→isProp (C-is-fib-rel f s) (t₀ , c₀) (t₁ , c₁)   

    comp-to : (f : Frm↓ (F , S , T)) → ucomp Pd ϕ f → C f
    comp-to (f , s , t) uc = fst (fst (R-is-fib-rel (f , s , t) uc)) 

    comp-from : (f : Frm↓ (F , S , T)) → C f → ucomp Pd ϕ f
    comp-from (f , s , t) c =
      transport (λ i → USrc↓ Pd (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t c i)))
                (ucomp-fill f s)

    comp-to-from : (f : Frm↓ (F , S , T)) (c : C f) → comp-to f (comp-from f c) ≡ c
    comp-to-from (f , s , t) c =
    
      fst (fst (R-is-fib-rel (f , s , t) 
        (transport (λ i → USrc↓ Pd (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t c i)))
                (ucomp-fill f s))))
                
        ≡⟨ transport-natural {A = Frm↓ (F , S , T)} {B = ucomp Pd ϕ} {C = C}
              comp-to {a₁ = f , s , t} (ucomp-fill f s) (λ i → (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t c i))) ⟩

      transport (λ i → C (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t c i)))
              (ucomp-competitor f s)
      
        ≡⟨ fst (PathP≃Path (λ i → C (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t c i))) (ucomp-competitor f s) c)
           (λ i → snd (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t c i)) ⟩
           
      c ∎ 

    -- Hmm.  More interesting this one ...
    comp-from-to : (f : Frm↓ (F , S , T)) (uc : ucomp Pd ϕ f) → comp-from f (comp-to f uc) ≡ uc
    comp-from-to (f , s , t) uc = 

        transport (λ i → USrc↓ Pd (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t (comp-to (f , s , t) uc) i)))
                (ucomp-fill f s)

                ≡⟨ {!!} ⟩

        uc ∎
                

