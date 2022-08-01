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
open import Core.OpetopicType
open import Core.OpetopicMap
open import Core.Universe

open import Lib.Structures
open import Lib.Terminal

open import Lib.CategoryOfTypes.Lemmas
open import Lib.CategoryOfTypes.CompositeFibrant

module Lib.CategoryOfTypes.Uniqueness where

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

    Src-hf-unique : {f : Frm↓ F} {s : USrc↓ S f}
      → (t₀ : T f) (us₀ : USrc↓ Pd (f , s , t₀))
      → (t₁ : T f) (us₁ : USrc↓ Pd (f , s , t₁))
      → Path (Σ[ t ∈ T f ] USrc↓ Pd (f , s , t)) (t₀ , us₀) (t₁ , us₁)
    Src-hf-unique {f} {s} t₀ us₀ t₁ us₁ = isContr→isProp (ucomp-is-fib-rel Pd ϕ f s) (t₀ , us₀) (t₁ , us₁)    
  
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


    postulate
    
      comp-from-to : (f : Frm↓ (F , S , T)) (uc : ucomp Pd ϕ f) → comp-from f (comp-to f uc) ≡ uc
      -- comp-from-to (f , s , t) uc = 

      --     transport (λ i → USrc↓ Pd (f , s , fst (C-hf-unique (ucomp-comp f s) (ucomp-competitor f s) t (comp-to (f , s , t) uc) i)))
      --         (ucomp-fill f s)

      --               -- This has to be some compatibility of transporting and 'ap'ing
      --               ≡⟨ {!!} ⟩

      --     transport (λ i → USrc↓ Pd (f , s , fst (Src-hf-unique (ucomp-comp f s) (ucomp-fill f s) t uc i)))
      --         (ucomp-fill f s)

      --             ≡⟨ fst (PathP≃Path (λ i → USrc↓ Pd (f , s , fst (Src-hf-unique (ucomp-comp f s) (ucomp-fill f s) t uc i))) (ucomp-fill f s) uc)
      --                 (λ i → snd (Src-hf-unique (ucomp-comp f s) (ucomp-fill f s) t uc i))  ⟩

      --     uc ∎
                
    --
    --  Now the filler ....
    --

    fill-to : (f : Frm↓ (F , S , T)) (s t : USrc↓ Pd f) → ufill Pd ϕ (f , s , t) → R (f , s , comp-to f t)
    fill-to (f , s , t) α β p = J (λ β' _ → R ((f , s , t) , α , comp-to (f , s , t) β'))
        (snd (fst (R-is-fib-rel (f , s , t) α)) ) p

    -- But I wonder if there is not a better way.  We should have
    --
    --   R (f , s , t) ≃ comp-to f s ≡ t 
    --
    -- from the fundamental theorem.
    --
    -- So shouldn't this say that we have
    --
    --  R (f , s , comp-to f t) ≃ comp-to f s ≡ comp-to f t
    --                          ≃ s ≡ t
    --
    -- Since we have already shown that the map comp-to is an equivalence.
    -- This seems correct.  Only thing to figure out, then, is how to see
    -- that this is "over" the equivalence stated....
    

  postulate

    ucomp-unique : ∀ {n ℓ} {F : Frm (𝕆U (suc n) ℓ)} (S : Src CellFib F)
      → (ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S) → is-fib-rel (S ⊚ p))
      → (C : CellFib F) (C-is-fib-rel : is-fib-rel C)
      → (R : CellFib (F , S , C)) (R-is-fib-rel : is-fib-rel R)
      → ucomp S ϕ ≡ C 

    ufill-unique : ∀ {n ℓ} {F : Frm (𝕆U (suc n) ℓ)} (S : Src CellFib F)
      → (ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S) → is-fib-rel (S ⊚ p))
      → (C : CellFib F) (C-is-fib-rel : is-fib-rel C)
      → (R : CellFib (F , S , C)) (R-is-fib-rel : is-fib-rel R)
      → (λ i → CellFib (F , S , ucomp-unique S ϕ C C-is-fib-rel R R-is-fib-rel i))
          [ ufill S ϕ ≡ R ] 

  uhorn-filler : ∀ {n ℓ} {F : Frm (𝕆U n ℓ)} (S : Src CellFib F)
      → (ϕ : (p : Pos {X = 𝕆U n ℓ} CellFib S) → is-fib-rel (S ⊚ p))
      → Type (ℓ-suc ℓ)
  uhorn-filler {F = F} S ϕ =
    Σ[ Cf ∈ (Σ[ C ∈ CellFib F ] is-fib-rel C) ]
    Σ[ R ∈ CellFib (F , S , fst Cf) ] is-fib-rel R 

  uhorn-filler-unique : ∀ {n ℓ} {F : Frm (𝕆U (suc n) ℓ)} (S : Src CellFib F)
      → (ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S) → is-fib-rel (S ⊚ p))
      → (C : CellFib F) (C-is-fib-rel : is-fib-rel C)
      → (R : CellFib (F , S , C)) (R-is-fib-rel : is-fib-rel {F = F , S , C} R)
      → Path (uhorn-filler S ϕ) ((ucomp S ϕ , ucomp-is-fib-rel S ϕ) ,
                                 (ufill S ϕ , ufill-is-fib-rel S ϕ))
                                ((C , C-is-fib-rel) , (R , R-is-fib-rel))                                 
  uhorn-filler-unique {F = F} S ϕ C C-is-fib-rel R R-is-fib-rel i =
    ((ucomp-unique S ϕ C C-is-fib-rel R R-is-fib-rel i) ,
        isOfHLevel→isOfHLevelDep 1 is-prop-is-fib-rel
          (ucomp-is-fib-rel S ϕ) C-is-fib-rel 
          (ucomp-unique S ϕ C C-is-fib-rel R R-is-fib-rel) i) ,
     (ufill-unique S ϕ C C-is-fib-rel R R-is-fib-rel i , 
       isOfHLevel→isOfHLevelDep 1
         {A = Σ[ T ∈ CellFib F ] (CellFib (F , S , T))}
         {B = λ P → is-fib-rel (snd P)}
         (λ P → is-prop-is-fib-rel (snd P))
         {a0 = (ucomp S ϕ , ufill S ϕ)} {a1 = (C , R)} 
         (ufill-is-fib-rel S ϕ) R-is-fib-rel 
           (λ j → ucomp-unique S ϕ C C-is-fib-rel R R-is-fib-rel j ,
                  ufill-unique S ϕ C C-is-fib-rel R R-is-fib-rel j) i)


    
