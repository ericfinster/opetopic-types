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

module Experimental.Local.CategoryOfTypes.Sketch where

  𝒮ₙ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮π : (n : ℕ) (ℓ : Level) → 𝒮ₙ n ℓ ⇒ 𝕆U n ℓ

  𝒮ₙ zero ℓ = tt*
  𝒮ₙ (suc n) ℓ = 𝒮ₙ n ℓ , λ f →
    Σ[ C ∈ CellFib (Frm⇒ (𝒮π n ℓ) f) ]
    is-fib-rel C
  
  𝒮π zero ℓ = tt*
  𝒮π (suc n) ℓ = 𝒮π n ℓ , fst

  𝒮Ext : (n : ℕ) (ℓ : Level) → 𝕆Type∞ (𝒮ₙ n ℓ)
  Fill (𝒮Ext n ℓ) = snd (𝒮ₙ (suc n) ℓ)
  Hom (𝒮Ext n ℓ) = 𝒮Ext (suc n) ℓ

  --
  --  Composition and filling in 𝒮
  --

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

  𝒮ₙ-Src-to-U : ∀ {n ℓ} (F : Frm (𝒮ₙ n ℓ))
    → Src (snd (𝒮ₙ (suc n) ℓ)) F
    → USrc (Frm⇒ (𝒮π n ℓ) F)
  𝒮ₙ-Src-to-U {n} {ℓ} F S = Src⇒ {f = F} S (𝒮π n ℓ) (λ p → fst (S ⊚ p))

  𝒮ₙ-Src-is-fib : ∀ {n ℓ} (F : Frm (𝒮ₙ n ℓ))
    → (S : Src (snd (𝒮ₙ (suc n) ℓ)) F)
    → (p : Pos {X = 𝕆U n ℓ} CellFib (𝒮ₙ-Src-to-U F S)) → is-fib-rel (𝒮ₙ-Src-to-U F S ⊚ p)
  𝒮ₙ-Src-is-fib {n} {ℓ} F S p = snd (S ⊚ Pos⇐ S (𝒮π n ℓ) (λ q → fst (S ⊚ q)) p)  

  𝒮ₙ-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (3 + n) ℓ)
  𝒮ₙ-is-fibrant n ℓ F S = 
    ((ucomp S' ϕ , ucomp-is-fib-rel S' ϕ) ,
     (ufill S' ϕ , ufill-is-fib-rel S' ϕ)) ,
     λ hf → uhorn-filler-unique S' ϕ
              (fst (fst hf)) (snd (fst hf))
              (fst (snd hf)) (snd (snd hf))

    where S' : Src CellFib (Frm⇒ (𝒮π (suc n) ℓ) F)
          S' = 𝒮ₙ-Src-to-U F S

          ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S') → is-fib-rel (S' ⊚ p)
          ϕ = 𝒮ₙ-Src-is-fib F S 

  𝒮Ext-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant-ext (𝒮Ext (suc n) ℓ)
  fill-fib (𝒮Ext-is-fibrant n ℓ) = 𝒮ₙ-is-fibrant n ℓ 
  hom-fib (𝒮Ext-is-fibrant n ℓ) = 𝒮Ext-is-fibrant (suc n) ℓ

  𝒮 : (ℓ : Level) → ∞Cat (ℓ-suc ℓ)
  𝒮 ℓ = 𝒮Ext 0 ℓ , 𝒮Ext-is-fibrant 0 ℓ 

