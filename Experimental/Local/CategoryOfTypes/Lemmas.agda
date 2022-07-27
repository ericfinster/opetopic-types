{-# OPTIONS --no-positivity-check --no-termination-check #-}
--
--  Universe.agda - The opetopic type of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat 

open import Core.Prelude
open import Experimental.Local.OpetopicType
open import Experimental.Local.Universe

module Experimental.Local.CategoryOfTypes.Lemmas where

  --
  --  Helper notation for working in the universal fibration
  --
  
  UFrm : (n : ℕ) (ℓ : Level) → Type (ℓ-suc ℓ)
  UFrm n ℓ = Frm (𝕆U n ℓ)

  USrc : ∀ {n ℓ} → UFrm n ℓ → Type (ℓ-suc ℓ)
  USrc F = Src CellFib F 

  UPos : ∀ {n ℓ} {F : UFrm n ℓ} (S : USrc F) → Type (ℓ-suc ℓ)
  UPos {n} {ℓ} {F} S = Pos {X = 𝕆U n ℓ} CellFib S

  USrc↓ : ∀ {n ℓ} {F : UFrm n ℓ} (S : USrc F) → Frm↓ F → Type ℓ
  USrc↓ S f = Src↓ {X = CellFib} (λ C → C) S f 

  ηU : ∀ {n ℓ} {F : UFrm n ℓ}
    → CellFib F → USrc F
  ηU {n} {ℓ} C = η {X = 𝕆U n ℓ} CellFib C 

  μU : ∀ {n ℓ} (F : UFrm n ℓ)
    → Src (Src CellFib) F → Src CellFib F
  μU {n} {ℓ} F S = μ {X = 𝕆U n ℓ} CellFib {f = F} S 

  νU : ∀ {n ℓ} 
    → {Q : UFrm n ℓ → Type (ℓ-suc ℓ)}
    → {F : UFrm n ℓ} (S : USrc F)
    → (ϕ : (p : Pos CellFib S) → Q (Typ CellFib S p))
    → Src {X = 𝕆U n ℓ} Q F
  νU {n} {ℓ} {Q} {F} S ϕ = ν {X = 𝕆U n ℓ} {P = CellFib} {Q = Q} {f = F} S ϕ 

  ηU-pos : ∀ {n ℓ} {F : UFrm n ℓ} (C : CellFib F)
    → Pos {X = 𝕆U n ℓ} CellFib (ηU C)
  ηU-pos {n} {ℓ} C = η-pos {X = 𝕆U n ℓ} CellFib C

  ηU↓ : ∀ {n ℓ} {F : UFrm n ℓ} (C : CellFib F)
    → {f : Frm↓ F} → C f → USrc↓ (ηU C) f
  ηU↓ C c = η↓ (λ C → C) {C = C} c

  μU↓ : ∀ {n ℓ} {F : UFrm n ℓ} (S : Src (Src CellFib) F)
    → {f : Frm↓ F} (s : Src↓ (Src↓ (λ C → C)) S f)
    → USrc↓ (μU F S) f
  μU↓ {F = F} S s = μ↓ {X = CellFib} (λ C → C) {F = F} {S = S} s 

  canopyU : ∀ {n ℓ}
    → {F : UFrm n ℓ} (S : Src CellFib F)
    → (D : Dec (Branch {X = 𝕆U n ℓ} {P = CellFib} CellFib) {f = F} S)
    → Src CellFib F
  canopyU {n} {ℓ} {F} S D =
    canopy {X = 𝕆U n ℓ} {P = CellFib} CellFib
      {f = F} {s = S} D 

  canopyU' : ∀ {n ℓ}
    → {X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ)}
    → {F : UFrm n ℓ} (S : Src CellFib F)
    → (D : (p : UPos {F = F} S) → Branch X (S ⊚ p))
    → Src CellFib F
  canopyU' {n} {ℓ} {F} S D = 
    μ {X = 𝕆U n ℓ} CellFib (ν S λ p → lvs (D p))

  --
  --  General lemmas
  --
  
  Dec↓-≡ : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ))
    → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
    → (Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src X F) (D : Dec {X = 𝕆U n ℓ} Y S)
    → {f : Frm↓ F} (s : Src↓ P S f)
    → (δ₀ δ₁ : Dec↓ Y Q S D s)
    → (ϕ : (p : Pos X S) → δ₀ ⊛↓ p ≡ δ₁ ⊛↓ p)
    → δ₀ ≡ δ₁
  Dec↓-≡ {zero} Y Q S D s δ₀ δ₁ ϕ = ϕ tt*
  Dec↓-≡ {suc n} Y Q (lf tgt) D s δ₀ δ₁ ϕ = refl
  Dec↓-≡ {suc n} {ℓ} {X} Y {P} Q (nd S T C Brs) (_ , D) (nd↓ src tgt flr brs) (q₀ , δ₀) (q₁ , δ₁) ϕ i =
    ϕ nd-here i , Dec↓-≡ {n = n} {X = λ F → Σ (CellFib F) (Branch X)}
                     (λ CB → Dec {X = 𝕆U n ℓ , CellFib} Y (br (snd CB)))
                     {P = λ pr f → Σ (fst pr f) (Branch↓ X P (snd pr))}
                     (λ {F} {CB} D' {f} cb → Dec↓ Y Q (br (snd CB)) D' (br↓ (snd cb)))
                     (ν {Q = λ F → Σ (CellFib F) (Branch X)} S (λ p → S ⊚ p , Brs ⊛ p)) D
                     (ν↓ {Y = λ F → Σ (CellFib F) (Branch X)} src (λ p → src ⊚↓ p , brs ⊛↓ p)) δ₀ δ₁
                     (λ p → let p' = ν-lift S (λ q → (S ⊚ q) , (Brs ⊛ q)) p
                            in Dec↓-≡ Y Q (br (Brs ⊛ p')) (D ⊛ p) (br↓ (brs ⊛↓ p')) (δ₀ ⊛↓ p) (δ₁ ⊛↓ p)
                              (λ q → ϕ (nd-there p' q))) i

  branch-lem : ∀ {n ℓ} 
    → (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    → (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (C : CellFib F)
    → {f : Frm↓ F} (c : C f)
    → (b : Branch↓ X P [ η {X = 𝕆U n ℓ} CellFib C , lf C ] c)
    → [ η↓ (λ C → C) {C = C} c , lf↓ c ]↓ ≡ b 
  branch-lem X P C c [ ._ , lf↓ .c ]↓ = refl

  -- Obviously not the most general, but I think there's something
  -- screwy with our fibration setup in the universe file ...
  η↓-dec : ∀ {n ℓ} 
    → {F : Frm (𝕆U n ℓ)} {S : Src CellFib F} 
    → {f : Frm↓ F} (s : Src↓ {X = CellFib} (λ C → C) S f)
    → Dec↓ {X = CellFib} (Branch CellFib) (Branch↓ CellFib (λ C → C)) {F = F} S
      (η-dec CellFib {f = F} S) s
  η↓-dec {n} {ℓ} {F} {S} src =
    λ-dec↓ {X = CellFib} {Y = Branch CellFib} (Branch↓ CellFib (λ C → C)) {F = F} {S = S}
      (η-dec {X = 𝕆U n ℓ} {P = CellFib} CellFib S)
      (λ p → [ η↓ (λ C → C) {C = S ⊚ p} (src ⊚↓ p) , lf↓ (src ⊚↓ p) ]↓)

  canopy↓ : ∀ {n ℓ}
    → (X : (F : Frm (𝕆U (suc n) ℓ)) → Type (ℓ-suc ℓ))
    → (P : {F : Frm (𝕆U (suc n) ℓ)} → X F → (f : Frm↓ F) → Type ℓ) 
    → {F : Frm (𝕆U n ℓ)} {S : Src CellFib F}
    → {D : Dec {X = 𝕆U n ℓ} (Branch X) S}
    → {f : Frm↓ F} {s : Src↓ {X = CellFib} (λ C → C) S f}
    → Dec↓ (Branch X) (Branch↓ X P) S D s
    → Src↓ {X = CellFib} (λ C → C) (canopy X D) f
  canopy↓ X P {F} {S} {f = frm} {s = src} brs =
    μ↓ {X = CellFib} (λ C → C) {F = F} (ν↓ {X = CellFib} {Y = Src CellFib}
       {P = λ C → C} {Q = Src↓ {X = CellFib} (λ C → C)} {F = F} {S = S}
       {f = frm} src (λ p → lvs↓ (brs ⊛↓ p)))

  -- A lemma about commuting transport
  transport-natural : ∀ {ℓ₀ ℓ₁} {A : Type ℓ₀} {B C : A → Type ℓ₁}
    → (ϕ : (a : A) → B a → C a)
    → {a₀ a₁ : A} (b₀ : B a₀) (p : a₀ ≡ a₁) 
    → ϕ a₁ (transport (λ i → B (p i)) b₀) ≡
      transport (λ i → C (p i)) (ϕ a₀ b₀)
  transport-natural {B = B} {C} ϕ {a₀} {a₁} b₀ =
    J (λ a p → ϕ a (transport (λ i → B (p i)) b₀) ≡
               transport (λ i → C (p i)) (ϕ a₀ b₀))
      (ϕ a₀ (transport (λ i → B a₀) b₀)   ≡[ i ]⟨ ϕ a₀ (transportRefl b₀ i) ⟩
       ϕ a₀ b₀                            ≡[ i ]⟨ transportRefl (ϕ a₀ b₀) (~ i) ⟩
       transport (λ i → C a₀) (ϕ a₀ b₀)   ∎) 


