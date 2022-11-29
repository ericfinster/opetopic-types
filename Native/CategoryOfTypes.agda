open import Core.Prelude 
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.OpetopicTerm
open import Native.Weakening
open import Native.OpetopicMap
open import Native.Universe

open import MiniHoTT

module Native.CategoryOfTypes where

  is-fibrant-rel : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)}
    → 𝕌-cell i → Type ℓ
  is-fibrant-rel {i = objₒ , ●} P = 𝟙 _
  is-fibrant-rel {ℓ} {suc n} {(ο ∣ ._) , (f ►⟦ t ∣ s ⟧)} P = 
    (f↓ : Frm↓ (𝕍  ℓ n) f) (s↓ : Src↓ (𝕍 ℓ n) 𝕍-cell s f↓)
     → is-contr (Σ[ t↓ ∈ t f↓ ] (P (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)))

  --  The (∞,1)-category of spaces.
  𝕊 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n
  𝕊-fst : ∀ {ℓ n} → 𝕊 ℓ n ⇒ 𝕌 ℓ n 

  𝕊-cell : ∀ {ℓ n} → Idx (𝕊 ℓ n) → Type (ℓ-suc ℓ)
  𝕊-cell (ο , f) = Σ[ P ∈ 𝕌-cell (ο , Frm⇒ 𝕊-fst f) ]
                   is-fibrant-rel P

  𝕊 ℓ zero = ○
  𝕊 ℓ (suc n) = 𝕊 ℓ n ∥ 𝕊-cell 

  𝕊-fst {n = zero} = ■
  𝕊-fst {n = suc n} = 𝕊-fst {n = n} ► fst

  -- 𝒮ₙ-is-fibrant : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (3 + n) ℓ)
  -- 𝒮ₙ-is-fibrant n ℓ F S = 
  --   ((ucomp S' ϕ , ucomp-is-fib-rel S' ϕ) ,
  --    (ufill S' ϕ , ufill-is-fib-rel S' ϕ)) ,
  --    λ hf → uhorn-filler-unique S' ϕ
  --             (fst (fst hf)) (snd (fst hf))
  --             (fst (snd hf)) (snd (snd hf))

  --   where S' : Src CellFib (Frm⇒ (𝒮π (suc n) ℓ) F)
  --         S' = 𝒮ₙ-Src-to-U F S

  --         ϕ : (p : Pos {X = 𝕆U (suc n) ℓ} CellFib S') → is-fib-rel (S' ⊚ p)
  --         ϕ = 𝒮ₙ-Src-is-fib F S 

  ucomp : ∀ {ℓ n} {ο : 𝕆 n} (F : Frm (𝕌 ℓ n) ο)
    → (S : Src (𝕌 ℓ n) 𝕌-cell (ο , F))
    → 𝕌-cell (ο , F)
  ucomp {ℓ} {n} F S f↓ = Src↓ (𝕍 ℓ n) 𝕍-cell S f↓ 

  ufill : ∀ {ℓ n} {ο : 𝕆 n} (F : Frm (𝕌 ℓ n) ο)
    → (S : Src (𝕌 ℓ n) 𝕌-cell (ο , F))
    → 𝕌-cell ((ο ∣ S .fst) , (F ►⟦ ucomp F S ∣ S ⟧))
  ufill {ℓ} {n} F S (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) = s↓ == t↓

  ufill-is-fib-rel : ∀ {ℓ n} {ο : 𝕆 n} (F : Frm (𝕌 ℓ n) ο)
    → (S : Src (𝕌 ℓ n) 𝕌-cell (ο , F))
    → is-fibrant-rel (ufill F S)
  ufill-is-fib-rel F S f↓ s↓ = pathfrom-is-contr s↓ 

  -- Now the harder part
  ucomp-is-fib-rel : ∀ {ℓ n} {ο : 𝕆 n} (F : Frm (𝕌 ℓ n) ο)
    → (S : Src (𝕌 ℓ n) 𝕌-cell (ο , F))
    → (ϕ : (p : Pos (S .fst)) → is-fibrant-rel (S .snd .snd p))
    → is-fibrant-rel (ucomp F S)
  ucomp-is-fib-rel F S ϕ = {!!} 
