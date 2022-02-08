--
--  OpetopicType.agda - Definition of Opetopic Types in Context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Core.Everything
open import Lib.Structures 

module Lib.Universe where

  -- The universe as an opetopic type 
  𝒰ₒ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒱ₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ

  𝒰ₒ zero ℓ = lift tt
  𝒰ₒ (suc n) ℓ = 𝒰ₒ n ℓ , λ f → Frm↓ (𝒱ₒ n) f → Type ℓ
  
  𝒱ₒ zero = lift tt
  𝒱ₒ (suc n) = 𝒱ₒ n , λ f↓ X → X f↓

  --
  --  Let's get set up for some of the main theorems
  --

  is-fibrant-rel : ∀ {n ℓ} {𝑜 : 𝒪 n} {f : Frm (𝒰ₒ n ℓ) 𝑜}
    → (X : Frm↓ (𝒱ₒ n) f → Type ℓ) → Type ℓ
  is-fibrant-rel {zero} X = Lift Unit
  is-fibrant-rel {suc n} {𝑜 = 𝑜 , 𝑝} {f , Xₙ , c , Yₙ} R = 
    (f↓ : Frm↓ (𝒱ₒ n) f) (c↓ : Cns↓ (𝒱ₒ n) f↓ c)
    (y↓ : (p : Pos 𝑝) → Yₙ p (Shp↓ (𝒱ₒ n) c↓ p))
     → isContr (Σ[ x↓ ∈ Xₙ f↓ ] R (f↓ , x↓ , c↓ , y↓)) 

  -- The dependent type of fibrancy
  ℱₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ
  ℱₒ zero = tt*
  ℱₒ (suc n) = ℱₒ n , λ _ X → is-fibrant-rel X
  
  -- We can now define the (∞,1)-category of spaces:
  𝒮ₙ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮ₙ n ℓ = Σₒ (𝒰ₒ n ℓ) (ℱₒ n) 

  -- Right, so this I think is now correct.  Just needs to be cleaned up
  -- and written in a way which is comprehensible....
  CompRel : ∀ {n ℓ} {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑡 : 𝒯r 𝑝}
    → (f : Frm (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) 𝑜)
    → (X : Σ (Frm↓ (𝒱ₒ n) (fst-frm f) → Type ℓ) is-fibrant-rel)
    → (c : Cns (Σₒ (𝒰ₒ n ℓ) (ℱₒ n)) f 𝑝)
    → (Y : (p : Pos 𝑝) → Σ (Frm↓ (𝒱ₒ n) (Shp (𝒰ₒ n ℓ) (fst-cns c) p) → Type ℓ) is-fibrant-rel)
    → (ω : Web (Σₒ (𝒰ₒ n ℓ) (ℱₒ n))
           (λ f₁ → Σ (Frm↓ (𝒱ₒ n) (fst-frm f₁) → Type ℓ) is-fibrant-rel)
           (f , X , c , Y) 𝑡)
    → (R : (p : 𝒯rPos 𝑡) →
        snd (fst (𝒮ₙ (suc (suc (suc n))) ℓ))
        (WebShp (fst (fst (fst (𝒮ₙ (suc (suc (suc n))) ℓ))))
         (snd (fst (fst (𝒮ₙ (suc (suc (suc n))) ℓ)))) ω p))
    → Frm↓ (𝒱ₒ (suc n)) (fst-frm f , fst X , fst-cns c , (λ p → fst (Y p))) → Type ℓ
  CompRel {n} {𝑡 = 𝑡} f X c Y ω R f↓ =
    Σ[ ω↓ ∈ Cns↓ (𝒱ₒ (suc n)) f↓ (fst-cns {P = ℱₒ (suc n)} ω) ]
    ((p : 𝒯rPos 𝑡) → fst (R p) {!Shp↓ (𝒱ₒ (suc n)) ω↓ ?!})
    -- (Shp↓ (𝒱ₒ (suc n)) ω↓ p))  

  -- Ah.  Annoying.  So we can't have the shape computing functions
  -- local because then the rewrites don't fire and we have to repeat
  -- everything.  So you'll have to change this...

  thm : (n : ℕ) (ℓ : Level) → is-fibrant (𝒮ₙ (suc (suc (suc n))) ℓ)
  thm n ℓ {𝑜 , 𝑝} {𝑡} {f , X , c , Y} ω R =
    ((CompRel f X c Y ω R , {!!}) , {!!}) , {!!}
