open import Core.Prelude 
open import Native.Opetopes
open import Native.OpetopicType
open import Native.Term 

module Native.Groupoid where

  Grp : ∀ {ℓ} → Type ℓ → (n : ℕ) → 𝕆Type ℓ n

  GrpTerm : ∀ {ℓ} (X : Type ℓ)
    → (n : ℕ) → 𝕆Term (Grp X n)
    
  data GrpCell {ℓ n} (X : Type ℓ) : Idx (Grp X n) → Type ℓ where

    reflₒ : (ο : 𝕆 n) → GrpCell X (ο , TermFrm (Grp X n) (GrpTerm X n) ο)

  Grp X zero = ●
  Grp X (suc n) = Grp X n , GrpCell X
  
  GrpTerm X zero = ●
  GrpTerm X (suc n) = GrpTerm X n , reflₒ

