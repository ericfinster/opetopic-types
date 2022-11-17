
open import Core.Prelude
open import Native.Opetopes

module Native.Examples where

  --
  --  The following elimination principle is useful for
  --  constructing explicit examples.
  --

  lf-dec : ∀ {ℓ n} {ο : 𝕆 n}
    → {P : TrPos (lfₒ ο) → Type ℓ}
    → (p : TrPos (lfₒ ο)) → P p
  lf-dec ()

  nd-dec : ∀ {ℓ n} {ο : 𝕆 n} {ρ : ℙ ο}
    → {δ : (p : Pos ρ) → Branch (Typ ρ p)}
    → {P : TrPos (ndₒ ρ δ) → Type ℓ}
    → (here* : P here)
    → (there* : (p : Pos ρ) (q : Pos (br (δ p))) → P (there p q))
    → (p : TrPos (ndₒ ρ δ)) → P p
  nd-dec here* there* here = here*
  nd-dec here* there* (there p q) = there* p q

  --
  --  Examples 
  --
  
  obj : 𝕆 0
  obj = ●

  arr : 𝕆 1
  arr = _ , ●

  drop : 𝕆 2
  drop = _ , lfₒ ●

  glob : 𝕆 2
  glob = _ , ndₒ ● (cst ⟨ lfₒ ● ⟩)

  simplex : 𝕆 2
  simplex = _ , ndₒ ● (cst ⟨ ndₒ ● (cst ⟨ lfₒ ● ⟩) ⟩)

  mickey : 𝕆 3
  mickey = simplex , ndₒ (snd simplex)
    (nd-dec ⟨ ηₒ glob ⟩
    (cst (nd-dec ⟨ ηₒ glob ⟩
    (cst lf-dec))))

  unit-l : 𝕆 3
  unit-l = glob , ndₒ (snd simplex)
    (nd-dec ⟨ ndₒ (lfₒ ●) lf-dec ⟩
    (cst (nd-dec ⟨ ηₒ glob ⟩
    (cst lf-dec))))

  unit-r : 𝕆 3
  unit-r = glob , ndₒ (snd simplex) 
    (nd-dec ⟨ ηₒ glob ⟩
    (cst (nd-dec ⟨ ndₒ (lfₒ ●) lf-dec ⟩
    (cst lf-dec))))

