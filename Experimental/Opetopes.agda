--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Core.Prelude

module Experimental.Opetopes where

  -- Okay.  I wonder about this idea of defining *just* the families
  -- need for the opetopes.

  data 𝒪 : (n : ℕ) → Type
  data 𝒫 : (n k : ℕ) (o : 𝒪 n) → Type 

  data 𝒪 where

    ● : 𝒪 0
    _∣_ : {n : ℕ} (o : 𝒪 n) → 𝒫 n 0 o → 𝒪 (suc n) 

  η : {n : ℕ} (o : 𝒪 n) → 𝒫 n 0 o 
  υ : {n k : ℕ} (o : 𝒪 n) (p : 𝒫 n k o) → 𝒫 n 0 o 
  μ : {n k : ℕ} (o : 𝒪 n) (p : 𝒫 n k o) → 𝒫 n 0 o 
  
  data 𝒫 where

    lfₒ : {n : ℕ} (o : 𝒪 n)
      → 𝒫 (suc n) 0 (o ∣ η o) 
      
    ndₒ : {n k : ℕ} {o : 𝒪 n}
      → (p : 𝒫 n k o)
      → (q : 𝒫 (suc n) k (o ∣ υ o p))
      → 𝒫 (suc n) k (o ∣ μ o p)

  η = {!!} 
  υ = {!!} 
  μ = {!!} 

  
