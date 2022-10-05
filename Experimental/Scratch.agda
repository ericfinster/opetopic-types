--
--  Scratch.agda - Random things I'm working on 
--

open import Core.Prelude

module Experimental.Scratch where

  data Tele : Type₁ where
    ■ : Tele
    _∣_ : (A : Type) (B : A → Tele) → Tele 
  
  data El : Tele → Type where
    ● : El ■
    _∥_ : {A : Type} {B : A → Tele}
      (a : A) (b : El (B a)) → El (A ∣ B)

  record Arity (I : Type₁) : Type₁ where
    constructor ⟪_,_⟫ 
    field
      T : Tele
      ϕ : El T → I

  open Arity

  μ-tele : (T : Tele) (S : El T → Tele) → Tele
  μ-tele ■ S = S ●
  μ-tele (A ∣ B) S = A ∣ λ a → μ-tele (B a) (λ b → S (a ∥ b))

  μ-tele-fst : (T : Tele) (S : El T → Tele)
    → El (μ-tele T S) → El T
  μ-tele-fst ■ S e = ●
  μ-tele-fst (A ∣ B) S (a ∥ e) = a ∥ (μ-tele-fst (B a) (λ b → S (a ∥ b)) e)

  μ-tele-snd : (T : Tele) (S : El T → Tele)
    → (e : El (μ-tele T S)) → El (S (μ-tele-fst T S e))
  μ-tele-snd ■ S e = e
  μ-tele-snd (A ∣ B) S (a ∥ e) = μ-tele-snd (B a) (λ b → S (a ∥ b)) e

  μ : (I : Type₁) → Arity (Arity I) → Arity I
  μ I α = ⟪ μ-tele (T α) (λ t → T (ϕ α t)) ,
            (λ e → ϕ (ϕ α (μ-tele-fst (T α) (λ t → T (ϕ α t)) e)) (μ-tele-snd (T α) (λ t → T (ϕ α t)) e)) ⟫

  -- So, I mean, this kind of works.  But this isn't the terminal
  -- monad anymore, is it?  Because it doesn't seem true that Tele
  -- and Type are equivalent....  So I find this suspicious ....


