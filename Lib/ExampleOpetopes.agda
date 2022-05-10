--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat
open import Cubical.Data.Sum

open import Core.Prelude
open import Core.Opetopes

module Lib.ExampleOpetopes where

  -- Dim 0 

  obj : 𝒪 0
  obj = ●

  -- Dim 1
  
  arrow : 𝒪 1
  arrow = ● ∣ objₒ 

  -- Dim 2
  
  n-path : ℕ → 𝒫 (● ∣ objₒ)
  n-path zero = lfₒ 
  n-path (suc n) = ndₒ objₒ (λ _ → objₒ) (λ _ → n-path n)

  n-gon : ℕ → 𝒪 2
  n-gon n = ● ∣ objₒ ∣ n-path n

  2-drop : 𝒪 2
  2-drop = n-gon 0 

  2-globe : 𝒪 2
  2-globe = n-gon 1

  2-simplex : 𝒪 2
  2-simplex = n-gon 2

  -- Dim 3

  left-unitor : 𝒫 2-globe
  left-unitor = ndₒ (n-path 2) 𝑞 𝑟   

    where 𝑞 : (p : Pos (n-path 2)) → 𝒫 (Typ (n-path 2) p)
          𝑞 (inl tt) = n-path 0
          𝑞 (inr (tt , inl tt)) = n-path 1

          𝑟 : (p : Pos (n-path 2)) → 𝒫 (Typ (n-path 2) p ∣ 𝑞 p)
          𝑟 (inl tt) = ndₒ {𝑜 = ● ∣ objₒ} lfₒ (λ { () }) (λ { () })
          𝑟 (inr (tt , inl tt)) = lfₒ

  fake-unitor : 𝒫 2-globe
  fake-unitor = ndₒ (n-path 2) 𝑞 𝑟   

    where 𝑞 : (p : Pos (n-path 2)) → 𝒫 (Typ (n-path 2) p)
          𝑞 (inl tt) = n-path 0
          𝑞 (inr (tt , inl tt)) = n-path 1

          𝑟 : (p : Pos (n-path 2)) → 𝒫 (Typ (n-path 2) p ∣ 𝑞 p)
          𝑟 (inl tt) = ndₒ {𝑜 = ● ∣ objₒ} lfₒ (λ { () }) (λ { () })
          𝑟 (inr (tt , inl tt)) = ηₒ (n-gon 1)



