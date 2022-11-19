open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Core.Everything
open import Lib.Structures

module Experimental.ContrTrees where

 ⟦_⟧ : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ}
   → (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ)
   → {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) (𝑝 : 𝒫 𝑜)
   → Type ℓ
 ⟦ Xₛₙ ⟧ f 𝑝 = Σ[ c ∈ Cns _ f 𝑝 ] ((p : Pos 𝑝) → Xₛₙ (Shp _ c p))

 lf-eq-to : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ}
   → {Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ}
   → {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
   → (c : Cns Xₙ f (ηₒ 𝑜)) (y : (p : Pos (ηₒ 𝑜)) → Xₛₙ (Shp Xₙ c p))
   → LfCns (Xₙ , Xₛₙ) (f , x , c , y)
   → Path (⟦ Xₛₙ ⟧ f (ηₒ 𝑜)) (c , y) (η Xₙ f , const x)
 lf-eq-to ._ ._ ._ (lf x) = refl

 lf-eq-from : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ}
   → {Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ}
   → {𝑜 : 𝒪 n} {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
   → (c : Cns Xₙ f (ηₒ 𝑜)) (y : (p : Pos (ηₒ 𝑜)) → Xₛₙ (Shp Xₙ c p))
   → Path (⟦ Xₛₙ ⟧ f (ηₒ 𝑜)) (c , y) (η Xₙ f , const x)
   → LfCns (Xₙ , Xₛₙ) (f , x , c , y)
 lf-eq-from {Xₙ = Xₙ} {Xₛₙ} {f = f} x c y p =
   transp (λ i → LfCns (Xₙ , Xₛₙ) (f , x , fst (p (~ i)) , snd (p (~ i)))) i0 (lf x) 

 NdCnsData : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
   → (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ)
   → (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
   → (f : Frm Xₙ 𝑜) (x : Xₛₙ f)
   → (μc : Cns Xₙ f (μₒ 𝑝 𝑞)) (μy : (p : Pos (μₒ 𝑝 𝑞)) → Xₛₙ (Shp Xₙ μc p))
   → Type ℓ
 NdCnsData Xₙ Xₛₙ 𝑜 𝑝 𝑞 𝑟 f x μc μy = 
    Σ[ c ∈ Cns Xₙ f 𝑝 ]
    Σ[ y ∈ ((p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p)) ]
    Σ[ d ∈ ((p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑞 p)) ] 
    Σ[ z ∈ ((p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp Xₙ (d p) q)) ]
    Σ[ ψ ∈ ((p : Pos 𝑝) → Cns (Xₙ , Xₛₙ) (Shp Xₙ c p , y p , d p , z p) (𝑟 p)) ]
    Path (⟦ Xₛₙ ⟧ f (μₒ 𝑝 𝑞)) (μ Xₙ c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) (μc , μy) 

 nd-eq-to : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ}
   → {Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ}
   → (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
   → {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
   → (c : Cns Xₙ f (μₒ 𝑝 𝑞)) (y : (p : Pos (μₒ 𝑝 𝑞)) → Xₛₙ (Shp Xₙ c p))
   → NdCns (Xₙ , Xₛₙ) 𝑜 𝑝 𝑞 𝑟 (f , x , c , y)
   → NdCnsData Xₙ Xₛₙ 𝑜 𝑝 𝑞 𝑟 f x c y 
 nd-eq-to 𝑜 𝑝 𝑞 𝑟 .x ._ ._ (nd x c y d z ψ) =
   c , y , d , z , ψ , refl

 nd-eq-from : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ}
   → {Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ}
   → (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
   → (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
   → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
   → {f : Frm Xₙ 𝑜} (x : Xₛₙ f)
   → (c : Cns Xₙ f (μₒ 𝑝 𝑞)) (y : (p : Pos (μₒ 𝑝 𝑞)) → Xₛₙ (Shp Xₙ c p))
   → NdCnsData Xₙ Xₛₙ 𝑜 𝑝 𝑞 𝑟 f x c y 
   → NdCns (Xₙ , Xₛₙ) 𝑜 𝑝 𝑞 𝑟 (f , x , c , y)
 nd-eq-from {Xₙ = Xₙ} {Xₛₙ} 𝑜 𝑝 𝑞 𝑟 {f} x cc yy (c , y , d , z , ψ , p) = 
   transp (λ i → NdCns (Xₙ , Xₛₙ) 𝑜 𝑝 𝑞 𝑟 (f , x , fst (p i) , snd (p i))) i0 (nd x c y d z ψ)


 --
 --  Attempt to prove that nodes over the unit multiplication 
 --  are unique ...
 -- 
 
 nd-over-unit-unique : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
   → (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ)
   → (Xₛₛₙ : {𝑜 : 𝒪 (suc n)} (f : Frm (Xₙ , Xₛₙ) 𝑜) → Type ℓ)
   → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
   → (f : Frm Xₙ 𝑜) (x : Xₛₙ f)
   → (c : Cns Xₙ f 𝑝) (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
   → (cc : NdCns (Xₙ , Xₛₙ) 𝑜 𝑝 (λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ) (f , x , c , y))
   → cc ≡ η (Xₙ , Xₛₙ) {𝑜 = 𝑜 ∣ 𝑝} (f , x , c , y)
 nd-over-unit-unique Xₙ Xₛₙ Xₛₛₙ {𝑜} {𝑝} f ._ ._ ._ (nd x c y d z ψ) = {!!} 
   
   where by-ψ : (p : Pos 𝑝) → Path (⟦ Xₛₙ ⟧ (Shp Xₙ c p) (ηₒ (Typ 𝑝 p)))
                                  (d p , z p) (η Xₙ (Shp Xₙ c p) , const (y p))
         by-ψ p = lf-eq-to (y p) (d p) (z p) (ψ p)

         d-is-η : (p : Pos 𝑝) → d p ≡ η Xₙ (Shp Xₙ c p)
         d-is-η p = λ i → fst (by-ψ p i) 

         c-is-μ : μ Xₙ c d ≡ c 
         c-is-μ i = μ Xₙ c (λ p → d-is-η p i)

         first-case : (p : Pos 𝑝) → Shp Xₙ (d p) (ηₒ-pos (Typ 𝑝 p)) ≡ Shp Xₙ (η Xₙ (Shp Xₙ c p)) (ηₒ-pos (Typ 𝑝 p))
         first-case p i = Shp Xₙ (d-is-η p i) (ηₒ-pos (Typ 𝑝 p)) 
 
         second-case : (p : Pos 𝑝) → Shp Xₙ (η Xₙ (Shp Xₙ c p)) (ηₒ-pos (Typ 𝑝 p)) ≡ Shp Xₙ c p
         second-case p = refl 

         Shp-eq : (p : Pos 𝑝) → Shp Xₙ c p ≡ Shp Xₙ (d p) (ηₒ-pos (Typ 𝑝 p))
         Shp-eq p = sym (first-case p ∙ second-case p) 

         y-is-z : (p : Pos 𝑝) → (λ i → Xₛₙ (Shp-eq p i)) [ y p ≡ z p (ηₒ-pos (Typ 𝑝 p)) ] 
         y-is-z p = {!!} 

-- Goal: nd x c y d z ψ ≡
--       nd x (μ Xₙ c d) (λ p → z p (ηₒ-pos (Typ 𝑝 p)))
--       (λ p → η Xₙ (Shp Xₙ (μ Xₙ c d) p)) (λ p q → z p (ηₒ-pos (Typ 𝑝 p)))
--       (λ p → lf (z p (ηₒ-pos (Typ 𝑝 p))))


  -- So, I'd like to prove that if Xₛₙ is a fibrant relation, then the type of trees is
  -- additionally contractible.

  -- is-fibrant : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  -- is-fibrant {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
  --   {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
  --   {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
  --   (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
  --   → isContr (Σ[ x ∈ Xₛₙ f ] Xₛₛₙ {𝑜 ∣ 𝑝} (f , x , c , y))

 canon-tr : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
   → (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ)
   → (Xₛₛₙ : {𝑜 : 𝒪 (suc n)} (f : Frm (Xₙ , Xₛₙ) 𝑜) → Type ℓ)
   → (is-fib : is-fibrant ((Xₙ , Xₛₙ) , Xₛₛₙ))
   → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑞 : 𝒫 (𝑜 ∣ 𝑝)}
   → {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
   → (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
   → Σ[ x ∈ Xₛₙ f ]
     Σ[ c ∈ Cns (Xₙ , Xₛₙ) (f , x , c , y) 𝑞 ]
     ((p : Pos 𝑞) → Xₛₛₙ (Shp (Xₙ , Xₛₙ) c p))
 canon-tr Xₙ Xₛₙ Xₛₛₙ is-fib {𝑜 = ●} c y = {!!}
 canon-tr Xₙ Xₛₙ Xₛₛₙ is-fib {𝑜 = 𝑜 ∣ 𝑝} {𝑞 = lfₒ} {f , x , c , y} cc yy = {!!} , {!!} , λ { () }
 canon-tr Xₙ Xₛₙ Xₛₛₙ is-fib {𝑜 = 𝑜 ∣ .(ηₒ 𝑜)} {𝑞 = ndₒ lfₒ 𝑟 𝑠} (lf x) yy =
   let ctr = (fst (is-fib (lf x) (λ { () })))
       idx = fst ctr -- because this is basically the identity on x ...
   in idx , nd idx (lf x) (λ { () }) (λ { () }) {!!} (λ { () } ) , λ { (inl tt) → {!snd ctr!} }

 canon-tr Xₙ Xₛₙ Xₛₛₙ is-fib {𝑜 = 𝑜 ∣ .(μₒ 𝑝 𝑞)} {𝑞 = ndₒ (ndₒ 𝑝 𝑞 𝑟) 𝑠 𝑡} cc yy = {!!} , {!!} , {!!}

   -- Right!  So here you have broken off a branch.  You can now go by
   -- induction on all the continuing horizontal 𝑟 branches, and this
   -- is going to give you your covered trees there.  So then you have
   -- to collect all these guys up into a decoration that you can
   -- compose.

 question : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ)
   → (Xₛₙ : {𝑜 : 𝒪 n} (f : Frm Xₙ 𝑜) → Type ℓ)
   → (Xₛₛₙ : {𝑜 : 𝒪 (suc n)} (f : Frm (Xₙ , Xₛₙ) 𝑜) → Type ℓ)
   → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
   → (f : Frm Xₙ 𝑜) (x : Xₛₙ f)
   → (c : Cns Xₙ f 𝑝) (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
   → (cc : NdCns (Xₙ , Xₛₙ) 𝑜 𝑝 (λ p → ηₒ (Typ 𝑝 p)) (λ p → lfₒ) (f , x , c , y))
   → (yy : (p : Unit ⊎ Σ-syntax (Pos 𝑝) (λ p₁ → ⊥)) → Xₛₛₙ (Shp (Xₙ , Xₛₙ) cc p))
   → Xₛₛₙ {𝑜 ∣ 𝑝} (f , x , c , y)
 question Xₙ Xₛₙ Xₛₛₙ {𝑜} {𝑝} f x ._ ._ (nd .x c y d z ψ) yy = {!!}

   where ψ-says : (p : Pos 𝑝) → Path (⟦ Xₛₙ ⟧ (Shp Xₙ c p) (ηₒ (Typ 𝑝 p)))
                                  (d p , z p) (η Xₙ (Shp Xₙ c p) , const (y p))
         ψ-says p = lf-eq-to (y p) (d p) (z p) (ψ p)

         d-is-η : (p : Pos 𝑝) → d p ≡ η Xₙ (Shp Xₙ c p)
         d-is-η p = λ i → fst (ψ-says p i) 

         z-is-const : (p : Pos 𝑝) → (λ i → (q : Pos (ηₒ (Typ 𝑝 p))) → Xₛₙ (Shp Xₙ (d-is-η p i) q)) [ z p ≡ const (y p) ] 
         z-is-const p = λ i → snd (ψ-says p i) 

         mu-reduces : μ Xₙ c d ≡ c 
         mu-reduces i = μ Xₙ c (λ p → d-is-η p i) 



  -- I see. Ψ is a witness that d and z are the "expected" decorations.  That is,
  -- that d is a collection of units and that z agrees with y.  And then this gives
  -- the right answer.


  --   Σ[ c ∈ Cns Xₙ f 𝑝 ]
  --   Σ[ y ∈ ((p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p)) ]
  --   Σ[ d ∈ ((p : Pos 𝑝) → Cns Xₙ (Shp Xₙ c p) (𝑞 p)) ] 
  --   Σ[ z ∈ ((p : Pos 𝑝) (q : Pos (𝑞 p)) → Xₛₙ (Shp Xₙ (d p) q)) ]
  --   Σ[ ψ ∈ ((p : Pos 𝑝) → Cns (Xₙ , Xₛₙ) (Shp Xₙ c p , y p , d p , z p) (𝑟 p)) ]
  --   Ident (DecCns Xₙ Xₛₙ {𝑜} {μₒ 𝑝 𝑞} f) (μ Xₙ c d , λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p)) (μc , μy) 

   -- claim : {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {𝑞 : 𝒫 (𝑜 ∣ 𝑝)}
   --   {f : Frm Xₙ 𝑜} (c : Cns Xₙ f 𝑝)
   --   (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
   --   → isContr (Σ[ x ∈ Xₛₙ f ]
   --              Σ[ c ∈ Cns (Xₙ , Xₛₙ) (f , x , c , y) 𝑞 ]
   --              ((p : Pos 𝑞) → Xₛₛₙ (Shp (Xₙ , Xₛₙ) c p)))
   -- claim {𝑞 = lfₒ} c y = {!!}
   -- claim {𝑞 = ndₒ 𝑝 𝑞 𝑟} c y = {!!}


    

