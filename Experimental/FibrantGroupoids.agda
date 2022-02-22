open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Core.Everything
open import Lib.Structures
open import Lib.Universe
open import Lib.Groupoid

module Experimental.FibrantGroupoids where

  --
  --  Fibrancy of the opetopic type associated to a type
  --

  module _ {ℓ} (X : Type ℓ) where

    idp : (x : X) → GrpCell X (tt* , reflₒ x ● , tt* , (λ p → reflₒ x ●))
    idp x = reflₒ x (● ∣ objₒ) 

    -- A frame with a filler is completely determined by a point.
    fullFrmEquivX : {n : ℕ} (𝑜 : 𝒪 n) → (Σ[ f ∈ Frm (Grp X n) 𝑜 ] GrpCell X f) ≃ X
    fullFrmEquivX {n} 𝑜 = isoToEquiv (iso to from to-from from-to)

      where to : Σ[ f ∈ Frm (Grp X n) 𝑜 ] GrpCell X f → X
            to (.(Frm-El (Pt x) 𝑜) , reflₒ x .𝑜) = x

            from : X → Σ[ f ∈ Frm (Grp X n) 𝑜 ] GrpCell X f
            from x = (Frm-El (Pt x) 𝑜) , reflₒ x 𝑜

            to-from : (x : X) → to (from x) ≡ x
            to-from x = refl

            from-to : (d : Σ[ f ∈ Frm (Grp X n) 𝑜 ] GrpCell X f) → from (to d) ≡ d
            from-to (.(Frm-El (Pt x) 𝑜) , reflₒ x .𝑜) = refl

    --
    --  proving there is a unique constructor with decoration
    --  

    -- Okay.  So to get better definitional behavior, I think you
    -- should rather define the root element locally so that it
    -- computes.

    root-el : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (Σ[ f ∈ Frm (Grp X n) 𝑜 ]
         Σ[ c ∈ Cns (Grp X n) f 𝑝 ]
         ((p : Pos 𝑝) → GrpCell X (Shp (Grp X n) c p))) → X
    root-el objₒ (f , c , y) with y tt
    root-el objₒ (f , c , y) | reflₒ x .● = x
    root-el lfₒ (._ , (lf (reflₒ x 𝑜)) , _) = x
    root-el (ndₒ 𝑝 𝑞 𝑟) (._ , (nd (reflₒ x 𝑜) c y d z ψ) , _) = x

    canon-dec : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → X → (Σ[ f ∈ Frm (Grp X n) 𝑜 ]
             Σ[ c ∈ Cns (Grp X n) f 𝑝 ]
             ((p : Pos 𝑝) → GrpCell X (Shp (Grp X n) c p)))
    canon-dec {𝑜 = 𝑜} 𝑝 x = Frm-El (Pt x) 𝑜 , Cns-El (Pt x) 𝑝 , λ p → reflₒ x (Typ 𝑝 p)

    one-dir : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (x : X)
      → root-el 𝑝 (canon-dec 𝑝 x) ≡ x
    one-dir objₒ x = refl
    one-dir lfₒ x = refl
    one-dir (ndₒ 𝑝 𝑞 𝑟) x = refl

    lemma₁ : (c : GrpCell X tt*) → reflₒ (root-el objₒ (tt* , tt* , const c)) ● ≡ c
    lemma₁ (reflₒ x .●) = refl

    lemma₂ : ∀ {ℓ} {P : ⊥ → Type ℓ} (f g : (p : ⊥) → P p) → f ≡ g
    lemma₂ {P = P} f g i () 
  
    harder-dir : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜)
      → (trpl : Σ[ f ∈ Frm (Grp X n) 𝑜 ]
                Σ[ c ∈ Cns (Grp X n) f 𝑝 ]
                ((p : Pos 𝑝) → GrpCell X (Shp (Grp X n) c p)))
      → canon-dec 𝑝 (root-el 𝑝 trpl) ≡ trpl

    harder-local : {n : ℕ} {𝑜 : 𝒪 n} (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
      → (𝑟 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p ∣ 𝑞 p))
      → (f : Frm (Grp X n) 𝑜) (x : GrpCell X f)
      → (c : Cns (Grp X n) f 𝑝) 
      → (y : (p : Pos 𝑝) → GrpCell X (Shp (Grp X n) c p))
      → (d : (p : Pos 𝑝) → Cns (Grp X n) (Shp (Grp X n) c p) (𝑞 p))
      → (z : (p : Pos 𝑝) (q : Pos (𝑞 p)) → GrpCell X (Shp (Grp X n) (d p) q))
      → (ψ : (p : Pos 𝑝) → Cns (Grp X n , GrpCell X) (Shp (Grp X n) c p , y p , d p , z p) (𝑟 p))
      → (δ : (p : Unit ⊎ Σ-syntax (Pos 𝑝) (λ p₁ → Pos (𝑟 p₁))) →
               GrpCell X (Shp (Grp X n , GrpCell X) (nd x c y d z ψ) p))
      → (cell : GrpCell X (f , x , c , y))
      → (eq : δ (inl tt) ≡ cell) 
      → canon-dec (ndₒ 𝑝 𝑞 𝑟) (root-el (ndₒ 𝑝 𝑞 𝑟) ((f , x , μ (Grp X n) c d , (λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p))) , nd x c y d z ψ , δ))
           ≡ ((f , x , μ (Grp X n) c d , (λ p → z (fstₚ 𝑝 𝑞 p) (sndₚ 𝑝 𝑞 p))) , nd x c y d z ψ , δ)               

    -- implementation of harder-dir
    harder-dir objₒ (tt* , tt* , δ) = λ i → tt* , tt* , λ p → lemma₁ (δ p) i
    
    harder-dir {suc n} lfₒ (._ , lf (reflₒ x 𝑜) , δ) = λ i → 
      ((Frm-El (Pt x) 𝑜 ,
          reflₒ x 𝑜 , η (Grp X n) (Frm-El (Pt x) 𝑜) , (λ p → reflₒ x 𝑜))
         , lf (reflₒ x 𝑜) , lemma₂ (λ p → reflₒ x (Typ lfₒ p)) δ i)

    harder-dir (ndₒ 𝑝 𝑞 𝑟) (._ , nd x c y d z ψ , δ) =
      harder-local 𝑝 𝑞 𝑟 _ x c y d z ψ δ (δ (inl tt)) refl 

    -- implementation of harder-local 
    harder-local {n} {𝑜} 𝑝 𝑞 𝑟 ._ ._ ._ ._ d z ψ δ (reflₒ x ._) eq =
      λ i → (Frm-El (Pt x) 𝑜 , reflₒ x 𝑜 , μ (Grp X n) (Cns-El (Pt x) 𝑝) {!!} , {!!}) ,
            nd (reflₒ x 𝑜) (Cns-El (Pt x) 𝑝) (λ p → reflₒ x (Typ 𝑝 p)) {!!} {!!} {!!} , {!!}

    -- Need equalities: 
    -- 
    --   d ≡ (λ p → Cns-El (Pt x) (𝑞 p))
    --   z ≡ (λ p q → reflₒ x (Typ (𝑞 p) q))
    --   ψ = (λ p → Cns-El (Pt x , reflₒ x) (𝑟 p))
    --   δ ≡ (λ p → reflₒ x (Typ (ndₒ 𝑝 𝑞 𝑟) p))
    -- 

      where IH-el : (p : Pos 𝑝) → (Σ[ f ∈ Frm (Grp X (suc n)) (Typ 𝑝 p ∣ 𝑞 p) ]
                                   Σ[ c ∈ Cns (Grp X (suc n)) f (𝑟 p) ]
                                   ((q : Pos (𝑟 p)) → GrpCell X (Shp (Grp X (suc n)) c q)))
            IH-el p = ((Shp (Grp X _) (Cns-El (Pt x) 𝑝) p , reflₒ x (Typ 𝑝 p) , d p , z p) , ψ p , λ q → δ (inr (p , q))) 

            IH : (p : Pos 𝑝) → canon-dec (𝑟 p) (root-el (𝑟 p) (IH-el p)) ≡ IH-el p
            IH p = harder-dir (𝑟 p) ((Frm-El (Pt x) (Typ 𝑝 p) , reflₒ x (Typ 𝑝 p)  , d p , z p) , ψ p , λ q → δ (inr (p , q))) 

            IH-fst : (p : Pos 𝑝) → Shp (Grp X n) (Cns-El (Pt (root-el (𝑟 p) (IH-el p))) 𝑝) p
                                 ≡ Shp (Grp X n) (Cns-El (Pt x) 𝑝) p
            IH-fst p i = fst (fst (IH p i))


    other-idea : {n : ℕ} (𝑜 : 𝒪 n) (𝑝 : 𝒫 𝑜)
      → X ≃ (Σ[ f ∈ Frm (Grp X n) 𝑜 ]
             Σ[ c ∈ Cns (Grp X n) f 𝑝 ]
             ((p : Pos 𝑝) → GrpCell X (Shp (Grp X n) c p)))
    other-idea {n} 𝑜 𝑝 = isoToEquiv (iso (canon-dec 𝑝) (root-el 𝑝)
                                         (harder-dir 𝑝) (one-dir 𝑝)) 

    thm : (n : ℕ) → is-fibrant (Grp X (suc (suc n)))
    thm n {𝑜} {𝑝} {f} c y = {!!}
