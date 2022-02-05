--
--  OpetopicType.agda - Definition of Opetopic Types in Context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicType
open import OpetopicFam 
open import OpetopicSub
open import OpetopicTerm
open import OpetopicExt

module Universe where

  -- Here's the version with the universe as a context.  
  𝒰ₒ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒱ₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ

  𝒰ₒ zero ℓ = lift tt
  𝒰ₒ (suc n) ℓ = 𝒰ₒ n ℓ , λ f → Frm↓ (𝒱ₒ n) f → Type ℓ
  
  𝒱ₒ zero = lift tt
  𝒱ₒ (suc n) = 𝒱ₒ n , λ f↓ X → X f↓

  -- The dependent type of fibrancy
  ℱₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ
  ℱₒ zero = lift tt
  ℱₒ (suc zero) = lift tt , λ f↓ x → Lift Unit
  ℱₒ (suc (suc n)) {ℓ} = ℱₒ (suc n) , is-fibrant

    where is-fibrant : {𝑜 : Σ (𝒪 n) 𝒫} {f : Frm (𝒰ₒ (suc n) ℓ) 𝑜 }
                       → (f↓ : Frm↓ (ℱₒ (suc n)) f)
                       → (X : Frm↓ (𝒱ₒ (suc n)) f → Type ℓ)
                       → Type ℓ
                      
          is-fibrant {𝑜 , 𝑝} {f , Xₙ , c , Yₙ} _ Xₛₙ =
              (f↓ : Frm↓ (𝒱ₒ n) f) (c↓ : Cns↓ (𝒱ₒ n) f↓ c)
              (y↓ : (p : Pos 𝑝) → Yₙ p (Shp↓ (𝒱ₒ n) c↓ p))
            → isContr (Σ[ x↓ ∈ Xₙ f↓ ] Xₛₙ (f↓ , x↓ , c↓ , y↓)) 

  -- We can now define the (∞,1)-category of spaces:
  𝒮ₙ : (n : ℕ) (ℓ : Level) → 𝕆Type n (ℓ-suc ℓ)
  𝒮ₙ n ℓ = Ext (𝒰ₒ n ℓ) (ℱₒ n) 

  is-fibrant-ctx : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  is-fibrant-ctx {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    (f : Frm Xₙ 𝑜) (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → isContr (Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y))

  thm : (n : ℕ) (ℓ : Level) → is-fibrant-ctx (𝒮ₙ (suc (suc (suc n))) ℓ)
  thm zero ℓ (lift tt , (X₀ , lift tt) , lift tt , Y₀) c Y = ({!!} , {!!}) , {!!}

    where TgtType : Type ℓ
          TgtType = X₀ (lift tt)

          SrcType : Type ℓ
          SrcType = fst (Y₀ tt) (lift tt) 

  thm (suc n) ℓ (f₀ , x₀ , c₀ , y₀) c y = {!!}

  -- And so now the hard work.  You'll need to slice one extra time
  -- and then show:
  --
  --  1. The relational composite defined below is fibrant when
  --     all of the individual components are.
  --
  --  2. The filling relation (i.e. the identity) is itself fibrant.
  --     This one should be trivial.
  --
  --  3. That the previous pair is unique.  How does this part work
  --     again? Let me sketch below
  --

  --  For 3: you now have an arbitrary fibrant relation related, by a
  --         fibrant relation to the input decorations.  Now, it is
  --         enough to prove an equivalence betwen the underlying
  --         relations, since being fibrant is a property.
  --
  --         Let's say I have an element of this relation.  Then I
  --         can alternatively compose down the input tree, compose
  --         using the fibrancy of the filler and see that I now
  --         have (up to a path) a filler and a pasting diagram.
  --
  --         Oh, didn't you have this clever argument to say that,
  --         in this situation, the type of trees together with a
  --         filler should be contractible as well?
  --
  --         Fuck.  Is there still a problem with the units? Hmm.
  --         Don't think so.  But it's hard to see...
  --
  --         Okay, right.  I think this will go through.  Just going
  --         to be long....

  -- Nice!  So That worked out like I expected.  Now, what's the real
  -- claim?  It's that the universe of multiplicative relations is
  -- *itself* multiplicative.  And similarly for uniqueness, etc.

  -- Umm.  But does this actually use the multiplication.  Isn't it
  -- just simply *true* after a couple slices that the universe is
  -- multiplicative? 

  is-mult-ctx : ∀ {n ℓ} (X : 𝕆Type (suc (suc n)) ℓ) → Type ℓ
  is-mult-ctx {n} ((Xₙ , Xₛₙ) , Xₛₛₙ) =
    {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    (f : Frm Xₙ 𝑜) (c : Cns Xₙ f 𝑝)
    (y : (p : Pos 𝑝) → Xₛₙ (Shp Xₙ c p))
    → Σ[ x ∈ Xₛₙ f ] Xₛₛₙ (f , x , c , y)

  -- Crazy!  So the second slice is already multiplicative, using the
  -- canonical relation and the identity.
  univ-dbl-slc-mult : ∀ {n ℓ} → is-mult-ctx (𝒰ₒ (suc (suc n)) ℓ)
  univ-dbl-slc-mult {n} {𝑜 = 𝑜} {𝑝} f c Y =
    (λ f↓ → Σ[ c↓ ∈ Cns↓ (𝒱ₒ n) f↓ c ] ((p : Pos 𝑝) → Y p (Shp↓ (𝒱ₒ n) c↓ p))) ,
    (λ φ → fst (snd φ) ≡ (fst (snd (snd φ)) , snd (snd (snd φ))))

  -- The only thing to show is that this is somehow unique as soon
  -- as the lower levels are fibrant.

  -- One thing to note should be that this relation is already somehow
  -- *universal* in the sense of Baez-Dolan: it should factor every
  -- other relation in a kind of canonical way ....
    
  -- The dependent type of multiplicative structures
  ℳₒ : (n : ℕ) {ℓ : Level} → 𝕆Fam (𝒰ₒ n ℓ) ℓ
  ℳₒ zero = lift tt
  ℳₒ (suc zero) = lift tt , λ f↓ x → Lift Unit
  ℳₒ (suc (suc n)) = ℳₒ (suc n) ,
    λ { {𝑜 , 𝑝} {f , Xₙ , c , Yₙ} _ Xₛₙ →
       (f↓ : Frm↓ (𝒱ₒ n) f) (c↓ : Cns↓ (𝒱ₒ n) f↓ c)
       (y↓ : (p : Pos 𝑝) → Yₙ p (Shp↓ (𝒱ₒ n) c↓ p))
       → Σ[ x↓ ∈ Xₙ f↓ ] Xₛₙ (f↓ , x↓ , c↓ , y↓) } 

