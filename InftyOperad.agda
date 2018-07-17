{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly
open import Frame

module InftyOperad where

  FillPoly : {I : Type₀} (P : Poly I)
    → (F : {i : I} {c : γ P i} {w : W P i} → Frame P w c → Type₀)
    → Poly (Σ I (γ P))
  γ (FillPoly P F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) (λ f → F f))
  ρ (FillPoly P F) (i , c) (w , f , x) = node P w 
  τ (FillPoly P F) (i , c) (w , f , x) n = node-type P w n

  record PolyType {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {c : γ P i} {w : W P i} → Frame P w c → Type₀
      H : PolyType (FillPoly P F)

  open PolyType public
  
  record is-algebraic {I : Type₀} {P : Poly I} (X : PolyType P) : Type₁ where
    coinductive
    field

      has-fillers : {i : I} (w : W P i)
        → is-contr (Σ (γ P i) (λ c → Σ (Frame P w c) (F X)))

      H-is-algebraic : is-algebraic (H X)

  open is-algebraic public

  module PolySig {I : Type₀} {P : Poly I} (X : PolyType P) (is-alg : is-algebraic X) where

    μ : {i : I} (w : W P i) → γ P i
    μ w = fst (contr-center (has-fillers is-alg w))

    μ-frm : {i : I} (w : W P i) → Frame P w (μ w)
    μ-frm w = fst (snd (contr-center (has-fillers is-alg w)))
    
    μ-plc-eqv : {i : I} (w : W P i) → leaf P w ≃ ρ P i (μ w)
    μ-plc-eqv w = frm-eqv (fst (snd (contr-center (has-fillers is-alg w)))) 

    μ-plc-coh : {i : I} (w : W P i) (l : leaf P w) → leaf-type P w l == τ P i (μ w) (–> (μ-plc-eqv w) l) 
    μ-plc-coh w l = frm-coh (fst (snd (contr-center (has-fillers is-alg w)))) l
    
    μ-witness : {i : I} (w : W P i) → F X (frm (μ-plc-eqv w) (μ-plc-coh w))
    μ-witness w = snd (snd (contr-center (has-fillers is-alg w))) 

    η : (i : I) → γ P i
    η i = μ (lf i)

    ηρ-contr : (i : I) → is-contr (ρ P i (η i))
    ηρ-contr i = equiv-preserves-level (μ-plc-eqv (lf i))

    ηρ-typ : (i : I) (p : ρ P i (η i))
      → τ P i (η i) p == i
    ηρ-typ i p = ap (τ P i (η i)) lem ∙ ! (μ-plc-coh (lf i) tt)

      where lem : p == (–> (μ-plc-eqv (lf i)) tt)
            lem = contr-has-all-paths ⦃ ηρ-contr i ⦄ p (–> (μ-plc-eqv (lf i)) tt)

  --   unary-op : (i : I) → Type₀
  --   unary-op i = Σ (γ P i) (λ c → is-contr (ρ P i c))

  --   u-domain : {i : I} (u : unary-op i) → I
  --   u-domain {i} (c , e) = τ P i c (contr-center e)

  --   urinv : (i : I) (u : unary-op i) → Type₀
  --   urinv i (u , is-c) = Σ (γ P (τ P i u (contr-center is-c))) (λ v → μ (nd i (u , (λ p → transport (W P) (ap (τ P i u) (contr-path is-c p)) (corolla P v)))) == η i)

  --   pre-comp-map : (i : I) (u : unary-op i)
  --     → γ P (u-domain u) → γ P i
  --   pre-comp-map i (u , is-c) c = μ (nd i (u , λ p → transport (W P) (ap (τ P i u) (contr-path is-c p)) (corolla P c)))

  --   -- So what if we say that u is invertible if this map is an equivalence?
  --   -- I guess it's at least obviously a proposition....

  --   η-op : (i : I) → unary-op i
  --   η-op i = η i , has-level-in (–> (μ-plc-eqv (lf i)) tt , <–-inv-r (μ-plc-eqv (lf i)))

  --   Arrow : I → I → Type₀
  --   Arrow i j = Σ (unary-op j) (λ u → u-domain u == i)

  --   id-arrow : (i : I) → Arrow i i
  --   id-arrow i = η-op i , ! (μ-plc-coh (lf i) tt)

  --   -- the last guy wants us to prove that the type of this guy
  --   -- is i, where that's the domain of f.
  --   Comp : (i j k : I) → Arrow i j → Arrow j k → Arrow i k
  --   Comp i j k ((f , α) , idp) ((g , β) , idp) = (μ w , is-c) , coh 

  --     where w : W P k
  --           w = nd k (g , λ p → transport (W P) ((ap (τ P k g) (contr-path β p))) (corolla P f))
            
  --           lf-eqv : (p : ρ P k g) → leaf P (corolla P f) ≃ leaf P (transport (W P) (ap (τ P k g) (contr-path β p)) (corolla P f))
  --           lf-eqv p = leaf-inv P (corolla P f) (ap (τ P k g) (contr-path β p))

  --           is-c : is-contr (ρ P k (μ w))
  --           is-c = equiv-preserves-level (μ-plc-eqv w)
  --                    ⦃ Σ-level β (λ p → equiv-preserves-level
  --                      (leaf-inv P (corolla P f) (ap (τ P k g) (contr-path β p))
  --                        ∘e (corolla-ρ-eqv P f)⁻¹ ) ⦃ α ⦄) ⦄

  --           l = –> (lf-eqv (contr-center β)) ((contr-center α) , tt)
            
  --           coh = τ P k (μ w) (contr-center is-c)
  --                   =⟨ (contr-path is-c) (–> (μ-plc-eqv w) (contr-center β , l)) |in-ctx (λ x → τ P k (μ w) x) ⟩
  --                 τ P k (μ w) (–> (μ-plc-eqv w) (contr-center β , l))
  --                   =⟨ ! (μ-plc-coh w (contr-center β , l)) ⟩
  --                 leaf-type P (transport (W P) (ap (τ P k g) (contr-path β (contr-center β))) (corolla P f)) l
  --                   =⟨ ! (leaf-inv-coh P (corolla P f) (ap (τ P k g) (contr-path β (contr-center β))) ((contr-center α) , tt)) ⟩
  --                 τ P (τ P k g (contr-center β)) f (contr-center α) ∎

  --   l-inv : {i : I} (u : unary-op i) → Type₀
  --   l-inv {i} u = Σ (Arrow i j) (λ l → fst (fst (Comp j i j (u , idp) l)) == η j)

  --     where j = u-domain u

  --   r-inv : {i : I} (u : unary-op i) → Type₀
  --   r-inv {i} u = Σ (Arrow i j) (λ r → fst (fst (Comp i j i r (u , idp))) == η i)

  --     where j = u-domain u

  --   is-invertible : ∀ {i} (u : unary-op i) → Type₀
  --   is-invertible u = l-inv u × r-inv u

  module _ {I : Type₀} {P : Poly I} (X : PolyType P) (is-alg : is-algebraic X) where

    module PS = PolySig X is-alg
    module HS = PolySig (H X) (H-is-algebraic is-alg)

    μₚ = PS.μ
    μ-frmₚ = PS.μ-frm
    μ-witₚ = PS.μ-witness

    μₕ = HS.μ
    ηₕ = HS.η
      
    -- μ : {i : I} (w : W P i) → γ P i
    -- μ w = fst (contr-center (has-fillers is-alg w))

    -- graft : (i : I) (w : W P i) (ε : (l : leaf P w) → W P (leaf-type P w l)) → W P i
    -- graft i (lf .i) ε = ε tt
    -- graft i (nd .i (c , δ)) ε = nd i (c , λ p → graft (τ P i c p) (δ p) (λ l → ε (p , l)))

    -- module _ {i : I} (c : γ P i) (f-tr : W (FillPoly P (F X)) (i , c)) where

    --   join : W P i
    --   join = fst (fst (contr-center (has-fillers (H-is-algebraic is-alg) f-tr)))

      -- So, the more general statement would be that this operation is necessarily
      -- given by the join operation as you usually understand it.

    join : {i : I} (w : W P i)
      → (κ : (n : node P w) → γ (FillPoly P (F X)) (node-type P w n))
      → W P i
    join (lf i) κ = lf i
    join (nd i (c , δ)) κ = graft P i (fst (κ (inl unit))) (dec-to P c (fst (κ true)) (fst (snd (κ (inl unit)))) (W P) δ')

      where δ' : (p : ρ P i c) → W P (τ P i c p)
            δ' p = join (δ p) (λ n → κ (inr (p , n)))

    -- Right.  So this is how one glues together a bunch of witnesses.
    -- Now, the point would be to show that the w one gets from multiplying
    -- necessarily has this form.

    subst : {i : I} (c : γ P i) (w : W (FillPoly P (F X)) (i , c)) → W P i
    subst c (lf .(_ , c)) = corolla P c
    subst c (nd .(_ , c) ((w , _ , _) , ε)) = join w (λ n → (subst (snd (node-type P w n)) (ε n)) , {!!})
    
    -- Why should this be?

    -- μ-slc : (i : I-slc) (n : γ-slc i) (κ : (p : ρ⁻-slc i n) → γ-slc (τ-slc i n (↑-slc i n p))) → γ-slc i
    -- μ-slc (i , .(η M i)) (dot .i) κ = dot i
    -- μ-slc (i , .(μ M i c δ)) (box .i c δ ε) κ = 
    --   let κ' p q = κ (inr (p , q))
    --       ε' p = let p' = ν M i c p in μ-slc (τ M i c (↑ M i c p') , δ p') (ε p') (κ' p')
    --   in graft-slc i c (κ (inl unit)) δ ε'


    module _ {i : I} (w : W P i) (ε : (l : leaf P w) → W P (leaf-type P w l)) where

      μw : W P i
      μw = nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)

      μw-dec : (n : node P μw) → W (FillPoly P (F X)) (node-type P μw n)
      μw-dec (inl unit) = nd (i , μₚ w) ((w , μ-frmₚ w , μ-witₚ w) , λ p → corolla (FillPoly P (F X)) (ηₕ (node-type P w p)))
      μw-dec (inr (p , n)) = corolla (FillPoly P (F X)) (ηₕ (node-type P (dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε p) n))

      filler-tree : W (FillPoly P (F X)) (i , μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))
      filler-tree = nd (i , μₚ μw) ((μw , μ-frmₚ μw , μ-witₚ μw) , μw-dec)

      filler-comp : Σ (W P i) (λ w₁ → Σ (Frame P w₁ (μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))) (F X))
      filler-comp = fst (contr-center (has-fillers (H-is-algebraic is-alg) filler-tree))

    -- Now, the idea is to prove a lemma which says that, in all cases, we can recover an equality
    -- between the projected tree and the grafting.

    lemma : {i : I} (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l))
      → graft P i w ε == fst (filler-comp w ε)
    lemma (lf i) ε = {!!}
    lemma (nd i (c , δ)) ε = {!!}

      where ih : (p : ρ P i c) → graft P (τ P i c p) (δ p) (λ l → ε (p , l)) == fst (filler-comp (δ p) (λ l → ε (p , l)))
            ih p = lemma (δ p) (λ l → ε (p , l))

    -- Okay, and what would be the idea from here?
    -- Oh, I guess it's a simpler lemma which should just
    -- be about multiplication. Let's try to sketch it out.

    module _ {i : I} (c : γ P i) (δ : (p : ρ P i c) → W P (τ P i c p)) where

      δ' : (p : ρ P i c) → W P (τ P i c p)
      δ' p = corolla P (μₚ (δ p))

      cw = nd i (c , δ')

      cw-dec : (n : node P cw) → W (FillPoly P (F X)) (node-type P cw n)
      cw-dec (inl unit) = corolla (FillPoly P (F X)) (ηₕ (i , c))
      cw-dec (inr (p , inl unit)) = nd (τ P i c p  , μₚ (δ p)) ((δ p , μ-frmₚ (δ p) , μ-witₚ (δ p)) , {!!})
      cw-dec (inr (p , inr (q , ())))
      
      cw-tr : W (FillPoly P (F X)) (i , μₚ (nd i (c , δ')))
      cw-tr = nd (i , μₚ (nd i (c , δ'))) ((cw , μ-frmₚ cw , μ-witₚ cw) , cw-dec)
      
      -- What do you know about this tree?
      mystery-tree : W P i
      mystery-tree = fst (μₕ cw-tr)

      -- By construction, it's nodes are equivalent to the leaves of
      -- the places of cw-tr, right?  Yes, let's try to construct that.
      my-eqv : leaf (FillPoly P (F X)) cw-tr ≃ node P mystery-tree 
      my-eqv = frm-eqv (fst (snd (contr-center (has-fillers (H-is-algebraic is-alg) cw-tr))))

      -- So, we have this identification.
      -- We need something more.

      -- Oh, oh, oh.  I'm starting to see it.  *If* you give me a node in this tree
      -- (of which, we have an explicit description) I can pick out a node in the multiplication.
      -- So the lemma has to be about this identification.

      -- Right.  I think this is exactly the idea.
      -- But this time, there's no induction to do.
      -- It has to be a kind of primitive fact.  What is it?
      lemma₀ : nd i (c , δ) == {!contr-center (has-fillers (H-is-algebraic is-alg) cw-tr)!}
      lemma₀ = {!!}

      -- filler-comp : Σ (W P i) (λ w₁ → Σ (Frame P w₁ (μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))) (F X))
      -- filler-comp = fst (contr-center (has-fillers (H-is-algebraic is-alg) filler-tree))



    μ-hm : {i : I} (w : W P i)
      → (ε : (l : leaf P w) → W P (leaf-type P w l)) 
      → μₚ (graft P i w ε) == μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε))
    μ-hm {i} w ε =  {!snd (contr-center (has-fillers (H-is-algebraic is-alg) tr))!}

      where f : Frame P w (μₚ w)
            f = μ-frmₚ w
            
            w' : W P i
            w' = nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)

            f-dec : (p : ⊤ ⊔ Σ (ρ P i (μₚ w)) (λ x → node P (dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε x)))
              → W (FillPoly P (F X)) (node-type P w' p)
            f-dec (inl unit) = nd (i , μₚ w) ((w , μ-frmₚ w , μ-witₚ w) , λ p → corolla (FillPoly P (F X)) (ηₕ (node-type P w p)))
            f-dec (inr (p , n)) = corolla (FillPoly P (F X)) (ηₕ (node-type P (dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε p) n))
            
            tr : W (FillPoly P (F X)) (i , μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))
            tr = nd (i , μₚ w') ((w' , μ-frmₚ w' , μ-witₚ w') , f-dec)

            tr-comp : Σ (W P i) (λ w₁ → Σ (Frame P w₁ (μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))) (F X))
            tr-comp = fst (contr-center (has-fillers (H-is-algebraic is-alg) tr))
            
            tr-wit : Σ (Frame (FillPoly P (F X)) tr tr-comp) (F (H X))
            tr-wit = {!!}

            -- Thing is, I think at this point I could construct the equivalence with the
            -- leaves of the guy I'm talking about.  But you also need the filler in order
            -- tho use the contractibility.

            -- So this makes me think that I really do need the *equality* between this
            -- mysterious tree I've just constructed at the grafted tree.  Right.  And the
            -- idea must be to transport the frame that I have along the conjectured equality,
            -- thus giving a new frame.

            -- Okay.  You've got your pasting diagram of witnesses.  Now you compose it.
            -- And what happens?  Well, it should have a "boundary" which is isomorphic
            -- in some sense to the graft.  So the idea is to create a frame for the graft
            -- which uses this information.  From there, you show that you have a filler
            -- using the previous guy, and voila!

            -- Right.  So what is this "tree" you are talking about.
            -- Okay, I think I see.  It's the "leaves" of tr thought, which will
            -- be nodes of these pastings.  Gotcha.

            -- So there should be a frame.  Let's try to make it.

    -- Right.  So the point is to create a H X tree.

    -- Okay.  We have a statement.  Now we have to prove it.
    -- The first thing to do is set up the composition of fillers witnessing
    -- the multiplications.  Then you have to compose them.  Then show that
    -- these fill the same frames.

    -- Hmmm.  Right, but it seems like maybe you made things more complicated that you need to.
    -- It seems like the combined statement (where you also compose the decorating trees) is a
    -- consequence of, like, the other unit law and so on.

    -- So let's start with the easy one.  It's, after all, enough to get the unit law, which
    -- is what you are really after.

    -- Yeah, and actually, you already see the generalization of this: you can define the
    -- substitution operation on trees, and more generally, apply μ to the substitution
    -- should be the same as first multiplying, and then multiplying the resulting
    -- tree.  But anyway ...


  -- module _ {I : Type₀} {P : Poly I} (O : PSet P) (is-alg : is-algebraic O) where

  --   -- The proof here is that μ is a homomorphism, automatically.
  --   -- But I wonder if it's not better to give an elementary proof here...
  --   unit-l : (i : I) (w : W P i)
  --     → μ O is-alg (nd i (η O is-alg i , λ p → transport! (W P) (ηρ-typ O is-alg i p) w)) == μ O is-alg w
  --   unit-l i w = {!!}

  --   -- Better or worse?
  --   unit-l' : (i : I) (δ : (p : ρ P i (η O is-alg i)) → W P (τ P i (η O is-alg i) p))
  --     → μ O is-alg (δ (contr-center (ηρ-contr O is-alg i))) == μ O is-alg (nd i (η O is-alg i , δ))
  --       [ γ P ↓ ηρ-typ O is-alg i (contr-center (ηρ-contr O is-alg i)) ]
  --   unit-l' i δ = {!!}

  --   -- This one is amusing, you use the unit in the next dimension!
  --   unit-r : (i : I) (c : γ P i)
  --     → μ O is-alg (corolla P c) == c
  --   unit-r i c = ap (μ O is-alg) claim₂ ∙ claim₁
  
  --     where ηic = η (Higher O) (higher-has-fillers is-alg) (i , c) 

  --           corolla' : W P i
  --           corolla' = fst ηic 

  --           corolla'-nd-contr : is-contr (node P corolla')
  --           corolla'-nd-contr = ηρ-contr (Higher O) (higher-has-fillers is-alg) (i , c)

  --           corolla'-typ-coh : node-type P corolla' (contr-center corolla'-nd-contr) == (i , c)
  --           corolla'-typ-coh = ηρ-typ (Higher O) (higher-has-fillers is-alg) (i , c) (contr-center corolla'-nd-contr)
            
  --           claim₁ : μ O is-alg corolla' == c
  --           claim₁ = fst= (contr-path (has-fillers is-alg corolla') (c , snd ηic))

  --           -- Bingo.  And now just a lemma about the corolla being unique with
  --           -- these properties and you're done!
  --           claim₂ : corolla P c == corolla'
  --           claim₂ = {!(has-fillers is-alg) corolla'!}

  
