{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Poly
open import Frame

module InftyOperad where

  _//_ : {I : Type₀} (P : Poly I)
    → (F : {i : I} {c : γ P i} {w : W P i} → Frame P w c → Type₀)
    → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) (λ f → F f))
  ρ (P // F) (i , c) (w , f , x) = node P w 
  τ (P // F) (i , c) (w , f , x) n = node-type P w n

  record PolyType {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀
      H : PolyType (P // F)

  open PolyType public

  --
  --  The Baez-Dolan substitution operation
  --

  module Substitution {I : Type₀} {P : Poly I} (X : PolyType P) where
      
    subst : {i : I} (c : γ P i)
      → (tr : W (P // (F X)) (i , c))
      → W P i

    subst-lcl : {i : I} (w : W P i)
      → (κ : (n : node P w) → W (P // (F X)) (node-type P w n))
      → W P i

    subst-lf-eqv : {i : I} (c : γ P i)
      → (tr : W (P // (F X)) (i , c))
      → leaf P (subst c tr) ≃ ρ P i c

    subst-lf-coh : {i : I} (c : γ P i)
      → (tr : W (P // (F X)) (i , c))
      → (l : leaf P (subst c tr))
      → leaf-type P (subst c tr) l == τ P i c (–> (subst-lf-eqv c tr) l)

    subst-lcl-lf-eqv : {i : I} (w : W P i)
      → (κ : (n : node P w) → W (P // (F X)) (node-type P w n))
      → leaf P (subst-lcl w κ) ≃ leaf P w

    subst-lcl-lf-coh : {i : I} (w : W P i)
      → (κ : (n : node P w) → W (P // (F X)) (node-type P w n))
      → (l : leaf P (subst-lcl w κ))
      → leaf-type P (subst-lcl w κ) l == leaf-type P w (–> (subst-lcl-lf-eqv w κ) l)

    subst c (lf .(_ , c)) = corolla P c
    subst c (nd .(_ , c) ((w , _ , _) , ε)) = subst-lcl w ε

    module SubstLcl {i : I} (c : γ P i)
      (δ : (p : ρ P i c) → W P (τ P i c p))
      (κ : (n : node P (nd i (c , δ))) → W (P // (F X)) (node-type P (nd i (c , δ)) n))
      (l : leaf P (subst c (κ true))) where

      p : ρ P i c
      p = –> (subst-lf-eqv c (κ true)) l

      w' : W P (leaf-type P (subst c (κ true)) l)
      w' = transport! (W P) (subst-lf-coh c (κ true) l) (δ p)

      κ' : (n : node P w') → W (P // (F X)) (node-type P w' n)
      κ' n = transport (W (P // (F X))) (node-inv-coh P (δ p) (subst-lf-coh c (κ true) l) n) (κ (inr (p , n'))) 

        where n' : node P (δ p)
              n' = <– (node-inv P (δ p) (subst-lf-coh c (κ true) l)) n

    subst-lcl (lf i) κ = lf i
    subst-lcl (nd i (c , δ)) κ = graft P i (subst c (κ (inl unit))) (λ l → subst-lcl (w' l) (κ' l))
      where open SubstLcl c δ κ 

    subst-lf-eqv c (lf .(_ , c)) = Σ₂-Unit
    subst-lf-eqv c (nd .(_ , c) ((w , f , x) , κ)) =
      frm-eqv f ∘e subst-lcl-lf-eqv w κ 

    subst-lf-coh c (lf .(_ , c)) (p , unit) = idp
    subst-lf-coh c (nd .(_ , c) ((w , f , x) , κ)) l =
      subst-lcl-lf-coh w κ l ∙ frm-coh f (–> (subst-lcl-lf-eqv w κ) l)

    subst-lcl-lf-eqv (lf i) κ = ide ⊤
    subst-lcl-lf-eqv (nd i (c , δ)) κ = 
      Σ-emap-l (leaf P ∘ δ) (subst-lf-eqv c (κ true)) ∘e                         -- Equivalence on base
      Σ-emap-r (λ l → (leaf-inv-! P (δ (p l)) (subst-lf-coh c (κ true) l))⁻¹ ∘e  -- Equivalence by transport ...
        subst-lcl-lf-eqv (w' l) (κ' l)) ∘e                                       -- ... and Induction Hypothesis
      (graft-lf-eqv P i (subst c (κ true)) (λ l → subst-lcl (w' l) (κ' l)))⁻¹    -- Characterization of graft leaves
      
      where open SubstLcl c δ κ

    subst-lcl-lf-coh (lf i) κ unit = idp
    subst-lcl-lf-coh (nd i (c , δ)) κ l = {!!}

  --
  --  Algebraic Polynomial Types
  --

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

  -- module _ {I : Type₀} {P : Poly I} (X : PolyType P) (is-alg : is-algebraic X) where

  --   module PS = PolySig X is-alg
  --   module HS = PolySig (H X) (H-is-algebraic is-alg)

  --   μₚ = PS.μ
  --   μ-frmₚ = PS.μ-frm
  --   μ-witₚ = PS.μ-witness

  --   μₕ = HS.μ
  --   ηₕ = HS.η

  --   μ-hm : {i : I} (w : W P i)
  --     → (ε : (l : leaf P w) → W P (leaf-type P w l)) 
  --     → μₚ (graft P i w ε) == μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε))
  --   μ-hm {i} w ε =  {!snd (contr-center (has-fillers (H-is-algebraic is-alg) tr))!}

  --     where f : Frame P w (μₚ w)
  --           f = μ-frmₚ w
            
  --           w' : W P i
  --           w' = nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)

  --           f-dec : (p : ⊤ ⊔ Σ (ρ P i (μₚ w)) (λ x → node P (dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε x)))
  --             → W (P // (F X)) (node-type P w' p)
  --           f-dec (inl unit) = nd (i , μₚ w) ((w , μ-frmₚ w , μ-witₚ w) , λ p → corolla (P // (F X)) (ηₕ (node-type P w p)))
  --           f-dec (inr (p , n)) = corolla (P // (F X)) (ηₕ (node-type P (dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε p) n))
            
  --           tr : W (P // (F X)) (i , μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))
  --           tr = nd (i , μₚ w') ((w' , μ-frmₚ w' , μ-witₚ w') , f-dec)

  --           tr-comp : Σ (W P i) (λ w₁ → Σ (Frame P w₁ (μₚ (nd i (μₚ w , dec-from P (μₚ w) w (μ-frmₚ w) (W P) ε)))) (F X))
  --           tr-comp = fst (contr-center (has-fillers (H-is-algebraic is-alg) tr))
            
  --           tr-wit : Σ (Frame (P // (F X)) tr tr-comp) (F (H X))
  --           tr-wit = {!!}

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

  
