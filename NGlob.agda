{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

-- Attempts at fixing n-globularity
module NGlob where

  -- We see from this setup that there are *no* hypotheses
  -- needed to iterate, and that the setup is completely
  -- uniform.

  -- Is it true, with this definition, that we have unique
  -- composites?  No!  When you use this definition, you get
  -- stuck because after eliminating the ff term, you're left
  -- with a loop in r.

  -- Right.  This has the problem that r is on both sides of
  -- the equation.  So WTF?????

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R₀ : PolyRel P) where

    record WellFormed {i : I} {f : Op P i}
      (w : W P i) (α : Frame P w f) (r : R₀ w f α)
      (pd : W (P // R₀) (i , f)) (β : Frame (P // R₀) pd (w , α , r)) : Type ℓ where
      constructor wf
      field
        ff : (flatten R₀ pd , flatten-frm R₀ pd) == (w , α)
        bb : (transport! (λ x → R₀ (fst x) f (snd x)) ff r , bd-frame R₀ pd) == (r , β)
          [ (λ x → Σ (R₀ (fst x) f (snd x)) (λ s → Frame (P // R₀) pd (fst x , snd x , s))) ↓ ff ]

    Q : PolyRel (P // R₀)
    Q {i , f} pd (w , α , r) β =
      WellFormed w α r pd β

    postulate

      flatten-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
        → flatten R₀ (flatten Q coh) == w

      flatten-frm-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
        → flatten-frm R₀ (flatten Q coh) == α
            [ (λ w₁ → Frame P w₁ f) ↓ flatten-flatten w α r coh ]

      flatten-bd-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
        → (s : R₀ (flatten R₀ (flatten Q coh)) f (flatten-frm R₀ (flatten Q coh)))
        → (q : s == r [ (λ x → R₀ (fst x) f (snd x)) ↓  pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh) ])
        → bd-frame R₀ (flatten Q coh) == flatten-frm Q coh
            [ Frame (P // R₀) (flatten Q coh) ↓ pair= (flatten-flatten w α r coh) (↓-Σ-in (flatten-frm-flatten w α r coh) q) ]

    -- globularity : {i : I} {f : Op P i}
    --   → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
    --   → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
    --   → (s : R₀ (flatten R₀ (flatten Q coh)) f (flatten-frm R₀ (flatten Q coh)))
    --   → (q : s == r [ (λ x → R₀ (fst x) f (snd x)) ↓  pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh) ])
    --   → Path {A = Σ (Op (P // R₀) (i , f)) (Frame (P // R₀) (flatten Q coh))}
    --          ((flatten R₀ (flatten Q coh) , flatten-frm R₀ (flatten Q coh) , s) , bd-frame R₀ (flatten Q coh))
    --          ((w , α , r) , flatten-frm Q coh)
    -- globularity w α r coh s q = pair= (pair= (flatten-flatten w α r coh)
    --   (↓-Σ-in (flatten-frm-flatten w α r coh) q)) (flatten-bd-flatten w α r coh s q)

    -- This kind of thing should reall by cleaned up.
    -- Also, you could use sectioning a bit better here ..
    glob-transp : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
      → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
      → R₀ (flatten R₀ (flatten Q coh)) f (flatten-frm R₀ (flatten Q coh))
    glob-transp {f = f} w α r coh = transport! (λ x → R₀ (fst x) f (snd x))
      (pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh)) r

    -- transp-globularity : {i : I} {f : Op P i}
    --   → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
    --   → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
    --   → Path {A = Σ (Op (P // R₀) (i , f)) (Frame (P // R₀) (flatten Q coh))}
    --          ((flatten R₀ (flatten Q coh) , flatten-frm R₀ (flatten Q coh) , glob-transp w α r coh) , bd-frame R₀ (flatten Q coh))
    --          ((w , α , r) , flatten-frm Q coh)
    -- transp-globularity {f = f} w α r coh = globularity w α r coh (glob-transp w α r coh)
    --   (from-transp! (λ x → R₀ (fst x) f (snd x)) (pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh)) idp)

    -- Umm, yeah, so like, there's some kind of extra fact about the baez-dolan
    -- frame being flatten in the next dimension ... what to make of it?

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    R₀ : PolyRel P
    R₀ = FrameRel P

    R₁ : PolyRel (P // R₀)
    R₁ = Q R₀ 

    -- σ₁ : {f : Ops P} {w : Op (P // R₀) f}
    --   → (coh : W ((P // R₀) // R₁) (f , w))
    --   → R₁ (flatten R₁ coh) w (flatten-frm R₁ coh)
    -- σ₁ {i , f} {w , α , r} coh = pair= (pair= (flatten-flatten R₀ (cst (lift tt)) w α r coh)
    --   (↓-Σ-in (flatten-frm-flatten R₀ (cst (lift tt)) w α r coh) prop-has-all-paths-↓))
    --     (flatten-bd-flatten R₀ (cst (lift tt)) w α r coh (lift tt) prop-has-all-paths-↓)

    -- Right.  So this is what's strange.  Here I can finish, exactly because of
    -- contractibility.  But I can't use that assumption, since it won't repeat...

    R₂ : PolyRel ((P // R₀) // R₁)
    R₂ = Q R₁ 

    -- σ₂ : {w : Ops (P // R₀)} {pd : Op ((P // R₀) // R₁) w}
    --   → (trp : W (((P // R₀) // R₁) // R₂) (w , pd))
    --   → R₂ (flatten R₂ trp) pd (flatten-frm R₂ trp)
    -- σ₂ {(i , f) , ._ , ._ , lift tt} {pd , ._ , idp} trp = pair= (pair= (flatten-flatten R₁ σ₁ pd _ idp trp)
    --   (↓-Σ-in (flatten-frm-flatten R₁ σ₁ pd _ idp trp) (↓-=-in {!!}))) {!!}

    -- σ₂ : {w : Ops (P // R₀)} {pd : Op ((P // R₀) // R₁) w}
    --   → (trp : W (((P // R₀) // R₁) // R₂) (w , pd))
    --   → R₂ (flatten R₂ trp) pd (flatten-frm R₂ trp)
    -- σ₂ {(i , f) , (w , α , r)} {pd , β , s} trp = pair= (pair= (flatten-flatten R₁ σ₁ pd β s trp)
    --   (↓-Σ-in ((flatten-frm-flatten R₁ σ₁ pd β s trp)) (↓-=-in {!!}))) {!!}

    -- R₂ : PolyRel ((P // R₀) // R₁)
    -- R₂ {(i , f) , (w , α , r)} coh (pd , β , s) γ =
    --   Path {A = OutFrame ((P // R₀) // R₁) coh}
    --     ((flatten R₁ coh , flatten-frm R₁ coh , {!!}) , bd-frame R₁ coh)
    --     ((pd , β , s) , γ)

    -- Okay, and this is exactly the point at which the globularity
    -- principle intervenes.  So we need a reasonable statement.  I don't
    -- like the full abstract one when I am trying to write this out in
    -- the very special case of the universe.

    R₂-mult : is-multiplicative ((P // R₀) // R₁) R₂
    R₂-mult {(i , f) , (w , α , r)} coh = has-level-in (ctr , pth)

      where ctr : Composite ((P // R₀) // R₁) R₂ coh
            ctr = (flatten R₁ coh , flatten-frm R₁ coh ,
              wf (pair= (flatten-flatten R₀ w α r coh) (flatten-frm-flatten R₀ w α r coh)) (↓-Σ-in prop-has-all-paths-↓ {!!})) ,
                bd-frame R₁ coh , wf idp idp

            pth : (cmp : Composite ((P // R₀) // R₁) R₂ coh) → ctr == cmp
            pth ((._ , ._ , wf ff bb₁) , e , wf idp bb) = {!!}

    -- R₂-regular : is-regular (P // R₀) R₁ R₂
    -- R₂-regular {i , f} {w , α , r} pd β s coh γ t =
    --   globular P R₀ R₁ R₁-regular w α r coh , t

    -- R₃ : PolyRel (((P // R₀) // R₁) // R₂)
    -- R₃ {((i , f) , (w , α , r)) , (pd , β , s)} trpl (coh , γ , t) δ = 
    --   Path {A = OutFrame (((P // R₀) // R₁) // R₂) trpl}
    --     ((flatten R₂ trpl , flatten-frm R₂ trpl , {!!}) , bd-frame R₂ trpl)
    --     ((coh , γ , t) , δ)

    -- R₃-regular : is-regular ((P // R₀) // R₁) R₂ R₃
    -- R₃-regular {((i , f) , (w , α , r))} {(pd , β , s)} coh γ t trpl δ u =
    --   (pair= (pair= idp (pair= idp {!!})) {!!} ∙
    --       (snd (globular (P // R₀) R₁ R₂ R₂-regular pd β s trpl))) , u

    -- R₄ : PolyRel ((((P // R₀) // R₁) // R₂) // R₃)
    -- R₄ = {!!}

    -- So I have an idea: what if you split the globularity statement into two
    -- pieces, one which says that you get this identification and a second which
    -- says, given an appropriate path-over, you get a baez-dolan identification
    -- as well.

    -- Because you see over and over again that somehow the natural division
    -- is grouping the tree and frame together and working about the filler
    -- and baez-dolan frame after.  Maybe this would give you more flexibility.

    -- Well, well, well.  So now that looks pretty interesting.
    -- Uh, yeah.  This is starting to look completely doable.

    -- It very much looks to me like, given this one extra fact about the targets
    -- of iterated applications of globular, that the resulting sequence after
    -- n = 3 stabilizes and becomes provable by induction.

    --
    --  Generalizing over n ...
    --

    -- RSort : (n : ℕ) → Type ℓ
    -- RPoly : (n : ℕ) → Poly (RSort n)
    -- RRel : (n : ℕ) → PolyRel (RPoly n)

    -- RSort O = I
    -- RSort (S n) = Ops (RPoly n)

    -- RPoly O = P 
    -- RPoly (S n) = RPoly n // RRel n

    -- postulate

    --   1-glob : (n : ℕ) {i : RSort n} {f : Op (RPoly n) i}
    --     → (pd : W (RPoly n // RRel n) (i , f))
    --     → (w : W (RPoly n) i) (α : Frame (RPoly n) w f) (r : (RRel n) w f α)
    --     → (β : Frame (RPoly (S n)) pd (w , α , r))
    --     → Σ (RRel n (flatten (RRel n) pd) f (flatten-frm (RRel n) pd))
    --         (λ r₀ → Path {A = OutFrame (RPoly (S n)) pd}
    --                      ((flatten (RRel n) pd , flatten-frm (RRel n) pd , r₀) , bd-frame (RRel n) pd)
    --                      ((w , α , r) , β))

    -- n-glob : (n : ℕ) {i : RSort n} {f : Op (RPoly n) i}
    --   → (w : W (RPoly n) i) (α : Frame (RPoly n) w f) (r : (RRel n) w f α)
    --   → (coh : W ((RPoly n // RRel n) // RRel (S n)) ((i , f) , (w , α , r)))
    --   → RRel (S n) (flatten (RRel (S n)) coh) (w , α , r) (flatten-frm (RRel (S n)) coh)

    -- RRel O = R₀
    -- RRel (S O) {i , f} pd (w , α , r) β =
    --   Σ (R₀ (flatten R₀ pd) f (flatten-frm R₀ pd))
    --     (λ s → Path {A = OutFrame (P // R₀) pd} 
    --              ((flatten R₀ pd , flatten-frm R₀ pd , s) , bd-frame R₀ pd)
    --              ((w , α , r) , β))
    -- RRel (S (S n)) {(i , f) , (w , α , r)} coh (pd , β , s) γ =
    --   Path {A = OutFrame (RPoly (S n) // RRel (S n)) coh}
    --     ((flatten (RRel (S n)) coh , flatten-frm (RRel (S n)) coh , n-glob n w α r coh) , bd-frame (RRel (S n)) coh)
    --     ((pd , β , s) , γ)


    -- n-glob = {!!}
    
    -- -- n-glob O w α r coh = glob₁ w α r coh
    -- -- n-glob (S O) {i , f} {._ , ._ , r} pd ._ (.r , idp) coh = {!!}
    -- -- n-glob (S (S n)) {i , f} {w , α , r} pd β s coh = {!!}

    -- -- n-glob O w α r coh = glob₁ w α r coh
    -- -- n-glob (S O) {i , f} {w , α , r} pd β s coh = {!!}
    -- -- n-glob (S (S n)) {i , f} {w , α , r} pd β s coh = {!ih!}

    -- --   where ih : RRel (S (S n)) (flatten (RRel (S (S n))) (flatten (RRel (S (S (S n)))) coh)) (w , α , r)
    -- --                         (flatten-frm (RRel (S (S n))) (flatten (RRel (S (S (S n)))) coh))
    -- --         ih = n-glob (S n) w α r (flatten (RRel (S (S (S n)))) coh)


    -- -- n-glob (S n) {i , f} {w , α , r} pd β s coh = {! !}

    -- --   where ih : RRel (S n) (flatten (RRel (S n)) (flatten (RRel (S (S n))) coh)) (w , α , r)
    -- --                         (flatten-frm (RRel (S n)) (flatten (RRel (S (S n))) coh))
    -- --         ih = n-glob n w α r (flatten (RRel (S (S n))) coh)


