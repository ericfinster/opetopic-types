
  --
  --  The identity types of source trees 
  --
  
  module _ {n ℓ}
    {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
    (U : Frm (X , P) → Type ℓ)
    where

    Cover : Σ[ f ∈ Frm (X , P) ] Pd U f → Σ[ f' ∈ Frm (X , P) ] Pd U f' → Type ℓ 
    Cover (._ , lf {frm} tgt) (._ , lf {frm'} tgt') = (frm , tgt) ≡ (frm' , tgt')
    Cover (._ , lf tgt) (._ , nd src' tgt' flr' brs') = Lift ⊥
    Cover (._ , nd src tgt flr brs) (._ , lf tgt') = Lift ⊥
    Cover (._ , nd {frm} src tgt flr brs) (._ , nd {frm'} src' tgt' flr' brs') =
      (frm , src , tgt , flr , brs) ≡ (frm' , src' , tgt' , flr' , brs')

    reflCode : (x : Σ[ f ∈ Frm (X , P) ] Pd U f) → Cover x x
    reflCode (._ , lf tgt) = refl
    reflCode (._ , nd src tgt flr brs) = refl

    encode : ∀ xs ys → (p : xs ≡ ys) → Cover xs ys
    encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

    encodeRefl : ∀ xs → encode xs xs refl ≡ reflCode xs
    encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

    decode : ∀ xs ys → Cover xs ys → xs ≡ ys
    decode (._ , lf tgt) (._ , lf tgt') c i =
      (c i .fst , η P (c i .snd) , c i .snd) , lf (c i .snd)
    decode (._ , nd src tgt flr brs) (._ , nd src' tgt' flr' brs') c i =
      (c i .fst , canopy U {c i .fst} (c i .snd .snd .snd .snd) , c i .snd .snd .fst) ,
      nd (c i .snd .fst) (c i .snd .snd .fst) (c i .snd .snd .snd .fst) (c i .snd .snd .snd .snd)

    decodeRefl : ∀ xs → decode xs xs (reflCode xs) ≡ refl
    decodeRefl (._ , lf tgt) = refl
    decodeRefl (._ , nd src tgt flr brs) = refl

    decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
    decodeEncode xs _ =
      J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
        (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)


  --
  --  An equivalence for decorations
  --

  Dec↓-Σ-equiv-to : ∀ {n ℓ} 
    → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
    → (Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ))
    → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
    → (Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ)
    → {F : Frm (𝕆U n ℓ)} (S : Src X F) (D : Dec {X = 𝕆U n ℓ} Y S)
    → {f : Frm↓ F} (s : Src↓ P S f) (d : Dec↓ Y Q S D s)
    → Src↓ (λ (x , y) f↓ → Σ[ p ∈ P x f↓ ] Q y p)
           (ν {Q = λ F → Σ[ x ∈ X F ] Y x} S (λ p → S ⊚ p , D ⊛ p)) f 
  Dec↓-Σ-equiv-to Y {P} Q {F} S D s d =
    ν↓ {Q = λ (x , y) f↓ → Σ[ p ∈ P x f↓ ] Q y p}
      {F = F} {S = S} {ϕ = λ p → S ⊚ p , D ⊛ p}
      s (λ p → s ⊚↓ p , d ⊛↓ p)

  -- Yeah, so probably this difficulty goes away if you say that
  -- this equivalence lies over one in the base.  That way you
  -- wouldn't have a weird roundtrip on the positions here I
  -- think ...
  -- Dec↓-Σ-equiv-from : ∀ {n ℓ} 
  --   → {X : (F : Frm (𝕆U n ℓ)) → Type (ℓ-suc ℓ)}
  --   → (Y : {F : Frm (𝕆U n ℓ)} → X F → Type (ℓ-suc ℓ))
  --   → {P : {F : Frm (𝕆U n ℓ)} → X F → (f : Frm↓ F) → Type ℓ}
  --   → (Q : {F : Frm (𝕆U n ℓ)} {C : X F} → Y C → {f : Frm↓ F} → P C f → Type ℓ)
  --   → {F : Frm (𝕆U n ℓ)} (S : Src X F) (D : Dec {X = 𝕆U n ℓ} Y S)
  --   → {f : Frm↓ F} (s : Src↓ (λ (x , y) f↓ → Σ[ p ∈ P x f↓ ] Q y p)
  --                       (ν {Q = λ F → Σ[ x ∈ X F ] Y x} S (λ p → S ⊚ p , D ⊛ p)) f)
  --   → Σ[ s' ∈ Src↓ P S f ] Dec↓ Y Q S D s'
  -- Dec↓-Σ-equiv-from {X = X} Y {P} Q {F} S D {f} s =
  --   blorp ,
  --   λ-dec↓ Q D {f = f} {s = blorp}
  --     (λ p → {!snd (s ⊚↓ ν-pos S (λ p → S ⊚ p , D ⊛ p) p)!})

  --   where blorp : Src↓ P S f
  --         blorp = ν↓ {Q = P} {F = F}
  --                   {S = ν {Q = λ F → Σ[ x ∈ X F ] Y x} S (λ p → S ⊚ p , D ⊛ p)}
  --                   {ϕ = λ p → S ⊚ ν-lift S (λ p → S ⊚ p , D ⊛ p) p}
  --                   s (λ p → fst (s ⊚↓ p))

