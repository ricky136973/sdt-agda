{-# OPTIONS --cubical --guardedness #-}

module Lattice where

open import SemiLattice public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Cubical.HITs.Join

infix 30 _⊎_
infix 30 _⊔_

_⊎_ = join

rec⊎ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  (f : A → C) (g : B → C) (p : ∀ x y → f x ≡ g y) → A ⊎ B → C
rec⊎ f _ _ (inl x) = f x
rec⊎ _ g _ (inr y) = g y
rec⊎ _ _ p (push a b i) = p a b i

postulate _⊔_ : S → S → S
postulate ⊔-def : ∀ {x y} → ⟦ x ⊔ y ⟧ ≡ ⟦ x ⟧ ⊎ ⟦ y ⟧

opaque
  ⊔-intro : ∀ {x y z} → x ≼ z → y ≼ z → x ⊔ y ≼ z
  ⊔-intro x≼z y≼z φ = rec⊎ x≼z y≼z (λ _ _ → defIsProp _ _) (transport ⊔-def φ)

  x≼x⊔y : ∀ {x y} → x ≼ x ⊔ y
  x≼x⊔y φ = transport (sym ⊔-def) (inl φ)

  y≼x⊔y : ∀ {x y} → y ≼ x ⊔ y
  y≼x⊔y φ = transport (sym ⊔-def) (inr φ)

  x⊔y=x : ∀ {x y} → y ≼ x → x ⊔ y ≡ x
  x⊔y=x y≼x = ≼-antisym (λ φ → rec⊎ (λ φ → φ) y≼x (λ _ _ → defIsProp _ _) (transport ⊔-def φ)) x≼x⊔y

  x⊔y=y : ∀ {x y} → x ≼ y → x ⊔ y ≡ y
  x⊔y=y x≼y = ≼-antisym (λ φ → rec⊎ x≼y (λ φ → φ) (λ _ _ → defIsProp _ _) (transport ⊔-def φ)) y≼x⊔y

  0⊔x=x : ∀ {x} → s0 ⊔ x ≡ x
  0⊔x=x = x⊔y=y s0-min

  x⊔0=x : ∀ {x} → x ⊔ s0 ≡ x
  x⊔0=x = x⊔y=x s0-min

  1⊔x=1 : ∀ {x} → s1 ⊔ x ≡ s1
  1⊔x=1 = x⊔y=x s1-max

  x⊔1=1 : ∀ {x} → x ⊔ s1 ≡ s1
  x⊔1=1 = x⊔y=y s1-max

  ⊔-idem : ∀ {x} → x ⊔ x ≡ x
  ⊔-idem = x⊔y=x ≼-refl

  ⊔-comm : ∀ {x y} → x ⊔ y ≡ y ⊔ x
  ⊔-comm =
    defIsMono (⊔-def ∙ isoToPath join-comm ∙ sym ⊔-def)

  ⊔-assoc : ∀ {x y z} → x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
  ⊔-assoc =
    defIsMono (⊔-def ∙ (cong (_⊎_ _) ⊔-def) ∙ sym (⊔-def ∙ cong (λ P → P ⊎ _) ⊔-def ∙ join-assoc _ _ _))

  ⊔-monotoneL : ∀ {x y z} → x ≼ y → x ⊔ z ≼ y ⊔ z
  ⊔-monotoneL x≼y φ =
    rec⊎
      (λ φ → transport (sym ⊔-def) (inl (x≼y φ)))
      (λ φ → transport (sym ⊔-def) (inr φ))
      (λ _ _ → defIsProp _ _)
      (transport ⊔-def φ)
  
  ⊔-monotoneR : ∀ {x y z} → y ≼ z → x ⊔ y ≼ x ⊔ z
  ⊔-monotoneR y≼z φ =
    rec⊎
      (λ φ → transport (sym ⊔-def) (inl φ))
      (λ φ → transport (sym ⊔-def) (inr (y≼z φ)))
      (λ _ _ → defIsProp _ _)
      (transport ⊔-def φ)
  
  ⊔-monotone : ∀ {w x y z} → w ≼ y → x ≼ z → w ⊔ x ≼ y ⊔ z
  ⊔-monotone w≼y x≼z φ = ⊔-monotoneL w≼y (⊔-monotoneR x≼z φ)

  ⊔-congL : ∀ {x y z} → x ≡ y → x ⊔ z ≡ y ⊔ z
  ⊔-congL p = ≼-antisym (⊔-monotoneL (≼-reflP p)) (⊔-monotoneL (≼-reflP (sym p)))

  ⊔-congR : ∀ {x y z} → y ≡ z → x ⊔ y ≡ x ⊔ z
  ⊔-congR p = ≼-antisym (⊔-monotoneR (≼-reflP p)) (⊔-monotoneR (≼-reflP (sym p)))

  ⊔-cong : ∀ {w x y z} → w ≡ x → y ≡ z → w ⊔ y ≡ x ⊔ z
  ⊔-cong p q = ⊔-congL p ∙ ⊔-congR q

interpolate : S → S → S → S
interpolate s t x = s ⊔ x ⊓ t

opaque
  interpolate-0 : ∀ s t → interpolate s t s0 ≡ s
  interpolate-0 _ _ = x⊔y=x (≼-trans x⊓y≼x s0-min)

  interpolate-1 : ∀ {s t} → s ≼ t → interpolate s t s1 ≡ t
  interpolate-1 s≼t = x⊔y=y (⊓-intro s1-max s≼t) ∙ 1⊓x=x

postulate SLinear : {f : S → S} → f ≡ interpolate (f s0) (f s1)

SMonotone : ∀ {x y} (f : S → S) → x ≼ y → f x ≼ f y
SMonotone {x} {y} f x≼y =
  transport (sym (cong (λ f → f x ≼ f y) SLinear)) (⊔-monotoneR (⊓-monotoneL x≼y))

f0≼f1 : (f : S → S) → f s0 ≼ f s1
f0≼f1 f = SMonotone f s1-max

SFunExt : ∀ {f g : S → S} → f s0 ≡ g s0 → f s1 ≡ g s1 → f ≡ g
SFunExt {f} {g} p q =
  transport (sym (cong₂ _≡_ SLinear SLinear)) (funExt λ s → cong₂ (λ x y → interpolate x y s) p q)

Phoa : Iso (S → S) (□↓ 2)
Phoa .Iso.fun f = (f s1 , f s0 , tt*) , SMonotone f s1-max , tt*
Phoa .Iso.inv ((t , s , _) , _) = interpolate s t
Phoa .Iso.rightInv ((t , s , _) , P , _) =
  □↓≡ ((≡-×
    ((x⊔y=y (≼-trans P (≼-reflP (sym 1⊓x=x)))) ∙ 1⊓x=x)
    (≡-× (x⊔y=x (≼-trans x⊓y≼x s0-min)) refl)))
Phoa .Iso.leftInv f =
  SFunExt
    (x⊔y=x (≼-trans (≼-reflP 0⊓x=0) s0-min))
    ((x⊔y=y (≼-trans (SMonotone f s1-max) (≼-reflP (sym 1⊓x=x)))) ∙ 1⊓x=x)

-------------------------------------------------------------

infix 20 _□≼□_
infix 20 _□≽□_

_□≼□_ : ∀ {n} → □ n → □ n → Type ℓ₀
_□≼□_ {zero} _ _ = Unit*
_□≼□_ {suc _} (s , x) (t , y) = s ≼ t × x □≼□ y

_□≽□_ : ∀ {n} → □ n → □ n → Type ℓ₀
x □≽□ y = y □≼□ x

opaque
  □≼□-isProp : ∀ {n} {x y : □ n} → isProp (x □≼□ y)
  □≼□-isProp {zero} = isPropUnit*
  □≼□-isProp {suc _} = isProp× ≼-isProp □≼□-isProp

  □≼□-refl : ∀ {n} {x : □ n} → x □≼□ x
  □≼□-refl {zero} = tt*
  □≼□-refl {suc _} = ≼-refl , □≼□-refl

  □≼□-reflP : ∀ {n} {x y : □ n} → x ≡ y → x □≼□ y
  □≼□-reflP {zero} _ = tt*
  □≼□-reflP {suc _} p = ≼-reflP (cong fst p) , □≼□-reflP (cong snd p)

  □≼□-trans : ∀ {n} {x y z : □ n} → x □≼□ y → y □≼□ z → x □≼□ z
  □≼□-trans {zero} _ _ = tt*
  □≼□-trans {suc _} (P , Q) (R , S) = ≼-trans P R , □≼□-trans Q S

  □≼□-antisym : ∀ {n} {x y : □ n} → x □≼□ y → y □≼□ x → x ≡ y
  □≼□-antisym {zero} _ _ = refl
  □≼□-antisym {suc _} (P , Q) (R , S) = ≡-× (≼-antisym P R) (□≼□-antisym Q S)

module _ where
  open Vector

  □-map : ∀ {n} → (S → S) → □ n → □ n
  □-map f = map f

  □-map-comp : ∀ {n f g} {x : □ n} → □-map f (□-map g x) ≡ □-map (λ x → f (g x)) x
  □-map-comp = map-comp

□↑-map : ∀ {n} → (S → S) → □↑ n → □↑ n
□↑-map f (x , _) .fst = □-map f x
□↑-map {0} _ _ .snd = tt*
□↑-map {1} _ _ .snd = tt*
□↑-map {suc (suc _)} f ((s , t , x) , P , Q) .snd = SMonotone f P , □↑-map f ((t , x) , Q) .snd

□↓-map : ∀ {n} → (S → S) → □↓ n → □↓ n
□↓-map f (x , _) .fst = □-map f x
□↓-map {0} _ _ .snd = tt*
□↓-map {1} _ _ .snd = tt*
□↓-map {suc (suc _)} f ((s , t , x) , P , Q) .snd = SMonotone f P , □↓-map f ((t , x) , Q) .snd

SMonotoneN : ∀ {n} {x y : □ n} (f : □ n → S) → x □≼□ y → f x ≼ f y
SMonotoneN {zero} _ _ = ≼-refl
SMonotoneN {suc n} {s , x} {t , y} f (P , Q) =
  ≼-trans (SMonotone (λ s → f (s , x)) P) (SMonotoneN (λ x → f (t , x)) Q)

fold⊔ : ∀ {n} → □ n → □ n
fold⊔ {zero} _ = tt*
fold⊔ {suc _} (s , x) = s , □-map (_⊔_ s) (fold⊔ x)

fold⊔≡id : ∀ {n} {x : □↑ n} → fold⊔ (fst x) ≡ fst x
fold⊔≡id {0} = refl
fold⊔≡id {1} = refl
fold⊔≡id {suc (suc _)} {(_ , _ , x) , s≼t , P} =
  ≡-× refl (≡-× (x⊔y=y s≼t) (
    □-map-comp ∙
    cong (λ f → □-map f (fold⊔ x)) (funExt λ x → ⊔-assoc ∙ cong (λ y → y ⊔ x) (x⊔y=y s≼t)) ∙
    cong snd (fold⊔≡id {x = _ , P})))

fold⊔-increasing : ∀ {n} {x : □ n} → increasing (fold⊔ x)
fold⊔-increasing {0} = tt*
fold⊔-increasing {1} = tt*
fold⊔-increasing {suc (suc _)} {_ , _ , x} =
  x≼x⊔y ,
  transport
    (sym (cong increasing (≡-× refl (□-map-comp ∙ cong (λ f → □-map f (fold⊔ x)) (funExt λ _ → ⊔-assoc)))))
    fold⊔-increasing

fold⊔↑ : ∀ {n} → □ n → □↑ n
fold⊔↑ x = fold⊔ x , fold⊔-increasing

fold⊔↑≡id : ∀ {n} {x : □↑ n} → fold⊔↑ (fst x) ≡ x
fold⊔↑≡id {x = x} = □↑≡ (fold⊔≡id {x = x})

fold⊓ : ∀ {n} → □ n → □ n
fold⊓ {zero} _ = tt*
fold⊓ {suc _} (s , x) = s , □-map (_⊓_ s) (fold⊓ x)

fold⊓≡id : ∀ {n} {x : □↓ n} → fold⊓ (fst x) ≡ fst x
fold⊓≡id {0} = refl
fold⊓≡id {1} = refl
fold⊓≡id {suc (suc _)} {(_ , _ , x) , s≽t , P} =
  ≡-× refl (≡-× (x⊓y=y s≽t) (
    □-map-comp ∙
    cong (λ f → □-map f (fold⊓ x)) (funExt λ x → ⊓-assoc ∙ cong (λ y → y ⊓ x) (x⊓y=y s≽t)) ∙
    cong snd (fold⊓≡id {x = _ , P})))

fold⊓-decreasing : ∀ {n} {x : □ n} → decreasing (fold⊓ x)
fold⊓-decreasing {0} = tt*
fold⊓-decreasing {1} = tt*
fold⊓-decreasing {suc (suc _)} {_ , _ , x} =
  x⊓y≼x ,
  transport
    (sym (cong decreasing (≡-× refl (□-map-comp ∙ cong (λ f → □-map f (fold⊓ x)) (funExt λ _ → ⊓-assoc)))))
    fold⊓-decreasing

fold⊓↓ : ∀ {n} → □ n → □↓ n
fold⊓↓ x = fold⊓ x , fold⊓-decreasing

fold⊓↓≡id : ∀ {n} {x : □↓ n} → fold⊓↓ (fst x) ≡ x
fold⊓↓≡id {x = x} = □↓≡ (fold⊓≡id {x = x})

extend↑ : ∀ {n} (f : □↑ n → S) → Σ[ f̃ ∈ (□ n → S) ] ∀ {x} → f̃ (fst x) ≡ f x
extend↑ f = (λ x → f (fold⊔↑ x)) , cong f fold⊔↑≡id

extend↓ : ∀ {n} (f : □↓ n → S) → Σ[ f̃ ∈ (□ n → S) ] ∀ {x} → f̃ (fst x) ≡ f x
extend↓ f = (λ x → f (fold⊓↓ x)) , cong f fold⊓↓≡id

SMonotoneN↑ : ∀ {n x y} (f : □↑ n → S) → fst x □≼□ fst y → f x ≼ f y
SMonotoneN↑ f x≼y =
  let f̃ , P = extend↑ f in
  ≼-trans (≼-reflP (sym P)) (≼-trans (SMonotoneN f̃ x≼y) (≼-reflP P))

SMonotoneN↓ : ∀ {n x y} (f : □↓ n → S) → fst x □≼□ fst y → f x ≼ f y
SMonotoneN↓ f x≼y =
  let f̃ , P = extend↓ f in
  ≼-trans (≼-reflP (sym P)) (≼-trans (SMonotoneN f̃ x≼y) (≼-reflP P))

-------------------------------------------------------------

module _ where
  open Vector

  vertices : ∀ n → Vector (□↓ n) (suc n)
  vertices zero = (tt* , tt*) , tt*
  vertices (suc _) = δ↓ s0 , map □↓-s1 (vertices _)

  vertices-increasing : ∀ {n} → IsMonotonic (λ x y → fst x □≼□ fst y) (vertices n)
  vertices-increasing {zero} = tt*
  vertices-increasing {suc n} .fst = δ0-min
    where
      δ0-min : ∀ {n} {x : □ n} → δ s0 □≼□ x
      δ0-min {zero} = tt*
      δ0-min {suc _} = s0-min , δ0-min
  vertices-increasing {suc n} .snd =
    map-monotone □↓-s1 (λ _ _ P → ≼-refl , P) vertices-increasing

  boundary : ∀ {n} → (□↓ n → S) → □ (suc n)
  boundary f = map f (vertices _)

  boundary-increasing : ∀ {n} {f : □↓ n → S} → increasing (boundary f)
  boundary-increasing {f = f} = map-monotone _ (λ x y → SMonotoneN↓ f) vertices-increasing

boundary↑ : ∀ {n} → (□↓ n → S) → □↑ (suc n)
boundary↑ f = boundary f , boundary-increasing

-------------------------------------------------------------

zip : ∀ {n} → □ n → □ n → S
zip {zero} _ _ = s0
zip {suc _} (s , x) (t , y) = s ⊓ t ⊔ zip x y

zip-δ0 : ∀ {n} {x : □ n} → zip x (δ s0) ≡ s0
zip-δ0 {zero} = refl
zip-δ0 {suc _} = x⊔y=y (≼-trans x⊓y≼y s0-min) ∙ zip-δ0

zip-monotoneL : ∀ {n} {x y z : □ n} → x □≼□ y → zip x z ≼ zip y z
zip-monotoneL {zero} _ = ≼-refl
zip-monotoneL {suc _} (P , Q) = ⊔-monotone (⊓-monotoneL P) (zip-monotoneL Q)

zip-monotoneR : ∀ {n} {x y z : □ n} → y □≼□ z → zip x y ≼ zip x z
zip-monotoneR {zero} _ = ≼-refl
zip-monotoneR {suc _} (P , Q) = ⊔-monotone (⊓-monotoneR P) (zip-monotoneR Q)

interpolateN : ∀ {n} → □ (suc n) → □ n → S
interpolateN (s , x) y = s ⊔ zip x y

interpolate↑ : ∀ {n} → □↑ (suc n) → □↓ n → S
interpolate↑ (x , _) (y , _) = interpolateN x y

-------------------------------------------------------------

module _ where
  open Vector

  boundary-inv : ∀ {n} (x : □↑ (suc n)) → boundary (interpolate↑ x) ≡ fst x
  boundary-inv {zero} _ = ≡-× x⊔0=x refl
  boundary-inv {suc n} ((s , t , x) , s≼t , P) = ≡-×
    (x⊔y=x (≼-trans (≼-reflP zip-δ0) s0-min))
    (
      ≡-×
        (⊔-assoc ∙ ⊔-congL (cong (_⊔_ s) x⊓1=x ∙ x⊔y=y s≼t))
        (map-comp ∙ cong
          (λ f → map f (vertices n .snd))
          (funExt λ x → ⊔-assoc ∙ ⊔-congL ((cong (_⊔_ s) x⊓1=x) ∙ x⊔y=y s≼t))) ∙
      boundary-inv ((t , x) , P)
    )

  interpolate↑-funExt : ∀ {n} (f : □↓ n → S) (x : □↓ n) → interpolate↑ (boundary↑ f) x ≡ f x
  interpolate↑-funExt {0} _ _ = x⊔0=x ∙ refl
  interpolate↑-funExt {1} f ((s , _) , _) =
    ⊔-congR (x⊔0=x ∙ ⊓-comm) ∙
    λ i → SLinear {λ s → f ((s , tt*) , tt*)} (~ i) s
  interpolate↑-funExt {suc (suc n)} f ((s , t , x) , s≽t , P) =
    ⊔-assoc ∙
    ⊔-cong
      (
        ⊔-cong
          (cong f (□↓≡ (≡-× (sym x⊔0=x) refl)))
          (⊓-comm ∙ ⊓-congR (cong f (□↓≡ (≡-× (sym x⊔0=x) refl)))) ∙
        λ i → SLinear {λ s → f ((s ⊔ s0 , s0 , δ s0) , y≼x⊔y , δ↓ s0 .snd)} (~ i) s
      )
      (⊔-cong
        (⊓-congL (cong f (□↓≡ (≡-× (sym x⊔1=1) refl))))
        (cong (λ y → zip y x) (
          map-comp ∙ map-comp ∙
          cong (λ f → map f (vertices n .snd)) (funExt λ _ → cong f (□↓≡ (≡-× (sym x⊔1=1) refl))) ∙
          sym map-comp))
      ) ∙
    interpolate↑-funExt {suc n} (λ ((t , x) , P) → f ((s ⊔ t , t , x) , y≼x⊔y , P)) ((t , x) , P) ∙
    cong f (□↓≡ (≡-× (x⊔y=x s≽t) refl))

boundary↑-inv : ∀ {n} (x : □↑ (suc n)) → boundary↑ (interpolate↑ x) ≡ x
boundary↑-inv x = □↑≡ (boundary-inv x)

interpolate↑-inv : ∀ {n} (f : □↓ n → S) → interpolate↑ (boundary↑ f) ≡ f
interpolate↑-inv f = funExt (interpolate↑-funExt f)

PhoaN : ∀ {n} → Iso (□↓ n → S) (□↑ (suc n))
PhoaN = iso boundary↑ interpolate↑ boundary↑-inv interpolate↑-inv

-------------------------------------------------------------

private
  data ⊥∙ (A∙ : Pointed ℓ₀) : Type ℓ₀ where
    base : ⊥∙ A∙
    incl : typ A∙ → ⊥∙ A∙
    path : S → ⊥∙ A∙
    path-0 : path s0 ≡ base
    path-1 : path s1 ≡ incl (pt A∙)

  record ElimData {ℓ A∙} (P : ⊥∙ A∙ → Type ℓ) : Type (ℓ-max ℓ ℓ₀) where
    constructor elimdata
    field
      baseP : P base
      inclP : ∀ x → P (incl x)
      pathP : ∀ s → P (path s)
      path-0P : PathP (λ i → P (path-0 i)) (pathP s0) baseP
      path-1P : PathP (λ i → P (path-1 i)) (pathP s1) (inclP (pt A∙))
  
  elim⊥∙ : ∀ {ℓ A∙} (P : ⊥∙ A∙ → Type ℓ) → ElimData P → (x : ⊥∙ A∙) → P x
  elim⊥∙ _ (elimdata baseP _ _ _ _) base = baseP
  elim⊥∙ _ (elimdata _ inclP _ _ _) (incl x) = inclP x
  elim⊥∙ _ (elimdata _ _ pathP _ _) (path s) = pathP s
  elim⊥∙ _ (elimdata _ _ _ path-0P _) (path-0 i) = path-0P i
  elim⊥∙ _ (elimdata _ _ _ _ path-1P) (path-1 i) = path-1P i

Λ∙ : ℕ → Pointed ℓ₀
Λ∙ zero = Unit* , tt*
Λ∙ (suc n) = ⊥∙ (Λ∙ n) , base

Λ : ℕ → Type ℓ₀
Λ n = typ (Λ∙ n)

boundaryΛ : ∀ {n} → (Λ n → S) → □ (suc n)
boundaryΛ {zero} f = f tt* , tt*
boundaryΛ {suc n} f = f base , boundaryΛ λ x → f (incl x)

boundaryΛ-increasing : ∀ {n} {f : Λ n → S} → increasing {suc n} (boundaryΛ f)
boundaryΛ-increasing {0} = tt*
boundaryΛ-increasing {1} {f} .fst =
  transport
    (cong₂ _≼_ (cong f path-0) (cong f path-1))
    (f0≼f1 (λ s → f (path s)))
boundaryΛ-increasing {suc (suc _)} {f} .fst =
  transport
    (cong₂ _≼_ (cong f path-0) (cong f path-1))
    (f0≼f1 (λ s → f (path s)))
boundaryΛ-increasing {suc _} .snd = boundaryΛ-increasing

boundaryΛ↑ : ∀ {n} → (Λ n → S) → □↑ (suc n)
boundaryΛ↑ f = boundaryΛ f , boundaryΛ-increasing

interpolateΛ↑ : ∀ {n} → □↑ (suc n) → Λ n → S
interpolateΛ↑ {0} ((s , _) , _) _ = s
interpolateΛ↑ {suc _} ((s , _ , _) , _ , _) base = s
interpolateΛ↑ {suc _} (_ , _ , P) (incl y) = interpolateΛ↑ (_ , P) y
interpolateΛ↑ {1} ((s , t , _) , _) (path u) = interpolate s t u
interpolateΛ↑ {suc (suc _)} ((s , _) , _ , P) (path u) = interpolate s (interpolateΛ↑ (_ , P) base) u
interpolateΛ↑ {1} ((s , t , _) , _) (path-0 i) = interpolate-0 s t i
interpolateΛ↑ {suc (suc _)} ((s , t , _) , _) (path-0 i) = interpolate-0 s t i
interpolateΛ↑ {1} (_ , s≼t , _) (path-1 i) = interpolate-1 s≼t i
interpolateΛ↑ {suc (suc _)} (_ , s≼t , _) (path-1 i) = interpolate-1 s≼t i

boundaryΛ-inv : ∀ {n} (x : □↑ (suc n)) → boundaryΛ (interpolateΛ↑ x) ≡ fst x
boundaryΛ-inv {zero} _ = refl
boundaryΛ-inv {suc _} (_ , _ , P) = ≡-× refl (boundaryΛ-inv (_ , P))

boundaryΛ↑-inv : ∀ {n} (x : □↑ (suc n)) → boundaryΛ↑ (interpolateΛ↑ x) ≡ x
boundaryΛ↑-inv _ = □↑≡ (boundaryΛ-inv _)

interpolateΛ↑-funExt : ∀ {n} (f : Λ n → S) (x : Λ n) → interpolateΛ↑ (boundaryΛ↑ {n} f) x ≡ f x
interpolateΛ↑-funExt {zero} _ _ = refl
interpolateΛ↑-funExt {suc _} _ = elim⊥∙ _ datum
  where
    open ElimData
    datum : ∀ {n} {f : Λ (suc n) → S} → ElimData λ x → interpolateΛ↑ (boundaryΛ↑ {suc n} f) x ≡ f x
    datum .baseP = refl
    datum {zero} .inclP _ = refl
    datum {suc _} .inclP = elim⊥∙ _ datum
    datum {zero} {f} .pathP s =
      sym (
        cong (λ f → f s) (SLinear {f = λ s → f (path s)}) ∙
        cong₃ interpolate (cong f path-0) (cong f path-1) refl)
    datum {suc _} {f} .pathP s =
      sym (
        cong (λ f → f s) (SLinear {f = λ s → f (path s)}) ∙
        cong₃ interpolate (cong f path-0) (cong f path-1) refl)
    datum .path-0P = isProp→PathP (λ _ → SisSet _ _) _ _
    datum .path-1P = isProp→PathP (λ _ → SisSet _ _) _ _

interpolateΛ↑-inv : ∀ {n} (f : Λ n → S) → interpolateΛ↑ (boundaryΛ↑ {n} f) ≡ f
interpolateΛ↑-inv {n} f = funExt (interpolateΛ↑-funExt {n} f)

PhoaΛ : ∀ {n} → Iso (Λ n → S) (□↑ (suc n))
PhoaΛ {n} = iso boundaryΛ↑ interpolateΛ↑ boundaryΛ↑-inv (interpolateΛ↑-inv {n})
