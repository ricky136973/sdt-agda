{-# OPTIONS --cubical --guardedness #-}

module SemiLattice where

open import PreSDT renaming (def to ⟦_⟧ ; map to L-map) public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat

≡-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ-syntax A B} →
  (p : fst x ≡ fst y) → (λ i → B (p i)) [ snd x ≡ snd y ] → x ≡ y
≡-Σ p P i = p i , P i

infix 20 _≼_
infix 20 _≽_
infix 40 _⊓_

_≼_ : S → S → Type ℓ₀
x ≼ y = ⟦ x ⟧ → ⟦ y ⟧

_≽_ : S → S → Type ℓ₀
x ≽ y = y ≼ x

opaque
  ≼-isProp : ∀ {x y} → isProp (x ≼ y)
  ≼-isProp x y i φ = defIsProp (x φ) (y φ) i

  ≼-refl : ∀ {x} → x ≼ x
  ≼-refl φ = φ

  ≼-reflP : ∀ {x y} → x ≡ y → x ≼ y
  ≼-reflP p = transport (cong ⟦_⟧ p)

  ≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
  ≼-trans x≼y y≼z φ = y≼z (x≼y φ)

  ≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
  ≼-antisym x≼y y≼x =
    defIsMono (isoToPath (iso x≼y y≼x (λ _ → defIsProp _ _) λ _ → defIsProp _ _))

  s0-min : ∀ {x} → s0 ≼ x
  s0-min φ = rec⊥ (s0≠s1 φ)

  s1-max : ∀ {x} → x ≼ s1
  s1-max _ = refl

postulate SΣ : L S → S
postulate SΣ-def : ∀ {s t} → ⟦ SΣ (s , t) ⟧ ≡ (Σ[ φ ∈ ⟦ s ⟧ ] ⟦ t φ ⟧)

opaque
  SΣ-≼L : ∀ {s t} → SΣ (s , t) ≼ s
  SΣ-≼L φ = transport SΣ-def φ .fst

  SΣ-≼R : ∀ {s t} φ → SΣ (s , t) ≼ t φ
  SΣ-≼R {s} {t} φ ψ =
    let x , y = transport SΣ-def ψ in
    transport (cong (λ x → ⟦ t x ⟧) (defIsProp x φ)) y

  SΣ-monotoneR : ∀ {s p q} → (∀ φ → p φ ≼ q φ) → SΣ (s , p) ≼ SΣ (s , q)
  SΣ-monotoneR P φ =
    let x , y = transport SΣ-def φ in
    transport (sym SΣ-def) (x , P x y)

  SΣ-φ : ∀ {s t φ} → SΣ (s , t) ≡ t φ
  SΣ-φ {_} {t} {φ} = defIsMono (SΣ-def ∙ isoToPath SΣ-φ≅)
    where
      SΣ-φ≅ : Iso (Σ[ φ ∈ _ ] ⟦ t φ ⟧) ⟦ t φ ⟧
      SΣ-φ≅ .Iso.fun (_ , y) = transport (cong (λ φ → ⟦ t φ ⟧) (defIsProp _ _)) y
      SΣ-φ≅ .Iso.inv = _,_ φ
      SΣ-φ≅ .Iso.rightInv _ = defIsProp _ _
      SΣ-φ≅ .Iso.leftInv _ = isPropΣ defIsProp (λ _ → defIsProp) _ _

_⊓_ : S → S → S
x ⊓ y = SΣ (x , λ _ → y)

opaque
  ⊓-intro : ∀ {x y z} → x ≼ y → x ≼ z → x ≼ y ⊓ z
  ⊓-intro x≼y y≼z φ = transport (sym SΣ-def) (x≼y φ , y≼z φ)

  x⊓y≼x : ∀ {x y} → x ⊓ y ≼ x
  x⊓y≼x = SΣ-≼L

  x⊓y≼y : ∀ {x y} → x ⊓ y ≼ y
  x⊓y≼y φ = SΣ-≼R (SΣ-≼L φ) φ

  x⊓y=x : ∀ {x y} → x ≼ y → x ⊓ y ≡ x
  x⊓y=x x≼y = ≼-antisym x⊓y≼x λ φ → transport (sym SΣ-def) (φ , x≼y φ)

  x⊓y=y : ∀ {x y} → y ≼ x → x ⊓ y ≡ y
  x⊓y=y y≼x = ≼-antisym x⊓y≼y λ φ → transport (sym SΣ-def) (y≼x φ , φ)

  0⊓x=0 : ∀ {x} → s0 ⊓ x ≡ s0
  0⊓x=0 = x⊓y=x s0-min

  x⊓0=0 : ∀ {x} → x ⊓ s0 ≡ s0
  x⊓0=0 = x⊓y=y s0-min

  1⊓x=x : ∀ {x} → s1 ⊓ x ≡ x
  1⊓x=x = x⊓y=y s1-max

  x⊓1=x : ∀ {x} → x ⊓ s1 ≡ x
  x⊓1=x = x⊓y=x s1-max

  ⊓-idem : ∀ {x} → x ⊓ x ≡ x
  ⊓-idem = x⊓y=x ≼-refl

  ⊓-comm : ∀ {x y} → x ⊓ y ≡ y ⊓ x
  ⊓-comm =
    defIsMono (SΣ-def ∙ isoToPath Σ-swap-Iso ∙ sym SΣ-def)

  ⊓-assoc : ∀ {x y z} → x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
  ⊓-assoc =
    defIsMono (SΣ-def ∙ (cong (_×_ _) SΣ-def) ∙ sym (SΣ-def ∙ cong (λ P → P × _) SΣ-def ∙ isoToPath Σ-assoc-Iso))

  ⊓-monotoneL : ∀ {x y z} → x ≼ y → x ⊓ z ≼ y ⊓ z
  ⊓-monotoneL x≼y φ =
    let ⟦x⟧ , ⟦z⟧ = transport SΣ-def φ in
    transport (sym SΣ-def) (x≼y ⟦x⟧ , ⟦z⟧)
  
  ⊓-monotoneR : ∀ {x y z} → y ≼ z → x ⊓ y ≼ x ⊓ z
  ⊓-monotoneR y≼z φ =
    let ⟦x⟧ , ⟦y⟧ = transport SΣ-def φ in
    transport (sym SΣ-def) (⟦x⟧ , y≼z ⟦y⟧)
  
  ⊓-monotone : ∀ {w x y z} → w ≼ y → x ≼ z → w ⊓ x ≼ y ⊓ z
  ⊓-monotone w≼y x≼z φ = ⊓-monotoneL w≼y (⊓-monotoneR x≼z φ)

  ⊓-congL : ∀ {x y z} → x ≡ y → x ⊓ z ≡ y ⊓ z
  ⊓-congL p = ≼-antisym (⊓-monotoneL (≼-reflP p)) (⊓-monotoneL (≼-reflP (sym p)))

  ⊓-congR : ∀ {x y z} → y ≡ z → x ⊓ y ≡ x ⊓ z
  ⊓-congR p = ≼-antisym (⊓-monotoneR (≼-reflP p)) (⊓-monotoneR (≼-reflP (sym p)))

  ⊓-cong : ∀ {w x y z} → w ≡ y → x ≡ z → w ⊓ x ≡ y ⊓ z
  ⊓-cong p q = ⊓-congL p ∙ ⊓-congR q

module Vector where
  variable ℓ ℓ' ℓ'' ℓ''' : Level
  variable A : Type ℓ
  variable B : Type ℓ'
  variable C : Type ℓ''
  variable R : A → A → Type ℓ'

  Vector : (A : Type ℓ) → ℕ → Type ℓ
  Vector A zero = Unit*
  Vector A (suc n) = A × Vector A n

  drop : ∀ {n} → Vector A (suc n) → Vector A n
  drop {n = zero} _ = tt*
  drop {n = suc _} (x , xs) = x , drop xs

  append : ∀ {n} → Vector A n → A → Vector A (suc n)
  append {n = zero} _ y = y , tt*
  append {n = suc _} (x , xs) y = x , append xs y

  reverse : ∀ {n} → Vector A n → Vector A n
  reverse {n = zero} _ = tt*
  reverse {n = suc n} (x , xs) = append (reverse xs) x

  map : (A → B) → ∀ {n} → Vector A n → Vector B n
  map f {zero} _ = tt*
  map f {suc _} (x , xs) = f x , map f xs

  map-comp : ∀ {n} {f : A → B} {g : B → C} {xs : Vector A n} →
    map g (map f xs) ≡ map (λ x → g (f x)) xs
  map-comp {n = zero} = refl
  map-comp {n = suc _} = ≡-× refl map-comp

  ListR : (R : A → A → Type ℓ') → ∀ {n} → A → Vector A n → Type ℓ'
  ListR R {zero} _ _ = Unit*
  ListR R {suc n} x (y , ys) = R x y × ListR R x ys

  ListRRev : (R : A → A → Type ℓ') → ∀ {n} → A → Vector A n → Type ℓ'
  ListRRev R = ListR (λ x y → R y x)

  ListRIsProp : {R : A → A → Type ℓ'} → (∀ x y → isProp (R x y)) → ∀ {n x} {y : Vector A n} → isProp (ListR R x y)
  ListRIsProp _ {zero} = isPropUnit*
  ListRIsProp P {suc n} = isProp× (P _ _) (ListRIsProp P)

  ListR-trans : ∀ {n} {x y} {zs : Vector A n} →
    (∀ x y z → R x y → R y z → R x z) → R x y → ListR R y zs → ListR R x zs
  ListR-trans {n = zero} _ _ _ = tt*
  ListR-trans {n = suc _} R-trans Rxy (Ryz , P) = R-trans _ _ _ Rxy Ryz , ListR-trans R-trans Rxy P

  ListR-append : ∀ {n x} {ys : Vector A n} {z} → ListR R x ys → R x z → ListR R x (append ys z)
  ListR-append {n = zero} _ Rxz = Rxz , tt*
  ListR-append {n = suc _} (Rxy , P) Rxz = Rxy , ListR-append P Rxz

  ListR-reverse : ∀ {n x} {ys : Vector A n} → ListR R x ys → ListR R x (reverse ys)
  ListR-reverse {n = zero} _ = tt*
  ListR-reverse {n = suc n} {x = x} {ys = y , ys} (Rxy , P) = ListR-append (ListR-reverse P) Rxy

  IsMonotonic : {A : Type ℓ} (R : A → A → Type ℓ') → ∀ {n} → Vector A n → Type (ℓ-max ℓ ℓ')
  IsMonotonic R {0} _ = Unit*
  IsMonotonic R {1} _ = Unit*
  IsMonotonic R {suc (suc n)} (x , y , z) = (R x y) × (IsMonotonic R (y , z))
  
  IsMonotonicIsProp :{A : Type ℓ} {R : A → A → Type ℓ'}
    → (∀ x y → isProp (R x y))
    → ∀ {n} {x : Vector A n} → isProp (IsMonotonic R x)
  IsMonotonicIsProp _ {0} = isPropUnit*
  IsMonotonicIsProp _ {1} = isPropUnit*
  IsMonotonicIsProp RisProp {suc (suc _)} = isProp× (RisProp _ _) (IsMonotonicIsProp RisProp)

  IsMonotonic-trans : ∀ {n} {x y} {zs : Vector A n} →
    (∀ x y z → R x y → R y z → R x z) → R x y → IsMonotonic R (y , zs) → IsMonotonic R (x , zs)
  IsMonotonic-trans {n = zero} _ _ _ = tt*
  IsMonotonic-trans {n = suc _} R-trans Rxy (Ryz , P) = R-trans _ _ _ Rxy Ryz , P

  ListRFromMonotone : ∀ {n} {xs : Vector A (suc n)} →
    (∀ x y z → R x y → R y z → R x z) → IsMonotonic R xs → ListR R (fst xs) (snd xs)
  ListRFromMonotone {n = 0} _ _ = tt*
  ListRFromMonotone {n = suc _} R-trans (Rxy , P) = Rxy , ListRFromMonotone R-trans (IsMonotonic-trans R-trans Rxy P)

  head-monotone : ∀ {n} {x : A} {ys : Vector A n} →
    ListR R x ys → IsMonotonic R ys → IsMonotonic R (x , ys)
  head-monotone {n = zero} _ _ = tt*
  head-monotone {n = suc _} (x≼y , _) Q = x≼y , Q

  tail-monotone : ∀ {n} {xs : Vector A (suc n)} →
    IsMonotonic R xs → IsMonotonic R (snd xs)
  tail-monotone {n = zero} P = tt*
  tail-monotone {n = suc _} (_ , P) = P

  drop-monotone : ∀ {n} {xs : Vector A (suc n)} →
    IsMonotonic R xs → IsMonotonic R (drop xs)
  drop-monotone {n = 0} _ = tt*
  drop-monotone {n = 1} _ = tt*
  drop-monotone {n = suc (suc n)} (Rxy , P) = Rxy , drop-monotone P

  append-monotone : ∀ {n} {xs : Vector A n} {y : A} →
    IsMonotonic R xs → ListRRev R y xs → IsMonotonic R (append xs y)
  append-monotone {n = 0} _ _ = tt*
  append-monotone {n = 1} _ (Rxy , _) = Rxy , tt*
  append-monotone {n = suc (suc _)} (Rxx' , P) (_ , Q) = Rxx' , append-monotone P Q

  reverse-monotone : ∀ {n} {xs : Vector A n} →
    (∀ x y z → R x y → R y z → R x z) → IsMonotonic R xs → IsMonotonic (λ x y → R y x) (reverse xs)
  reverse-monotone {n = zero} _ _ = tt*
  reverse-monotone {n = suc _} {xs = x , xs} R-trans P =
    append-monotone (reverse-monotone R-trans (tail-monotone P)) (ListR-reverse (ListRFromMonotone R-trans P))

  map-monotone : ∀
    {R : A → A → Type ℓ''}
    {R' : B → B → Type ℓ'''}
    (f : A → B) (r : ∀ x y → R x y → R' (f x) (f y))
    {n} {x : Vector A n} →
    IsMonotonic R x → IsMonotonic R' (map f x)
  map-monotone _ _ {0} _ = tt*
  map-monotone _ _ {1} _ = tt*
  map-monotone _ r {suc (suc _)} (Rxy , P) = r _ _ Rxy , map-monotone _ r P

open Vector

□ : ℕ → Type ℓ₀
□ = Vector S

δ : ∀ {n} → S → □ n
δ {zero} _ = tt*
δ {suc _} s = s , δ s

infix 20 _≼□_
infix 20 _≽□_

_≼□_ : ∀ {n} → S → □ n → Type ℓ₀
_≼□_ = ListR _≼_

opaque
  ≼□-isProp : ∀ {n} {x} {y : □ n} → isProp (x ≼□ y)
  ≼□-isProp = ListRIsProp λ _ _ → ≼-isProp

_≽□_ : ∀ {n} → S → □ n → Type ℓ₀
_≽□_ = ListR _≽_

opaque
  ≽□-isProp : ∀ {n} {x} {y : □ n} → isProp (x ≽□ y)
  ≽□-isProp = ListRIsProp λ _ _ → ≼-isProp

s0-min□ : ∀ {n} {x : □ n} → s0 ≼□ x
s0-min□ {zero} = tt*
s0-min□ {suc _} = s0-min , s0-min□

s1-max□ : ∀ {n} {x : □ n} → s1 ≽□ x
s1-max□ {zero} = tt*
s1-max□ {suc _} = s1-max , s1-max□

□1≅S : Iso (□ 1) S
□1≅S = iso fst (λ s → s , tt*) (λ _ → refl) (λ _ → refl)

□1≡S : □ 1 ≡ S
□1≡S = isoToPath □1≅S

L□→□ : ∀ {n} → L (□ n) → □ n
L□→□ {zero} _ = tt*
L□→□ {suc _} (s , t) = SΣ (s , λ φ → t φ .fst) , L□→□ (s , λ φ → t φ .snd)

opaque
  L□→□≽□ : ∀ {n} {x : L (□ n)} → x .fst ≽□ (L□→□ x)
  L□→□≽□ {zero} = tt*
  L□→□≽□ {suc n} {s , t} = SΣ-≼L , L□→□≽□

  L□→□≡ : ∀ {n s} {t : □ n} → s ≽□ t → L□→□ (s , λ _ → t) ≡ t
  L□→□≡ {zero} _ = refl
  L□→□≡ {suc _} (P , Q) = ≡-× (x⊓y=y P) (L□→□≡ Q)

  L□→□≡φ : ∀ {n s} {t : ⟦ s ⟧ → □ n} → (∀ φ → s ≽□ t φ) → {φ : ⟦ s ⟧} → L□→□ (s , t) ≡ t φ
  L□→□≡φ {zero} _ = refl
  L□→□≡φ {suc _} P = ≡-× SΣ-φ (L□→□≡φ (λ φ → P φ .snd))

increasing : ∀ {n} → □ n → Type ℓ₀
increasing = IsMonotonic _≼_

opaque
  increasingIsProp : ∀ {n} (x : □ n) → isProp (increasing x)
  increasingIsProp _ = IsMonotonicIsProp λ _ _ → ≼-isProp

  increasing-≼ : ∀ {n s t} {x : □ n} → s ≼ t → increasing (t , x) → increasing (s , x)
  increasing-≼ = IsMonotonic-trans λ _ _ _ → ≼-trans

  increasing→≼□ : ∀ {n s} {x : □ n} → increasing (s , x) → s ≼□ x
  increasing→≼□ = ListRFromMonotone λ _ _ _ → ≼-trans

decreasing : ∀ {n} → □ n → Type ℓ₀
decreasing = IsMonotonic _≽_

opaque
  decreasingIsProp : ∀ {n} (x : □ n) → isProp (decreasing x)
  decreasingIsProp _ = IsMonotonicIsProp λ _ _ → ≼-isProp

  decreasing-≽ : ∀ {n s t} {x : □ n} → s ≽ t → decreasing (t , x) → decreasing (s , x)
  decreasing-≽ = IsMonotonic-trans λ _ _ _ P Q → ≼-trans Q P

  decreasing→≽□ : ∀ {n s} {x : □ n} → decreasing (s , x) → s ≽□ x
  decreasing→≽□ = ListRFromMonotone λ _ _ _ P Q → ≼-trans Q P

□↑ : ℕ → Type ℓ₀
□↑ n = Σ[ x ∈ □ n ] increasing x

□↑≡ : ∀ {n} {x y : □↑ n} → fst x ≡ fst y → x ≡ y
□↑≡ = Σ≡Prop increasingIsProp

□↓ : ℕ → Type ℓ₀
□↓ n = Σ[ x ∈ □ n ] decreasing x

□↓≡ : ∀ {n} {x y : □↓ n} → fst x ≡ fst y → x ≡ y
□↓≡ = Σ≡Prop decreasingIsProp

□↑-d0 : ∀ {n} → □↑ (suc n) → □↑ n
□↑-d0 ((_ , x) , P) = x , tail-monotone P

□↑-d1 : ∀ {n} → □↑ (suc n) → □↑ n
□↑-d1 (x , P) = drop x , drop-monotone P

□↑-s0 : ∀ {n} → □↑ n → □↑ (suc n)
□↑-s0 (x , P) = (s0 , x) , head-monotone s0-min□ P

□↑-s1 : ∀ {n} → □↑ n → □↑ (suc n)
□↑-s1 (x , P) = append x s1 , append-monotone P s1-max□

□↓-d0 : ∀ {n} → □↓ (suc n) → □↓ n
□↓-d0 (x , P) = drop x , drop-monotone P

□↓-d1 : ∀ {n} → □↓ (suc n) → □↓ n
□↓-d1 ((_ , x) , P) = x , tail-monotone P

□↓-s0 : ∀ {n} → □↓ n → □↓ (suc n)
□↓-s0 (x , P) = append x s0 , append-monotone P s0-min□

□↓-s1 : ∀ {n} → □↓ n → □↓ (suc n)
□↓-s1 (x , P) = (s1 , x) , head-monotone s1-max□ P

□↑-reverse : ∀ {n} → □↑ n → □↓ n
□↑-reverse (x , P) = reverse x , reverse-monotone (λ _ _ _ → ≼-trans) P

□↓-reverse : ∀ {n} → □↓ n → □↑ n
□↓-reverse (x , P) = reverse x , reverse-monotone (λ _ _ _ P Q → ≼-trans Q P) P

δ↑ : ∀ {n} → S → □↑ n
δ↑ s .fst = δ s
δ↑ {0} _ .snd = tt*
δ↑ {1} _ .snd = tt*
δ↑ {suc (suc _)} s .snd = ≼-refl , δ↑ s .snd

δ↓ : ∀ {n} → S → □↓ n
δ↓ s .fst = δ s
δ↓ {0} _ .snd = tt*
δ↓ {1} _ .snd = tt*
δ↓ {suc (suc _)} s .snd = ≼-refl , δ↓ s .snd

L□→□-decreasing : ∀ {n} {x : L (□ n)} → (∀ φ → decreasing (x .snd φ)) → decreasing (L□→□ x)
L□→□-decreasing {0} _ = tt*
L□→□-decreasing {1} _ = tt*
L□→□-decreasing {suc (suc _)} P = (SΣ-monotoneR λ φ → P φ .fst) , L□→□-decreasing λ φ → P φ .snd

L□↓→□↓ : ∀ {n} → L (□↓ n) → □↓ (suc n)
L□↓→□↓ (s , t) .fst = s , L□→□ (s , λ φ → t φ .fst)
L□↓→□↓ {zero} _ .snd = tt*
L□↓→□↓ {suc _} (s , t) .snd =
  (λ φ → transport SΣ-def φ .fst) , L□→□-decreasing λ φ → t φ .snd

□↓→L□↓ : ∀ {n} → □↓ (suc n) → L (□↓ n)
□↓→L□↓ ((s , _) , _) .fst = s
□↓→L□↓ ((_ , t) , _) .snd _ .fst = t
□↓→L□↓ {zero} _ .snd _ .snd = tt*
□↓→L□↓ {suc _} (_ , P) .snd _ .snd = P .snd

L□↓≅□↓ : ∀ {n} → Iso (L (□↓ n)) (□↓ (suc n))
L□↓≅□↓ .Iso.fun = L□↓→□↓
L□↓≅□↓ .Iso.inv = □↓→L□↓

L□↓≅□↓ {zero} .Iso.rightInv _ = refl
L□↓≅□↓ {suc _} .Iso.rightInv (_ , P , Q) =
  □↓≡ (≡-× refl (≡-× (x⊓y=y P) (L□→□≡ (decreasing→≽□ (decreasing-≽ P Q)))))

L□↓≅□↓ {zero} .Iso.leftInv _ = refl
L□↓≅□↓ {suc n} .Iso.leftInv (s , t) =
  ≡-Σ refl (funExt (λ φ → □↓≡ (≡-× SΣ-φ (L□→□≡φ (λ φ → decreasing→≽□ (decreasing-≽ (λ _ → φ) (t φ .snd)))))))

L□↓≡□↓ : ∀ {n} → L (□↓ n) ≡ □↓ (suc n)
L□↓≡□↓ = isoToPath L□↓≅□↓

Δ : ℕ → Type ℓ₀
Δ zero = Unit*
Δ (suc n) = L (Δ n)

Δ1≅S : Iso (Δ 1) S
Δ1≅S = iso fst (λ s → s , λ _ → tt*) (λ _ → refl) (λ _ → refl)

Δ1≡S : Δ 1 ≡ S
Δ1≡S = isoToPath Δ1≅S

Δ≡□↓ : ∀ {n} → Δ n ≡ □↓ n
Δ≡□↓ {zero} = isoToPath (iso (λ _ → tt* , tt*) (λ _ → tt*) (λ _ → refl) (λ _ → refl))
Δ≡□↓ {suc _} = cong L Δ≡□↓ ∙ L□↓≡□↓
