{-# OPTIONS --cubical --guardedness #-}

module SemiLattice where

open import PreSDT renaming (def to ⟦_⟧) public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat

≡-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ-syntax A B} →
  (p : fst x ≡ fst y) → PathP (λ i → B (p i)) (snd x) (snd y) → x ≡ y
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

  ≼-partial : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
  ≼-partial x≼y y≼x =
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
  x⊓y≼x : ∀ {x y} → x ⊓ y ≼ x
  x⊓y≼x = SΣ-≼L

  x⊓y≼y : ∀ {x y} → x ⊓ y ≼ y
  x⊓y≼y φ = SΣ-≼R (SΣ-≼L φ) φ

  x⊓y=x : ∀ {x y} → x ≼ y → x ⊓ y ≡ x
  x⊓y=x x≼y = ≼-partial x⊓y≼x λ φ → transport (sym SΣ-def) (φ , x≼y φ)

  x⊓y=y : ∀ {x y} → y ≼ x → x ⊓ y ≡ y
  x⊓y=y y≼x = ≼-partial x⊓y≼y λ φ → transport (sym SΣ-def) (y≼x φ , φ)

  0⊓x=0 : ∀ {x} → s0 ⊓ x ≡ s0
  0⊓x=0 = x⊓y=x s0-min

  x⊓0=0 : ∀ {x} → x ⊓ s0 ≡ s0
  x⊓0=0 = x⊓y=y s0-min

  1⊓x=x : ∀ {x} → s1 ⊓ x ≡ x
  1⊓x=x = x⊓y=y s1-max

  x⊓1=x : ∀ {x} → x ⊓ s1 ≡ x
  x⊓1=x = x⊓y=x s1-max

  ⊓-monotoneL : ∀ {x y z} → x ≼ y → x ⊓ z ≼ y ⊓ z
  ⊓-monotoneL x≼y φ =
    let ⟦x⟧ , ⟦z⟧ = transport SΣ-def φ in
    transport (sym SΣ-def) (x≼y ⟦x⟧ , ⟦z⟧)
  
  ⊓-monotoneR : ∀ {x y z} → y ≼ z → x ⊓ y ≼ x ⊓ z
  ⊓-monotoneR y≼z φ =
    let ⟦x⟧ , ⟦y⟧ = transport SΣ-def φ in
    transport (sym SΣ-def) (⟦x⟧ , y≼z ⟦y⟧)

□ : ℕ → Type ℓ₀
□ zero = Unit*
□ (suc n) = S × □ n

infix 20 _≼□_
infix 20 _≽□_

_≼□_ : ∀ {n} → S → □ n → Type ℓ₀
_≼□_ {zero} _ _ = Unit*
_≼□_ {suc _} s (t , x) = (s ≼ t) × (s ≼□ x)

opaque
  ≼□-isProp : ∀ {n} {x} {y : □ n} → isProp (x ≼□ y)
  ≼□-isProp {zero} = isPropUnit*
  ≼□-isProp {suc _} = isProp× ≼-isProp ≼□-isProp

_≽□_ : ∀ {n} → S → □ n → Type ℓ₀
_≽□_ {zero} _ _ = Unit*
_≽□_ {suc _} s (t , x) = (s ≽ t) × (s ≽□ x)

opaque
  ≽□-isProp : ∀ {n} {x} {y : □ n} → isProp (x ≽□ y)
  ≽□-isProp {zero} = isPropUnit*
  ≽□-isProp {suc _} = isProp× ≼-isProp ≽□-isProp

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
increasing {0} _ = Unit*
increasing {1} _ = Unit*
increasing {suc (suc _)} (x , y , z) = (x ≼ y) × increasing (y , z)

opaque
  increasingIsProp : ∀ {n} {x : □ n} → isProp (increasing x)
  increasingIsProp {0} = isPropUnit*
  increasingIsProp {1} = isPropUnit*
  increasingIsProp {suc (suc _)} = isProp× ≼-isProp increasingIsProp

  increasing-≼ : ∀ {n s t} {x : □ n} → s ≼ t → increasing (t , x) → increasing (s , x)
  increasing-≼ {zero} _ _ = tt*
  increasing-≼ {suc _} P (Q , R) = ≼-trans P Q , R

  increasing→≼□ : ∀ {n s} {x : □ n} → increasing (s , x) → s ≼□ x
  increasing→≼□ {zero} _ = tt*
  increasing→≼□ {suc _} (P , Q) = P , increasing→≼□ (increasing-≼ P Q)

decreasing : ∀ {n} → □ n → Type ℓ₀
decreasing {0} _ = Unit*
decreasing {1} _ = Unit*
decreasing {suc (suc n)} (x , y , z) = (x ≽ y) × decreasing (y , z)

opaque
  decreasingIsProp : ∀ {n} {x : □ n} → isProp (decreasing x)
  decreasingIsProp {0} = isPropUnit*
  decreasingIsProp {1} = isPropUnit*
  decreasingIsProp {suc (suc _)} = isProp× ≼-isProp decreasingIsProp

  decreasing-≽ : ∀ {n s t} {x : □ n} → s ≽ t → decreasing (t , x) → decreasing (s , x)
  decreasing-≽ {zero} _ _ = tt*
  decreasing-≽ {suc _} P (Q , R) = (≼-trans Q P) , R

  decreasing→≽□ : ∀ {n s} {x : □ n} → decreasing (s , x) → s ≽□ x
  decreasing→≽□ {zero} _ = tt*
  decreasing→≽□ {suc _} (P , Q) = P , decreasing→≽□ (decreasing-≽ P Q)

□↑ : ℕ → Type ℓ₀
□↑ n = Σ[ x ∈ □ n ] increasing x

□↓ : ℕ → Type ℓ₀
□↓ n = Σ[ x ∈ □ n ] decreasing x

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
  Σ≡Prop
    (λ _ → isProp× ≼-isProp decreasingIsProp)
    (≡-× refl (≡-× (x⊓y=y P) (L□→□≡ (decreasing→≽□ (decreasing-≽ P Q)))))

L□↓≅□↓ {zero} .Iso.leftInv _ = refl
L□↓≅□↓ {suc n} .Iso.leftInv (s , t) =
  ≡-Σ refl (funExt λ φ → Σ≡Prop
    (λ _ → decreasingIsProp)
    (≡-× SΣ-φ (L□→□≡φ (λ φ → decreasing→≽□ (decreasing-≽ (λ _ → φ) (t φ .snd))))))

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
