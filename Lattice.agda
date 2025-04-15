{-# OPTIONS --cubical --guardedness #-}

module Lattice where

open import SemiLattice public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Cubical.HITs.Join

infix 30 _⊎_
infix 30 _⊔_

_⊎_ = join

rec⊎ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  (f : A → C) (g : B → C) (p : ∀ x y → f x ≡ g y) (x : A ⊎ B) → C
rec⊎ f g p (inl x) = f x
rec⊎ f g p (inr y) = g y
rec⊎ f g p (push a b i) = p a b i

postulate _⊔_ : S → S → S
postulate ⊔-def : ∀ {x y} → ⟦ x ⊔ y ⟧ ≡ ⟦ x ⟧ ⊎ ⟦ y ⟧

opaque
  x≼x⊔y : ∀ {x y} → x ≼ x ⊔ y
  x≼x⊔y φ = transport (sym ⊔-def) (inl φ)

  y≼x⊔y : ∀ {x y} → y ≼ x ⊔ y
  y≼x⊔y φ = transport (sym ⊔-def) (inr φ)

  x⊔y=x : ∀ {x y} → y ≼ x → x ⊔ y ≡ x
  x⊔y=x y≼x = ≼-partial (λ φ → rec⊎ (λ φ → φ) y≼x (λ _ _ → defIsProp _ _) (transport ⊔-def φ)) x≼x⊔y

  x⊔y=y : ∀ {x y} → x ≼ y → x ⊔ y ≡ y
  x⊔y=y x≼y = ≼-partial (λ φ → rec⊎ x≼y (λ φ → φ) (λ _ _ → defIsProp _ _) (transport ⊔-def φ)) y≼x⊔y

  0⊔x=x : ∀ {x} → s0 ⊔ x ≡ x
  0⊔x=x = x⊔y=y s0-min

  x⊔0=x : ∀ {x} → x ⊔ s0 ≡ x
  x⊔0=x = x⊔y=x s0-min

  1⊔x=1 : ∀ {x} → s1 ⊔ x ≡ s1
  1⊔x=1 = x⊔y=x s1-max

  x⊔1=1 : ∀ {x} → x ⊔ s1 ≡ s1
  x⊔1=1 = x⊔y=y s1-max

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

interpole : S → S → S → S
interpole s t x = s ⊔ x ⊓ t

postulate SLinear : {f : S → S} → f ≡ interpole (f s0) (f s1)

opaque
  SMonotone : ∀ {x y} (f : S → S) → x ≼ y → f x ≼ f y
  SMonotone {x} {y} f x≼y =
    transport (sym (cong (λ f → f x ≼ f y) SLinear)) (⊔-monotoneR (⊓-monotoneL x≼y))

  SFunExt : ∀ {f g : S → S} → f s0 ≡ g s0 → f s1 ≡ g s1 → f ≡ g
  SFunExt {f} {g} p q =
    transport (sym (cong₂ _≡_ SLinear SLinear)) (funExt λ s → cong₂ (λ x y → interpole x y s) p q)

Phoa : Iso (S → S) (□↓ 2)
Phoa .Iso.fun f = (f s1 , f s0 , tt*) , SMonotone f s1-max , tt*
Phoa .Iso.inv ((t , s , _) , _) = interpole s t
Phoa .Iso.rightInv ((t , s , _) , P , _) =
  Σ≡Prop
    (λ _ → isProp× ≼-isProp isPropUnit*)
    (≡-×
      ((x⊔y=y (≼-trans P (≼-reflP (sym 1⊓x=x)))) ∙ 1⊓x=x)
      (≡-× (x⊔y=x (≼-trans x⊓y≼x s0-min)) refl))
Phoa .Iso.leftInv f =
  SFunExt
    (x⊔y=x (≼-trans (≼-reflP 0⊓x=0) s0-min))
    ((x⊔y=y (≼-trans (SMonotone f s1-max) (≼-reflP (sym 1⊓x=x)))) ∙ 1⊓x=x)
