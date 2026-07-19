{-# OPTIONS --cubical --guardedness #-}

module Orthogonal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

ortho : ∀ {ℓ₁ ℓ₂ ℓ₃}
  {X : Type ℓ₁}
  {Y : Type ℓ₂} →
  (X → Y) →
  Type ℓ₃ →
  Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃))
ortho f Z = ∀ (g : _ → Z) → isContr (Σ[ h ∈ (_ → Z) ] (g ≡ λ x → h (f x)))

isOrthoComplete : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃} 
  {T : Type ℓ₀}
  {X : T → Type ℓ₁}
  {Y : T → Type ℓ₂} →
  (∀ t → X t → Y t) →
  Type ℓ₃ →
  Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)))
isOrthoComplete f Z = ∀ t → ortho (f t) Z

⊤isOrthoComplete : ∀ {ℓ₀ ℓ₁ ℓ₂} 
  {T : Type ℓ₀}
  {X : T → Type ℓ₁}
  {Y : T → Type ℓ₂}
  (f : ∀ t → X t → Y t) →
  isOrthoComplete f Unit
⊤isOrthoComplete _ _ _ .fst .fst _ = tt
⊤isOrthoComplete _ _ _ .fst .snd _ _ = tt
⊤isOrthoComplete _ _ _ .snd _ _ .fst _ = tt
⊤isOrthoComplete _ _ _ .snd _ _ .snd _ _ = tt

ΠisOrthoComplete : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄} 
  {T : Type ℓ₀}
  {X : T → Type ℓ₁}
  {Y : T → Type ℓ₂}
  {U : Type ℓ₃}
  {Z : U → Type ℓ₄}
  (f : ∀ t → X t → Y t) →
  (∀ u → isOrthoComplete f (Z u)) →
  isOrthoComplete f (∀ u → Z u)
ΠisOrthoComplete f P t g .fst .fst y u =
  P u t (λ x → g x u) .fst .fst y
ΠisOrthoComplete f P t g .fst .snd i x u =
  P u t (λ x → g x u) .fst .snd i x
ΠisOrthoComplete f P t g .snd p i .fst y u =
  P u t (λ x → g x u) .snd
    ((λ y → p .fst y u) , λ i x → p .snd i x u) i .fst y
ΠisOrthoComplete f P t g .snd p i .snd j x u =
  P u t (λ x → g x u) .snd
    ((λ y → p .fst y u) , λ i x → p .snd i x u) i .snd j x
