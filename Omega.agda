{-# OPTIONS --cubical --guardedness #-}

module Omega where

open import Lattice public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sequence

open import Cubical.HITs.SequentialColimit

□↑-seq : Sequence ℓ₀
□↑-seq = sequence □↑ □↑-s1

□↓-seq : Sequence ℓ₀
□↓-seq = sequence □↓ □↓-s0

□↑ω : Type ℓ₀
□↑ω = SeqColim □↑-seq

□↓ω : Type ℓ₀
□↓ω = SeqColim □↓-seq

□↓ω→ω : □↓ω → ω
□↓ω→ω (incl {0} _) = ω-zero
□↓ω→ω (incl {1} ((s , _) , _)) = σ (s , λ _ → ω-zero)
□↓ω→ω (incl {suc (suc _)} ((s , t , x) , s≽t , P)) = σ (s , λ _ → □↓ω→ω (incl ((t , x) , P)))
□↓ω→ω (push {0} _ i) = σ (s0 , λ φ → rec⊥ {A = rec⊥ (s0≠s1 φ) ≡ ω-zero} (s0≠s1 φ) i)
□↓ω→ω (push {1} ((s , _) , _) i) = σ (s , λ _ → □↓ω→ω (push (tt* , tt*) i))
□↓ω→ω (push {suc (suc n)} ((s , t , x) , s≽t , P) i) = σ (s , λ _ → □↓ω→ω (push ((t , x) , P) i))

record □∞ : Type ℓ₀ where
  inductive
  no-eta-equality
  pattern
  constructor _,_
  field
    fst : S
    snd : □∞

module _ where
  open □∞

  increasing∞ : □∞ → Type ℓ₀
  increasing∞ (s , t , x) = (s ≼ t) × increasing∞ (t , x)

  decreasing∞ : □∞ → Type ℓ₀
  decreasing∞ (s , t , x) = (s ≽ t) × decreasing∞ (t , x)
