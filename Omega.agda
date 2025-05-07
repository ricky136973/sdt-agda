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

-------------------------------------------------------------

□∞ : Type ℓ₀
□∞ = ℕ → S

increasing∞ : □∞ → Type ℓ₀
increasing∞ x = ∀ n → (x n ≼ x (suc n))

increasing∞IsProp : ∀ x → isProp (increasing∞ x)
increasing∞IsProp _ _ _ = funExt λ _ → ≼-isProp _ _

□↑∞ : Type ℓ₀
□↑∞ = Σ[ x ∈ □∞ ] increasing∞ x

□↑∞≡ : ∀ {x y : □↑∞} → (∀ n → x .fst n ≡ y .fst n) → x ≡ y
□↑∞≡ p = Σ≡Prop increasing∞IsProp (funExt p)

decreasing∞ : □∞ → Type ℓ₀
decreasing∞ x = ∀ n → (x n ≽ x (suc n))

decreasing∞IsProp : ∀ x → isProp (decreasing∞ x)
decreasing∞IsProp _ _ _ = funExt λ _ → ≼-isProp _ _

□↓∞ : Type ℓ₀
□↓∞ = Σ[ x ∈ □∞ ] decreasing∞ x

□↓∞≡ : ∀ {x y : □↓∞} → (∀ n → x .fst n ≡ y .fst n) → x ≡ y
□↓∞≡ p = Σ≡Prop decreasing∞IsProp (funExt p)

□↑→□∞ : ∀ {n} → □↑ n → □∞
□↑→□∞ {0} _ _ = s1
□↑→□∞ {suc _} ((s , _) , _) 0 = s
□↑→□∞ {1} _ (suc _) = s1
□↑→□∞ {suc (suc _)} ((_ , x) , _ , P) (suc k) = □↑→□∞ (x , P) k

□↑→□∞-increasing : ∀ {n} → (x : □↑ n) → increasing∞ (□↑→□∞ x)
□↑→□∞-increasing {0} _ _ = s1-max
□↑→□∞-increasing {1} _ _ = s1-max
□↑→□∞-increasing {suc (suc _)} (_ , s≼t , _) 0 = s≼t
□↑→□∞-increasing {suc (suc _)} ((_ , x) , _ , P) (suc k) = □↑→□∞-increasing (x , P) k

□↑→∞ : ∀ {n} → □↑ n → □↑∞
□↑→∞ x = □↑→□∞ x , □↑→□∞-increasing x

□↓→□∞ : ∀ {n} → □↓ n → □∞
□↓→□∞ {0} _ _ = s0
□↓→□∞ {suc _} ((s , _) , _) 0 = s
□↓→□∞ {1} _ (suc _) = s0
□↓→□∞ {suc (suc _)} ((_ , x) , _ , P) (suc k) = □↓→□∞ (x , P) k

□↓ω→□∞-decreasing : ∀ {n} → (x : □↓ n) → decreasing∞ (□↓→□∞ x)
□↓ω→□∞-decreasing {0} _ _ = s0-min
□↓ω→□∞-decreasing {1} _ _ = s0-min
□↓ω→□∞-decreasing {suc (suc _)} (_ , s≽t , _) 0 = s≽t
□↓ω→□∞-decreasing {suc (suc _)} ((_ , x) , _ , P) (suc k) = □↓ω→□∞-decreasing (x , P) k

□↓→∞ : ∀ {n} → □↓ n → □↓∞
□↓→∞ x = □↓→□∞ x , □↓ω→□∞-decreasing x

infix 20 _∞≼∞_
infix 20 _∞≽∞_

_∞≼∞_ : □∞ → □∞ → Type ℓ₀
x ∞≼∞ y = ∀ n → x n ≼ y n

_∞≽∞_ : □∞ → □∞ → Type ℓ₀
x ∞≽∞ y = y ∞≼∞ x

boundaryω : (□↓ω → S) → □∞
boundaryω f n = f (incl (δ↓ {n} s1))
