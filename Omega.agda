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

open import Cubical.HITs.SequentialColimit renaming (elim to elim→)

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
□↓ω→ω (push {suc (suc _)} ((s , t , x) , s≽t , P) i) = σ (s , λ _ → □↓ω→ω (push ((t , x) , P) i))

SMonotoneω : ∀ {n} {x y : □↓ n} (f : □↓ω → S) → fst x □≼□ fst y → f (incl x) ≼ f (incl y)
SMonotoneω f = SMonotoneN↓ λ x → f (incl x)

-------------------------------------------------------------

□∞ : Type ℓ₀
□∞ = ℕ → S

□∞-tail : □∞ → □∞
□∞-tail x n = x (suc n)

□∞-proj : ∀ n → □∞ → □ n
□∞-proj zero x = tt*
□∞-proj (suc n) x = x 0 , □∞-proj n (□∞-tail x)

increasing∞ : □∞ → Type ℓ₀
increasing∞ x = ∀ n → (x n ≼ x (suc n))

increasing∞IsProp : ∀ x → isProp (increasing∞ x)
increasing∞IsProp _ _ _ = funExt λ _ → ≼-isProp _ _

□↑∞ : Type ℓ₀
□↑∞ = Σ[ x ∈ □∞ ] increasing∞ x

□↑∞≡ : ∀ {x y : □↑∞} → (∀ n → x .fst n ≡ y .fst n) → x ≡ y
□↑∞≡ p = Σ≡Prop increasing∞IsProp (funExt p)

□↑∞-d0 : □↑∞ → □↑∞
□↑∞-d0 (x , P) = □∞-tail x , λ n → P (suc n)

decreasing∞ : □∞ → Type ℓ₀
decreasing∞ x = ∀ n → (x n ≽ x (suc n))

decreasing∞IsProp : ∀ x → isProp (decreasing∞ x)
decreasing∞IsProp _ _ _ = funExt λ _ → ≼-isProp _ _

□↓∞ : Type ℓ₀
□↓∞ = Σ[ x ∈ □∞ ] decreasing∞ x

□↓∞≡ : ∀ {x y : □↓∞} → (∀ n → x .fst n ≡ y .fst n) → x ≡ y
□↓∞≡ p = Σ≡Prop decreasing∞IsProp (funExt p)

□↓∞-d1 : □↓∞ → □↓∞
□↓∞-d1 (x , P) = □∞-tail x , λ n → P (suc n)

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

module _ where
  open Vector

  boundaryω : (□↓ω → S) → □∞
  boundaryω f n = f (incl (δ↓ {n} s1))

  boundaryω≡boundary : ∀ {n} f → □∞-proj (suc n) (boundaryω f) ≡ boundary λ x → f (incl x)
  boundaryω≡boundary {zero} f = refl
  boundaryω≡boundary {suc n} f =
    ≡-× (cong f δ↓-s0-reduce) (
      ≡-× refl (cong (□∞-proj n) (funExt λ n → cong f (cong incl (□↓≡ refl)))) ∙
      (boundaryω≡boundary λ x → f (□↓ω-s1 x)) ∙
      sym map-comp
    )
    where
      □↓ω-zero : □↓ω
      □↓ω-zero = incl (tt* , tt*)

      δ↓-s0-reduce : ∀ {n} → □↓ω-zero ≡ incl (δ↓ {n} s0)
      δ↓-s0-reduce {zero} = refl
      δ↓-s0-reduce {suc n} = δ↓-s0-reduce ∙ (push (δ↓ s0)) ∙ cong incl (□↓≡ δ-append)
        where
          δ-append : ∀ {n} → append (δ {n} s0) s0 ≡ δ s0
          δ-append {zero} = refl
          δ-append {suc n} = ≡-× refl δ-append

      □↓ω-s1 : □↓ω → □↓ω
      □↓ω-s1 (incl x) = incl (□↓-s1 x)
      □↓ω-s1 (push x i) = (push (□↓-s1 x) ∙ cong incl □↓-s0-s1-comm) i
        where
          □↓-s0-s1-comm : ∀ {n} {x : □↓ n} → □↓-s0 (□↓-s1 x) ≡ □↓-s1 (□↓-s0 x)
          □↓-s0-s1-comm = □↓≡ refl

  boundaryω-increasing : ∀ {f} → increasing∞ (boundaryω f)
  boundaryω-increasing {f} n = ≼-trans (≼-reflP λ i → f (push (δ↓ {n} s1) i)) (SMonotoneω f δ1-□↓-s0)
    where
      δ1-□↓-s0 : ∀ {n} → □↓-s0 {n} (δ↓ s1) .fst □≼□ (δ↓ s1) .fst
      δ1-□↓-s0 {zero} = s1-max , tt*
      δ1-□↓-s0 {suc _} = s1-max , δ1-□↓-s0

boundary↑ω : (□↓ω → S) → □↑∞
boundary↑ω f = boundaryω f , boundaryω-increasing {f}

-------------------------------------------------------------

zipω : □∞ → ∀ {n} → □ n → S
zipω x {zero} y = s0
zipω x {suc n} (t , y) = x zero ⊓ t ⊔ zipω (□∞-tail x) y

zipω≡zip : ∀ {n x} {y : □ n} → zipω x y ≡ zip (□∞-proj _ x) y
zipω≡zip {zero} = refl
zipω≡zip {suc n} = ⊔-congR zipω≡zip

interpolateω : □∞ → ∀ {n} → □ n → S
interpolateω x y = x zero ⊔ zipω (□∞-tail x) y

interpolateω≡interpolateN : ∀ {n x} {y : □ n} → interpolateω x y ≡ interpolateN (□∞-proj _ x) y
interpolateω≡interpolateN = ⊔-congR zipω≡zip

module _ where
  open Vector

  zipω-push : ∀ {n x} {y : □ n} → zipω x y ≡ zipω x (append y s0)
  zipω-push {zero} = sym (x⊔y=y x⊓y≼y)
  zipω-push {suc _} = ⊔-congR zipω-push

  interpolateω-push : ∀ x {n} (y : □ n) → interpolateω x y ≡ interpolateω x (append y s0)
  interpolateω-push _ _ = ⊔-congR zipω-push

interpolate↑ω : □↑∞ → □↓ω → S
interpolate↑ω (x , _) (incl (y , _)) = interpolateω x y
interpolate↑ω (x , _) (push (y , _) i) = interpolateω-push x y i

-------------------------------------------------------------

boundaryω-inv : ∀ x n → boundaryω (interpolate↑ω x) n ≡ fst x n
boundaryω-inv x zero = x⊔y=x s0-min
boundaryω-inv (x , P) (suc n) =
  ⊔-assoc ∙
  ⊔-congL (⊔-congR x⊓1=x ∙ x⊔y=y (P 0)) ∙
  boundaryω-inv (□↑∞-d0 (x , P)) n

boundary↑ω-inv : ∀ x → boundary↑ω (interpolate↑ω x) ≡ x
boundary↑ω-inv x = □↑∞≡ (boundaryω-inv x)

interpolate↑ω-funExt : ∀ f x → interpolate↑ω (boundary↑ω f) x ≡ f x
interpolate↑ω-funExt f = elim→ _ _ datum
  where
    datum : ElimData _ _
    datum .ElimData.inclP _ =
      interpolateω≡interpolateN {x = boundaryω f} ∙
      cong₂ interpolateN (boundaryω≡boundary f) refl ∙
      interpolate↑-funExt (λ x → f (incl x)) _
    datum .ElimData.pushP _ = isProp→PathP (λ _ → SisSet _ _) _ _

interpolate↑ω-inv : ∀ f → interpolate↑ω (boundary↑ω f) ≡ f
interpolate↑ω-inv f = funExt (interpolate↑ω-funExt f)

Phoaω : Iso (□↓ω → S) □↑∞
Phoaω = iso boundary↑ω interpolate↑ω boundary↑ω-inv interpolate↑ω-inv

-------------------------------------------------------------

data Λω : Type ℓ₀ where
  step : ℕ → Λω
  succ : ℕ → S → Λω
  succ-0 : ∀ n → succ n s0 ≡ step n
  succ-1 : ∀ n → succ n s1 ≡ step (suc n)

record ElimDataΛω {ℓ} (P : Λω → Type ℓ) : Type (ℓ-max ℓ ℓ₀) where
  constructor elimdataΛω
  field
    stepP : ∀ n → P (step n)
    succP : ∀ n s → P (succ n s)
    succ-0P : ∀ n → PathP (λ i → P (succ-0 n i)) (succP n s0) (stepP n)
    succ-1P : ∀ n → PathP (λ i → P (succ-1 n i)) (succP n s1) (stepP (suc n))

elimΛω : ∀ {ℓ} (P : Λω → Type ℓ) → ElimDataΛω P → (x : Λω) → P x
elimΛω _ (elimdataΛω stepP _ _ _) (step _) = stepP _
elimΛω _ (elimdataΛω _ succP _ _) (succ _ _) = succP _ _
elimΛω _ (elimdataΛω _ _ succ-0P _) (succ-0 _ i) = succ-0P _ i
elimΛω _ (elimdataΛω _ _ _ succ-1P) (succ-1 _ i) = succ-1P _ i

boundaryΛω : (Λω → S) → □∞
boundaryΛω f n = f (step n)

boundaryΛω-increasing : ∀ {f} → increasing∞ (boundaryΛω f)
boundaryΛω-increasing {f} n =
  transport
    (cong₂ _≼_ (cong f (succ-0 n)) (cong f (succ-1 n)))
    (f0≼f1 (λ s → f (succ n s)))

boundaryΛ↑ω : (Λω → S) → □↑∞
boundaryΛ↑ω f = boundaryΛω f , boundaryΛω-increasing {f}

interpolateΛ↑ω : □↑∞ → Λω → S
interpolateΛ↑ω (x , _) (step n) = x n
interpolateΛ↑ω (x , _) (succ n s) = interpolate (x n) (x (suc n)) s
interpolateΛ↑ω (x , _) (succ-0 n i) = interpolate-0 (x n) (x (suc n)) i
interpolateΛ↑ω (_ , P) (succ-1 n i) = interpolate-1 (P n) i

boundaryΛ↑ω-inv : ∀ x → boundaryΛ↑ω (interpolateΛ↑ω x) ≡ x
boundaryΛ↑ω-inv _ = □↑∞≡ λ _ → refl

interpolateΛ↑ω-funExt : ∀ f x → interpolateΛ↑ω (boundaryΛ↑ω f) x ≡ f x
interpolateΛ↑ω-funExt f = elimΛω _ datum
  where
    datum : ElimDataΛω _
    datum .ElimDataΛω.stepP _ = refl
    datum .ElimDataΛω.succP n s =
      sym (
        cong (λ f → f s) (SLinear {λ s → f (succ n s)}) ∙
        cong₃ interpolate (cong f (succ-0 _)) (cong f (succ-1 _)) refl)
    datum .ElimDataΛω.succ-0P _ = isProp→PathP (λ _ → SisSet _ _) _ _
    datum .ElimDataΛω.succ-1P _ = isProp→PathP (λ _ → SisSet _ _) _ _

interpolateΛ↑ω-inv : ∀ f → interpolateΛ↑ω (boundaryΛ↑ω f) ≡ f
interpolateΛ↑ω-inv _ = funExt (interpolateΛ↑ω-funExt _)

PhoaΛω : Iso (Λω → S) □↑∞
PhoaΛω = iso boundaryΛ↑ω interpolateΛ↑ω boundaryΛ↑ω-inv interpolateΛ↑ω-inv
