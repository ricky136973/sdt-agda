{-# OPTIONS --cubical --guardedness #-}

module PreSDT where

open import Orthogonal

open import Agda.Builtin.Cubical.Equiv

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat


private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ₁
    B : Type ℓ₂

postulate ℓ₀ : Level
postulate S : Type ℓ₀

postulate s0 : S
postulate s1 : S

postulate SisSet : isSet S

S→SisSet : isSet (S → S)
S→SisSet f g p q i j x = SisSet (f x) (g x) (λ i → p i x) (λ i → q i x) i j

def : S → Set ℓ₀
def s = s ≡ s1

defIsProp : ∀ {s} → isProp (def s)
defIsProp = SisSet _ _

postulate s0≠s1 : def s0 → ⊥

postulate defIsMono : ∀ {s t} → def s ≡ def t → s ≡ t 

L : Type ℓ → Type (ℓ-max ℓ ℓ₀)
L A = Σ[ s ∈ S ] (def s → A)

S≅L⊤ : Iso S (L Unit)
S≅L⊤ = iso (λ s → s , λ _ → tt) fst (λ _ → refl) (λ _ → refl)

S≃L⊤ : S ≃ L Unit
S≃L⊤ = isoToEquiv S≅L⊤

S≡L⊤ : S ≡ L Unit
S≡L⊤ = isoToPath S≅L⊤

-- S≃L⊤ : S ≃ L Unit
-- S≃L⊤ .fst s = s , λ _ → tt
-- S≃L⊤ .snd .equiv-proof (s , _) .fst = s , refl
-- S≃L⊤ .snd .equiv-proof _       .snd P i .fst = P .snd (~ i) .fst
-- S≃L⊤ .snd .equiv-proof (s , p) .snd P i .snd j .fst =
--   SisSet (P .snd (~ i) .fst) s (λ k → P .snd (~ i ∨ k) .fst) (λ k → P .snd (~ i ∨ k) .fst) i j
-- S≃L⊤ .snd .equiv-proof _       .snd _ _ .snd _ .snd _ = tt

L⊥ : L A
L⊥ = s0 , λ φ → rec⊥ (s0≠s1 φ)

η : A → L A
η x = s1 , λ _ → x

_⇀_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))
A ⇀ B = A → L B

map : (A → B) → L A → L B
map f (s , a) = s , λ φ → f (a φ)

step : (L A → A) → ℕ → A
step α zero = α L⊥
step α (suc n) = α (η (step α n))

data ω : Type ℓ₀ where
  σ : L ω → ω

ω-zero : ω
ω-zero = σ L⊥

ω-suc : ω → ω
ω-suc n = σ (η n)

ℕ→ω : ℕ → ω
ℕ→ω zero = ω-zero
ℕ→ω (suc n) = ω-suc (ℕ→ω n)

ℕ→ω≡step : ℕ→ω ≡ step σ
ℕ→ω≡step i zero = ω-zero
ℕ→ω≡step i (suc n) = ω-suc (ℕ→ω≡step i n)

record ϖ : Type ℓ₀ where
  coinductive
  constructor ς
  field
    π : L ϖ

open ϖ public

ι : ω → ϖ
ι (σ (s , f)) .π = s , λ φ → ι (f φ)

ι∘σ≡ς∘ι : ∀ x → ι (σ x) ≡ ς (map ι x)
ι∘σ≡ς∘ι x _ .π = x .fst , λ φ → ι (x .snd φ)

ϖ-zero : ϖ
ϖ-zero = ι ω-zero

ϖ-suc : ϖ → ϖ
ϖ-suc x .π = η x

ℕ→ϖ : ℕ → ϖ
ℕ→ϖ n = iter n ϖ-suc ϖ-zero

ℕ→ϖ≡ι∘ℕ→ω : ∀ n → ℕ→ϖ n ≡ ι (ℕ→ω n)
ℕ→ϖ≡ι∘ℕ→ω zero = refl
ℕ→ϖ≡ι∘ℕ→ω (suc n) i .π = η (ℕ→ϖ≡ι∘ℕ→ω n i)

∞ : ϖ
∞ .π = s1 , λ _ → ∞

suc∞≡∞ : ϖ-suc ∞ ≡ ∞
suc∞≡∞ _ .π = η ∞

Chain : Type ℓ → Type (ℓ-max ℓ₀ ℓ)
Chain A = ω → A

Chain* : Type ℓ → Type (ℓ-max ℓ₀ ℓ)
Chain* A = ϖ → A

ι* : Chain* A → Chain A
ι* c n = c (ι n)

isComplete : Type ℓ → Type (ℓ-max ℓ ℓ₀)
isComplete A = isEquiv (ι* {A = A})

isWellComplete : Type ℓ → Type (ℓ-max ℓ ℓ₀)
isWellComplete A = isComplete (L A)

sup : isComplete A → Chain A → A
sup P c = P .equiv-proof c .fst .fst ∞

⊥isComplete : isComplete ⊥
⊥isComplete .equiv-proof c = rec⊥ (c ω-zero)

ι⊥ : Type ℓ → Type (ℓ-max ℓ ℓ₀)
ι⊥ = isOrthoComplete {T = Unit} (λ _ → ι)

ι⊥isComplete : ι⊥ A → isComplete A
ι⊥isComplete P .equiv-proof c .fst .fst =
  P tt c .fst .fst
ι⊥isComplete P .equiv-proof c .fst .snd i =
  P tt c .fst .snd (~ i)
ι⊥isComplete P .equiv-proof c .snd (c* , p) i .fst =
  P tt c .snd (c* , sym p) i .fst
ι⊥isComplete P .equiv-proof c .snd (c* , p) i .snd j =
  P tt c .snd (c* , sym p) i .snd (~ j)

ι⊥ifComplete : isComplete A → ι⊥ A
ι⊥ifComplete P _ c .fst .fst =
  P .equiv-proof c .fst .fst
ι⊥ifComplete P _ c .fst .snd i =
  P .equiv-proof c .fst .snd (~ i)
ι⊥ifComplete P _ c .snd (c* , p) i .fst =
  P .equiv-proof c .snd (c* , sym p) i .fst
ι⊥ifComplete P _ c .snd (c* , p) i .snd j =
  P .equiv-proof c .snd (c* , sym p) i .snd (~ j)

⊤isComplete : isComplete Unit
⊤isComplete = ι⊥isComplete (⊤isOrthoComplete λ _ → ι)

ΠisComplete : {F : A → Type ℓ} → (∀ x → isComplete (F x)) → isComplete (∀ x → F x)
ΠisComplete P = ι⊥isComplete (ΠisOrthoComplete (λ _ → ι) λ x → ι⊥ifComplete (P x))

postulate SisComplete : isComplete S

ωχ : Chain* S → Type ℓ₀
ωχ χ = Σ[ n ∈ ω ] def (χ (ι n))

ϖχ : Chain* S → Type ℓ₀
ϖχ χ = Σ[ u ∈ ϖ ] def (χ u)

εχ : ∀ χ → ωχ χ → ϖχ χ
εχ χ (n , φ) = (ι n) , φ

εχ⊥ : Type ℓ → Type (ℓ-max ℓ ℓ₀)
εχ⊥ = isOrthoComplete εχ
