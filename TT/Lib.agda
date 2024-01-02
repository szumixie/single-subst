{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check #-}

module TT.Lib where

open import Agda.Primitive public

infixr 2 Σₚ
infix 4 _↝_ _≡_ _≡[_]_
infixr 4 _,,_
infixl 5 the
infixr 9 _∙_ _∙ᵈ_

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A A₀ A₁ B : Set ℓ
  P₀ P₁ : Prop ℓ
  a a₀ a₁ a₂ a₃ : A

postulate
  _↝_ : A → A → Propω
{-# BUILTIN REWRITE _↝_ #-}

the : (A : Set ℓ) → A → A
the _ a = a
{-# INLINE the #-}

syntax the A a = a ∈ A

record Lift (P : Prop ℓ) : Set ℓ where
  eta-equality
  constructor lift
  field
    lower : P

open Lift public

data _≡_ {A : Set ℓ} (a : A) : A → Prop ℓ where
  refl : a ≡ a

sym : a₀ ≡ a₁ → a₁ ≡ a₀
sym refl = refl

_∙_ : a₀ ≡ a₁ → a₁ ≡ a₂ → a₀ ≡ a₂
refl ∙ a₁₂ = a₁₂

coeₚ : P₀ ≡ P₁ → P₀ → P₁
coeₚ refl p = p

private postulate
  coe₀ : A₀ ≡ A₁ → A₀ → A₁
  coe₀-refl : coe₀ refl a ↝ a
  {-# REWRITE coe₀-refl #-}

opaque
  coe : A₀ ≡ A₁ → A₀ → A₁
  coe = coe₀

  coe-refl : coe refl a ≡ a
  coe-refl = refl

private variable
  A₀₁ A₁₂ A₂₁ A₃₂ : A₀ ≡ A₁

_≡[_]_ : A₀ → A₀ ≡ A₁ → A₁ → Prop _
a₀ ≡[ A₀₁ ] a₁ = coe A₀₁ a₀ ≡ a₁

opaque
  unfolding coe

  reflᵈ : a₀ ≡[ refl ] a₀
  reflᵈ = refl

  symᵈ : a₀ ≡[ A₀₁ ] a₁ → a₁ ≡[ sym A₀₁ ] a₀
  symᵈ {A₀₁ = refl} refl = refl

  _∙ᵈ_ : a₀ ≡[ A₀₁ ] a₁ → a₁ ≡[ A₁₂ ] a₂ → a₀ ≡[ A₀₁ ∙ A₁₂ ] a₂
  _∙ᵈ_ {A₀₁ = refl} refl a₁₂ = a₁₂

  dep : a₀ ≡ a₁ → a₀ ≡[ refl ] a₁
  dep a₀₁ = a₀₁

  undep : a₀ ≡[ refl ] a₁ → a₀ ≡ a₁
  undep a₀₁ = a₀₁

  splitl : a₀ ≡[ A₀₁ ∙ A₁₂ ] a₂ → coe A₀₁ a₀ ≡[ A₁₂ ] a₂
  splitl {A₀₁ = refl} a₀₂ = a₀₂

  splitr : a₀ ≡[ A₀₁ ∙ sym A₂₁ ] a₂ → a₀ ≡[ A₀₁ ] coe A₂₁ a₂
  splitr {A₀₁ = refl} {A₂₁ = refl} a₀₂ = a₀₂

  splitlr : a₀ ≡[ A₀₁ ∙ A₁₂ ∙ sym A₃₂ ] a₃ → coe A₀₁ a₀ ≡[ A₁₂ ] coe A₃₂ a₃
  splitlr {A₀₁ = refl} {A₁₂ = refl} {A₃₂ = refl} a₀₃ = a₀₃

record Σₚ (P : Prop ℓ₁) (Q : P → Prop ℓ₂) : Prop (ℓ₁ ⊔ ℓ₂) where
  constructor _,,_
  field
    fst : P
    snd : Q fst

open Σₚ public
syntax Σₚ P (λ p → Q) = Σₚ[ p ∈ P ] Q

record ⊤ : Set where
  eta-equality
  constructor ⋆

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
