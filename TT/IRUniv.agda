{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.IRUniv where

open import TT.Lib

private variable
  i : ℕ

data Uᵇ₀ : Set where

Elᵇ₀ : Uᵇ₀ → Set
Elᵇ₀ ()

module _ (U : Set) (El : U → Set) where
  data Uᵇ₊ : Set where
    `U : Uᵇ₊
    `Lift : U → Uᵇ₊

  Elᵇ₊ : Uᵇ₊ → Set
  Elᵇ₊ `U = U
  Elᵇ₊ (`Lift A) = El A

module _ (Uᵇ : Set) (Elᵇ : Uᵇ → Set) where
  data Uᶜ : Set
  Elᶜ : Uᶜ → Set

  data Uᶜ where
    base : Uᵇ → Uᶜ
    `⊤ : Uᶜ
    `Σ : (A : Uᶜ) → (Elᶜ A → Uᶜ) → Uᶜ
    `Π : (A : Uᶜ) → (Elᶜ A → Uᶜ) → Uᶜ

  Elᶜ (base A) = Elᵇ A
  Elᶜ `⊤ = ⊤
  Elᶜ (`Π A B) = (a : Elᶜ A) → Elᶜ (B a)
  Elᶜ (`Σ A B) = Σ (Elᶜ A) λ a → Elᶜ (B a)

Uᵇ : ℕ → Set
Elᵇ : Uᵇ i → Set

U : ℕ → Set
El : U i → Set

Uᵇ zero = Uᵇ₀
Uᵇ (suc i) = Uᵇ₊ (U i) El

Elᵇ {zero} = Elᵇ₀
Elᵇ {suc i} = Elᵇ₊ (U i) El

U i = Uᶜ (Uᵇ i) Elᵇ
El {i} = Elᶜ (Uᵇ i) Elᵇ

data Uᵇω : Set where
  `U : ℕ → Uᵇω
  `Lift : U i → Uᵇω

Elᵇω : Uᵇω → Set
Elᵇω (`U i) = U i
Elᵇω (`Lift A) = El A

Uω : Set
Uω = Uᶜ Uᵇω Elᵇω

Elω : Uω → Set
Elω = Elᶜ Uᵇω Elᵇω
