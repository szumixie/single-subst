{-# OPTIONS --with-K --rewriting --postfix-projections #-}

module TT.SSC.Properties where

open import TT.Lib
open import TT.SSC
open import TT.SSC.AlphaNf

private variable
  i : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A B : Ty Γ i
  x : Var Γ A

infixl 2 _++_
data Tel (Γ : Con) : Set
_++_ : (Γ : Con) → Tel Γ → Con

infixl 2 _▹_
data Tel Γ where
  ◇ : Tel Γ
  _▹_ : (Ω : Tel Γ) → Ty (Γ ++ Ω) i → Tel Γ

Γ ++ ◇ = Γ
Γ ++ (Ω ▹ A) = (Γ ++ Ω) ▹ A

module _ where
  open import Data.Product

  private
    infixl 2 _▸′_
    data Tel-++ (Γ : Con) : Con → Set where
      ◆′ : Tel-++ Γ Γ
      _▸′_ : (Ω : Tel-++ Γ Δ) → Ty Δ i → Tel-++ Γ (Δ ▹ A)

    Tel′ : Con → Set
    Tel′ Γ = Σ[ Δ ∈ Con ] Tel-++ Γ Δ

    _++′_ : (Γ : Con) → Tel′ Γ → Con
    Γ ++′ Ω = Ω .proj₁

private variable
  Ω : Tel Γ

infixl 9 _[_]ᵀˡ
infixl 10 _⁺^
_[_]ᵀˡ : Tel Γ → Sub Δ Γ → Tel Δ
_⁺^ : (γ : Sub Δ Γ) → Sub (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω)

◇ [ γ ]ᵀˡ = ◇
(Ω ▹ A) [ γ ]ᵀˡ = Ω [ γ ]ᵀˡ ▹ A [ γ ⁺^ ]ᵀ

_⁺^ {Ω = ◇} γ = γ
_⁺^ {Ω = Ω ▹ A} γ = γ ⁺^ ⁺

module _ where
  open import Data.Product

  private
    []ᵀˡ-⁺^ : (Ω : Tel Γ) → Sub Δ Γ → Σ[ Ω′ ∈ Tel Δ ] Sub (Δ ++ Ω′) (Γ ++ Ω)
    []ᵀˡ-⁺^ ◇ γ .proj₁ = ◇
    []ᵀˡ-⁺^ ◇ γ .proj₂ = γ
    []ᵀˡ-⁺^ (Ω ▹ A) γ .proj₁ = []ᵀˡ-⁺^ Ω γ .proj₁ ▹ A [ []ᵀˡ-⁺^ Ω γ .proj₂ ]ᵀ
    []ᵀˡ-⁺^ (Ω ▹ A) γ .proj₂ = []ᵀˡ-⁺^ Ω γ .proj₂ ⁺

    infixl 9 _[_]ᵀˡ′
    _[_]ᵀˡ′ : Tel Γ → Sub Δ Γ → Tel Δ
    Ω [ γ ]ᵀˡ′ = []ᵀˡ-⁺^ Ω γ .proj₁

    infixl 10 _⁺^′
    _⁺^′ : (γ : Sub Δ Γ) → Sub (Δ ++ Ω [ γ ]ᵀˡ′) (Γ ++ Ω)
    γ ⁺^′ = []ᵀˡ-⁺^ _ γ .proj₂

infixl 10 _⁺^ʷ
_⁺^ʷ : Wk Δ Γ γ → Wk (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω) (γ ⁺^)
_⁺^ʷ {Ω = ◇} γ = γ
_⁺^ʷ {Ω = Ω ▹ A} γ = γ ⁺^ʷ ⁺

var-p-⁺-⁺^ʷ :
  {x : Var (Γ ++ Ω) B} → Wk Δ Γ γ →
  {! tm[ ? ] (var x [ p ⁺^ ]ᵗ [ γ ⁺ ⁺^ ]ᵗ)  !} ≡
  (Tm (Δ ▹ A ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) (B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ)
    ∋ var x [ γ ⁺^ ]ᵗ [ p ⁺^ ]ᵗ)
var-p-⁺-⁺^ʷ = {!   !}

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
