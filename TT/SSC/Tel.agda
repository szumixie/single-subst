{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Tel where

open import TT.Lib
open import TT.SSC.Syntax
open import TT.SSC.Path

private variable
  i i₀ i₁ : ℕ
  Γ Δ : Con
  A A₀ A₁ : Ty Γ i

infixl 2 _++_
data Tel (Γ : Con) : Set
_++_ : (Γ : Con) → Tel Γ → Con

infixl 2 _▹_
data Tel Γ where
  ◇ : Tel Γ
  _▹_ : (Ω : Tel Γ) → Ty (Γ ++ Ω) i → Tel Γ

Γ ++ ◇ = Γ
Γ ++ (Ω ▹ A) = (Γ ++ Ω) ▹ A

private variable
  Ω Ω₀ Ω₁ : Tel Γ

infixl 9 _[_]ᵀˡ
infixl 10 _⁺^
_[_]ᵀˡ : Tel Γ → Sub Δ Γ → Tel Δ
_⁺^ : (γ : Sub Δ Γ) → Sub (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω)

◇ [ γ ]ᵀˡ = ◇
(Ω ▹ A) [ γ ]ᵀˡ = Ω [ γ ]ᵀˡ ▹ A [ γ ⁺^ ]ᵀ

_⁺^ {Ω = ◇} γ = γ
_⁺^ {Ω = Ω ▹ A} γ = γ ⁺^ ⁺

infixl 9 _[_]ᵀˡ*
infixl 10 _⁺^*
_[_]ᵀˡ* : Tel Γ → Sub* Δ Γ → Tel Δ
_⁺^* : (γ* : Sub* Δ Γ) → Sub* (Δ ++ Ω [ γ* ]ᵀˡ*) (Γ ++ Ω)

◇ [ γ* ]ᵀˡ* = ◇
(Ω ▹ A) [ γ* ]ᵀˡ* = Ω [ γ* ]ᵀˡ* ▹ A [ γ* ⁺^* ]ᵀ*

_⁺^* {Ω = ◇} γ* = γ*
_⁺^* {Ω = Ω ▹ A} γ* = γ* ⁺^* ⁺*

opaque
  unfolding coe

  ap-++ : Ω₀ ≡ Ω₁ → (Γ ++ Ω₀) ≡ (Γ ++ Ω₁)
  ap-++ refl = refl

  ap-▹ᵀˡ :
    (Ω₀₁ : Ω₀ ≡ Ω₁) → A₀ ≡[ ap-Ty (ap-++ Ω₀₁) ] A₁ → (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁)
  ap-▹ᵀˡ refl refl = refl

  ▹ᵀˡ-inj-Ω : (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁) → Ω₀ ≡ Ω₁
  ▹ᵀˡ-inj-Ω refl = refl

  ▹ᵀˡ-inj-i :
    {A₀ : Ty (Γ ++ Ω₀) i₀} {A₁ : Ty (Γ ++ Ω₁) i₁} →
    (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁) → i₀ ≡ i₁
  ▹ᵀˡ-inj-i refl = refl

  ▹ᵀˡ-inj-A :
    (e : (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁)) →
    A₀ ≡[ ap-Ty₂ (ap-++ (▹ᵀˡ-inj-Ω e)) (▹ᵀˡ-inj-i e) ] A₁
  ▹ᵀˡ-inj-A refl = refl
