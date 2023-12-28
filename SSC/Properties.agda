{-# OPTIONS --with-K --rewriting --postfix-projections #-}

module SSC.Properties where

open import Lib
open import SSC
open import SSC.AlphaNf

private variable
  i j : ℕ
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
  Ω Ω₀ Ω₁ : Tel Γ

cong-▹ :
  {A₀ : Ty (Γ ++ Ω₀) i} {A₁ : Ty (Γ ++ Ω₁) i}
  (Ω₀₁ : Ω₀ ≡ Ω₁) → transpTy (cong (Γ ++_) Ω₀₁) A₀ ≡ A₁ → (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁)
cong-▹ refl refl = refl

infixl 9 _[_]ᵀˡ
infixl 10 _⁺^[_]
_[_]ᵀˡ : Tel Γ → Sub Δ Γ → Tel Δ
_⁺^[_] : (γ : Sub Δ Γ) (Ω : Tel Γ) → Sub (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω)

◇ [ γ ]ᵀˡ = ◇
(Ω ▹ A) [ γ ]ᵀˡ = Ω [ γ ]ᵀˡ ▹ A [ γ ⁺^[ Ω ] ]ᵀ

γ ⁺^[ ◇ ] = γ
γ ⁺^[ Ω ▹ A ] = γ ⁺^[ Ω ] ⁺

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

    infixl 10 _⁺^′[_]
    _⁺^′[_] : (γ : Sub Δ Γ) (Ω : Tel Γ) → Sub (Δ ++ Ω [ γ ]ᵀˡ′) (Γ ++ Ω)
    γ ⁺^′[ Ω ] = []ᵀˡ-⁺^ Ω γ .proj₂

infixl 10 _⁺^ʷ
_⁺^ʷ[_] : Wk Δ Γ γ → (Ω : Tel Γ) → Wk (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω) (γ ⁺^[ Ω ])
γ ⁺^ʷ[ ◇ ] = γ
γ ⁺^ʷ[ Ω ▹ A ] = γ ⁺^ʷ[ Ω ] ⁺
{-
var-p-⁺-⁺^ʷ :
  {A : Ty Γ i} {x : Var (Γ ++ Ω) B} (γʷ : Wk Δ Γ γ) →
  tm[ cong (Δ ▹ A [ γ ]ᵀ ++_) (p-⁺ᵀˡʷ γʷ) , (p-⁺ᵀ-⁺^ʷ γʷ) ]
    (var x [ p {A = A} ⁺^[ Ω ] ]ᵗ [ γ ⁺ ⁺^[ Ω [ p ]ᵀˡ ] ]ᵗ) ≡
  (Tm
    (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ)
    (B [ γ ⁺^[ Ω ] ]ᵀ [ p ⁺^[ Ω [ γ ]ᵀˡ ] ]ᵀ)
    ∋ var x [ γ ⁺^[ Ω ] ]ᵗ [ p ⁺^[ Ω [ γ ]ᵀˡ ] ]ᵗ)
var-p-⁺-⁺^ʷ = {!   !}
-}
module p-⁺ʷ where
  open NfModel

  M : NfModel _ _
  M .NTyᴹ Γ₀ j B =
    ∀ {i Γ} {A : Ty Γ i} {Ω} →
    (p-⁺ᵀˡʷ :
      ∀ {Δ γ} → Wk Δ Γ γ →
      Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ (Tel (Δ ▹ A [ γ ]ᵀ) ∋ Ω [ γ ]ᵀˡ [ p ]ᵀˡ)) →
    ∀ {Δ γ} (Γ₌ : Γ₀ ≡ (Γ ++ Ω)) (γʷ : Wk Δ Γ γ) →
    transpTy (cong (Δ ▹ A [ γ ]ᵀ ++_) (p-⁺ᵀˡʷ γʷ))
      (transpTy Γ₌ B [ p ⁺^[ Ω ] ]ᵀ [ γ ⁺ ⁺^[ Ω [ p ]ᵀˡ ] ]ᵀ) ≡
    (Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j
      ∋ transpTy Γ₌ B [ γ ⁺^[ Ω ] ]ᵀ [ p ⁺^[ Ω [ γ ]ᵀˡ ] ]ᵀ)
  M .NTy-propᴹ = {!   !}
  M .NTmᴹ = {!   !}
  M .NTm-propᴹ = {!   !}
  M .varᴺᴹ = {!   !}
  M .Uᴺᴹ = {!   !}
  M .Elᴺᴹ = {!   !}
  M .cᴺᴹ = {!   !}
  M .Πᴺᴹ {A = A} Aᴺᴹ Bᴺᴹ {Ω = Ω} asd refl γʷ = {!   !}
    where
    _ = Bᴺᴹ {Ω = Ω ▹ A} (λ γʷ → cong-▹ (asd γʷ) (Aᴺᴹ asd refl γʷ)) refl γʷ
  M .appᴺᴹ = {!   !}
  M .lamᴺᴹ = {!   !}

  open NfRec M public

p-⁺ᵀˡʷ : Wk Δ Γ γ → Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ (Tel (Δ ▹ A [ γ ]ᵀ) ∋ Ω [ γ ]ᵀˡ [ p ]ᵀˡ)
p-⁺ᵀ-⁺^ʷ :
  {A : Ty Γ i} (γʷ : Wk Δ Γ γ) →
  transpTy (cong (Δ ▹ A [ γ ]ᵀ ++_) (p-⁺ᵀˡʷ γʷ))
    (B [ p ⁺^[ Ω ] ]ᵀ [ γ ⁺ ⁺^[ Ω [ p ]ᵀˡ ] ]ᵀ) ≡
  (Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j
    ∋ B [ γ ⁺^[ Ω ] ]ᵀ [ p ⁺^[ Ω [ γ ]ᵀˡ ] ]ᵀ)

p-⁺ᵀˡʷ {Ω = ◇} γʷ = refl
p-⁺ᵀˡʷ {Ω = Ω ▹ B} γʷ = cong-▹ (p-⁺ᵀˡʷ γʷ) (p-⁺ᵀ-⁺^ʷ γʷ)

p-⁺ᵀ-⁺^ʷ {B = B} γʷ = p-⁺ʷ.⟦_⟧ᵀ (normᵀ B) p-⁺ᵀˡʷ refl γʷ

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
