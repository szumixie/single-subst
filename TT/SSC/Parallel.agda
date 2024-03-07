{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --hidden-argument-puns #-}

module TT.SSC.Parallel where

open import TT.Lib
open import TT.SSC.Syntax
open import TT.SSC.Path
open import TT.SSC.Tel
open import TT.SSC.Lift

private variable
  i : ℕ
  Γ Δ Θ : Con
  A B : Ty Γ i
  a a₀ a₁ b : Tm Γ A

data Tms : Con → Con → Set

⌞_⌟ : Tms Δ Γ → Sub* Δ Γ

infixl 4 _,_
data Tms where
  ε : Tms Γ ◇
  _,_ : (γᵗ : Tms Δ Γ) → Tm Δ (A [ ⌞ γᵗ ⌟ ]ᵀ*) → Tms Δ (Γ ▹ A)

⌞ ε ⌟ = ε*
⌞ γᵗ , a ⌟ = ⌞ γᵗ ⌟ ,* a

_[_]ᵀᵗ : Ty Γ i → Tms Δ Γ → Ty Δ i
A [ γᵗ ]ᵀᵗ = A [ ⌞ γᵗ ⌟ ]ᵀ*

_[_]ᵗᵗ : Tm Γ A → (γᵗ : Tms Δ Γ) → Tm Δ (A [ γᵗ ]ᵀᵗ)
a [ γᵗ ]ᵗᵗ = a [ ⌞ γᵗ ⌟ ]ᵗ*

private variable
  γᵗ γᵗ₀ γᵗ₁ δᵗ θᵗ : Tms Δ Γ

opaque
  unfolding coe

  ap-[]ᵀᵗ : γᵗ₀ ≡ γᵗ₁ → A [ γᵗ₀ ]ᵀᵗ ≡ A [ γᵗ₁ ]ᵀᵗ
  ap-[]ᵀᵗ refl = refl

  ap-, :
    {A : Ty Γ i} {a₀ : Tm Δ (A [ γᵗ₀ ]ᵀᵗ)} {a₁ : Tm Δ (A [ γᵗ₁ ]ᵀᵗ)}
    (γᵗ₀₁ : γᵗ₀ ≡ γᵗ₁) →
    a₀ ≡[ ap-Tm (ap-[]ᵀᵗ γᵗ₀₁) ] a₁ →
    (γᵗ₀ , a₀) ≡ (γᵗ₁ , a₁)
  ap-, refl refl = refl

infixl 9 _∘ᵗ_
_∘ᵗ_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
[]ᵀ-∘ᵗ : (γᵗ : Tms Δ Γ) → A [ γᵗ ∘ᵗ δᵗ ]ᵀᵗ ≡ A [ γᵗ ]ᵀᵗ [ δᵗ ]ᵀᵗ
[]ᵗ-∘ᵗ :
  (γᵗ : Tms Δ Γ) → a [ γᵗ ∘ᵗ δᵗ ]ᵗᵗ ≡[ ap-Tm ([]ᵀ-∘ᵗ γᵗ) ] a [ γᵗ ]ᵗᵗ [ δᵗ ]ᵗᵗ

ε ∘ᵗ δ = ε
(γᵗ , a) ∘ᵗ δᵗ = γᵗ ∘ᵗ δᵗ , coe (ap-Tm (sym ([]ᵀ-∘ᵗ γᵗ))) (a [ δᵗ ]ᵗᵗ)

[]ᵀ-∘ᵗ {δᵗ} ε = sym (ε-[]ᵀ* ⌞ δᵗ ⌟)
[]ᵀ-∘ᵗ {δᵗ} (γᵗ , a) =
  ap-[]ᵀ₃
    (ap-▹ᵣ ([]ᵀ-∘ᵗ γᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘ᵗ δᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌞ δᵗ ⌟)
      ([]ᵀ-∘ᵗ γᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ)
      (◇ ▹ _))
    (apᵈ-⟨⟩ ([]ᵀ-∘ᵗ γᵗ) (splitl reflᵈ)) ∙
  sym (⟨⟩-[]ᵀ* ⌞ δᵗ ⌟)

[]ᵗ-∘ᵗ {δᵗ} ε = symᵈ (ε-[]ᵗ* ⌞ δᵗ ⌟)
[]ᵗ-∘ᵗ {δᵗ} (γᵗ , a) =
  apᵈ-[]ᵗ₄
    (ap-▹ᵣ ([]ᵀ-∘ᵗ γᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘ᵗ δᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌞ δᵗ ⌟)
      ([]ᵀ-∘ᵗ γᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ)
      (◇ ▹ _))
    ([]ᵛ→⁺^ᵗ
      ⌞ γᵗ ∘ᵗ δᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌞ δᵗ ⌟)
      ([]ᵀ-∘ᵗ γᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ)
      (◇ ▹ _))
    (apᵈ-⟨⟩ ([]ᵀ-∘ᵗ γᵗ) (splitl reflᵈ)) ∙ᵈ
  symᵈ (⟨⟩-[]ᵗ* ⌞ δᵗ ⌟)

assocᵗ : γᵗ ∘ᵗ (δᵗ ∘ᵗ θᵗ) ≡ (γᵗ ∘ᵗ δᵗ) ∘ᵗ θᵗ
assocᵗ {γᵗ = ε} = refl
assocᵗ {γᵗ = γᵗ , a} {δᵗ} {θᵗ} =
  ap-, assocᵗ (splitlr ([]ᵗ-∘ᵗ δᵗ ∙ᵈ apᵈ-[]ᵗ* (sym ([]ᵀ-∘ᵗ γᵗ)) refl ⌞ θᵗ ⌟))

infixl 9 _∘pᵗ
_∘pᵗ : Tms Δ Γ → Tms (Δ ▹ A) Γ
[]ᵀ-∘pᵗ : (γᵗ : Tms Δ Γ) → B [ γᵗ ∘pᵗ ]ᵀᵗ ≡ B [ γᵗ ]ᵀᵗ [ p ]ᵀ ∈ Ty (Δ ▹ A) i
[]ᵗ-∘pᵗ :
  (γᵗ : Tms Δ Γ) →
  b [ γᵗ ∘pᵗ ]ᵗᵗ ≡[ ap-Tm ([]ᵀ-∘pᵗ γᵗ) ]
  b [ γᵗ ]ᵗᵗ [ p ]ᵗ ∈ Tm (Δ ▹ A) (B [ γᵗ ]ᵀᵗ [ p ]ᵀ)

ε ∘pᵗ = ε
(γᵗ , b) ∘pᵗ = γᵗ ∘pᵗ , coe (ap-Tm (sym ([]ᵀ-∘pᵗ γᵗ))) (b [ p ]ᵗ)

[]ᵀ-∘pᵗ ε = sym ε*-[]ᵀ
[]ᵀ-∘pᵗ (γᵗ , a) =
  ap-[]ᵀ₃
    (ap-▹ᵣ ([]ᵀ-∘pᵗ γᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘pᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌜ p ⌝)
      ([]ᵀ-∘pᵗ γᵗ)
      (λ _ → []ᵗ-∘pᵗ γᵗ)
      (◇ ▹ _))
    (apᵈ-⟨⟩ ([]ᵀ-∘pᵗ γᵗ) (splitl reflᵈ)) ∙
  sym ⟨⟩-[]ᵀ

[]ᵗ-∘pᵗ ε = symᵈ ε*-[]ᵗ
[]ᵗ-∘pᵗ (γᵗ , a) =
  apᵈ-[]ᵗ₄
    (ap-▹ᵣ ([]ᵀ-∘pᵗ γᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘pᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌜ p ⌝)
      ([]ᵀ-∘pᵗ γᵗ)
      (λ _ → []ᵗ-∘pᵗ γᵗ)
      (◇ ▹ _))
    ([]ᵛ→⁺^ᵗ
      ⌞ γᵗ ∘pᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌜ p ⌝)
      ([]ᵀ-∘pᵗ γᵗ)
      (λ _ → []ᵗ-∘pᵗ γᵗ)
      (◇ ▹ _))
    (apᵈ-⟨⟩ ([]ᵀ-∘pᵗ γᵗ) (splitl reflᵈ)) ∙ᵈ
  symᵈ (⟨⟩-[]ᵗ-⁺^ ◇)

∘p-,ᵗ : γᵗ ∘pᵗ ∘ᵗ (δᵗ , a) ≡ γᵗ ∘ᵗ δᵗ
∘p-,ᵗ {γᵗ = ε} = refl
∘p-,ᵗ {γᵗ = γᵗ , b} {δᵗ} {a} =
  ap-,
    ∘p-,ᵗ
    (splitlr (apᵈ-[]ᵗ* ([]ᵀ-∘pᵗ γᵗ) (splitl reflᵈ) ⌞ δᵗ , a ⌟ ∙ᵈ ▹-β₁ᵗ* ⌞ δᵗ ⌟))

idᵗ : Tms Γ Γ
[]ᵀ-idᵗ : {A : Ty Γ i} → A [ idᵗ ]ᵀᵗ ≡ A
[]ᵗ-idᵗ : {a : Tm Γ A} → a [ idᵗ ]ᵗᵗ ≡[ ap-Tm []ᵀ-idᵗ ] a

idᵗ {Γ = ◇} = ε
idᵗ {Γ = Γ ▹ A} =
  idᵗ ∘pᵗ , coe (ap-Tm (ap-[]ᵀ (sym []ᵀ-idᵗ) ∙ sym ([]ᵀ-∘pᵗ idᵗ))) q

[]ᵀ-idᵗ {Γ = ◇} = refl
[]ᵀ-idᵗ {Γ = Γ ▹ A} =
  ap-[]ᵀ₃
    (ap-▹ᵣ ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ idᵗ ∘pᵗ ⌟
      ⌜ p ⌝
      ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ)
      (λ _ → []ᵗ-∘pᵗ idᵗ ∙ᵈ apᵈ-[]ᵗ []ᵀ-idᵗ []ᵗ-idᵗ)
      (◇ ▹ A))
    (apᵈ-⟨⟩ ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ) (splitl reflᵈ)) ∙
  sym ▹-ηᵀ

[]ᵗ-idᵗ {Γ = ◇} = reflᵈ
[]ᵗ-idᵗ {Γ = Γ ▹ A} =
  apᵈ-[]ᵗ₄
    (ap-▹ᵣ ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ idᵗ ∘pᵗ ⌟
      ⌜ p ⌝
      ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ)
      (λ _ → []ᵗ-∘pᵗ idᵗ ∙ᵈ apᵈ-[]ᵗ []ᵀ-idᵗ []ᵗ-idᵗ)
      (◇ ▹ A))
    ([]ᵛ→⁺^ᵗ
      ⌞ idᵗ ∘pᵗ ⌟
      ⌜ p ⌝
      ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ)
      (λ _ → []ᵗ-∘pᵗ idᵗ ∙ᵈ apᵈ-[]ᵗ []ᵀ-idᵗ []ᵗ-idᵗ)
      (◇ ▹ A))
    (apᵈ-⟨⟩ ([]ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ) (splitl reflᵈ)) ∙ᵈ
  symᵈ (▹-ηᵗ-⁺^ ◇)

pᵗ : Tms (Γ ▹ A) Γ
pᵗ = idᵗ ∘pᵗ

[]ᵀ-pᵗ : B [ pᵗ ]ᵀᵗ ≡ B [ p ]ᵀ ∈ Ty (Γ ▹ A) i
[]ᵀ-pᵗ = []ᵀ-∘pᵗ idᵗ ∙ ap-[]ᵀ []ᵀ-idᵗ

idrᵗ : γᵗ ∘ᵗ idᵗ ≡ γᵗ
idrᵗ {γᵗ = ε} = refl
idrᵗ {γᵗ = γᵗ , a} = ap-, idrᵗ (splitl []ᵗ-idᵗ)

idlᵗ : idᵗ ∘ᵗ γᵗ ≡ γᵗ
idlᵗ {γᵗ = ε} = refl
idlᵗ {γᵗ = γᵗ , a} =
  ap-,
    (∘p-,ᵗ ∙ idlᵗ)
    (splitl
      ( apᵈ-[]ᵗ* []ᵀ-pᵗ (splitl reflᵈ) ⌞ γᵗ , a ⌟ ∙ᵈ
        ▹-β₂* ⌞ γᵗ ⌟))

qᵗ : Tm (Γ ▹ A) (A [ pᵗ ]ᵀᵗ)
qᵗ = coe (ap-Tm (ap-[]ᵀ (sym []ᵀ-idᵗ) ∙ sym ([]ᵀ-∘pᵗ idᵗ))) q

▹-β₁ᵗ : (γᵗ : Tms Δ Γ) {a : Tm Δ (A [ γᵗ ]ᵀᵗ)} → pᵗ ∘ᵗ (γᵗ , a) ≡ γᵗ
▹-β₁ᵗ γᵗ = ∘p-,ᵗ ∙ idlᵗ

▹-β₂ᵗ :
  (γᵗ : Tms Δ Γ) {A : Ty Γ i} {a : Tm Δ (A [ γᵗ ]ᵀᵗ)} →
  qᵗ [ γᵗ , a ]ᵗᵗ
    ≡[ ap-Tm (sym ([]ᵀ-∘ᵗ {δᵗ = γᵗ , a} pᵗ) ∙ ap-[]ᵀᵗ (▹-β₁ᵗ γᵗ)) ]
  a
▹-β₂ᵗ γᵗ {a} = apᵈ-[]ᵗ* []ᵀ-pᵗ (splitl reflᵈ) ⌞ γᵗ , a ⌟ ∙ᵈ ▹-β₂* ⌞ γᵗ ⌟

,∘ : {γᵗ : Tms Δ Γ}{a : Tm Δ (A [ γᵗ ]ᵀᵗ)} → (_,_ γᵗ a) ∘ᵗ δᵗ ≡ (γᵗ ∘ᵗ δᵗ , coe (ap-Tm (sym ([]ᵀ-∘ᵗ γᵗ))) (a [ δᵗ ]ᵗᵗ))
,∘ = refl

▹-ηᵗ : (pᵗ , qᵗ) ≡ idᵗ {Γ ▹ A}
▹-ηᵗ = refl
