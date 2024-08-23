{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --hidden-argument-puns
#-}

module TT.SSC.Parallel where

open import TT.Lib
open import TT.SSC.Syntax
open import TT.SSC.Path
open import TT.SSC.Tel
open import TT.SSC.Lift

private variable
  i : ℕ
  Γ Δ Θ : Con
  A A₀ A₁ B : Ty Γ i
  a a₀ a₁ b f α : Tm Γ A

data Tms : Con → Con → Set

⌞_⌟ : Tms Δ Γ → Sub* Δ Γ

infixl 4 _,_
data Tms where
  ε : Tms Γ ◇
  _,_ : (γᵗ : Tms Δ Γ) → Tm Δ (A [ ⌞ γᵗ ⌟ ]ᵀ*) → Tms Δ (Γ ▹ A)

⌞ ε ⌟ = ε*
⌞ γᵗ , a ⌟ = ⌞ γᵗ ⌟ ,* a

infixl 9 _[_]ᵀᵗ
_[_]ᵀᵗ : Ty Γ i → Tms Δ Γ → Ty Δ i
A [ γᵗ ]ᵀᵗ = A [ ⌞ γᵗ ⌟ ]ᵀ*

infixl 9 _[_]ᵗᵗ
_[_]ᵗᵗ : Tm Γ A → (γᵗ : Tms Δ Γ) → Tm Δ (A [ γᵗ ]ᵀᵗ)
a [ γᵗ ]ᵗᵗ = a [ ⌞ γᵗ ⌟ ]ᵗ*

private variable
  γᵗ γᵗ₀ γᵗ₁ δᵗ δᵗ₀ δᵗ₁ θᵗ : Tms Δ Γ

opaque
  unfolding coe

  ap-[]ᵀᵗ : A₀ ≡ A₁ → (γᵗ : Tms Δ Γ) → A₀ [ γᵗ ]ᵀᵗ ≡ A₁ [ γᵗ ]ᵀᵗ
  ap-[]ᵀᵗ refl _ = refl

  ap-[]ᵀᵗᵣ : γᵗ₀ ≡ γᵗ₁ → A [ γᵗ₀ ]ᵀᵗ ≡ A [ γᵗ₁ ]ᵀᵗ
  ap-[]ᵀᵗᵣ refl = refl

  ap-, :
    {A : Ty Γ i} {a₀ : Tm Δ (A [ γᵗ₀ ]ᵀᵗ)} {a₁ : Tm Δ (A [ γᵗ₁ ]ᵀᵗ)}
    (γᵗ₀₁ : γᵗ₀ ≡ γᵗ₁) →
    a₀ ≡[ ap-Tm (ap-[]ᵀᵗᵣ γᵗ₀₁) ] a₁ →
    (γᵗ₀ , a₀) ≡ (γᵗ₁ , a₁)
  ap-, refl refl = refl

infixl 9 _∘ᵗ_
_∘ᵗ_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
[]ᵀ-∘ᵗ : (γᵗ : Tms Δ Γ) (δᵗ : Tms Θ Δ) → A [ γᵗ ∘ᵗ δᵗ ]ᵀᵗ ≡ A [ γᵗ ]ᵀᵗ [ δᵗ ]ᵀᵗ
[]ᵗ-∘ᵗ :
  (γᵗ : Tms Δ Γ) (δᵗ : Tms Θ Δ) →
  a [ γᵗ ∘ᵗ δᵗ ]ᵗᵗ ≡[ ap-Tm ([]ᵀ-∘ᵗ γᵗ δᵗ) ] a [ γᵗ ]ᵗᵗ [ δᵗ ]ᵗᵗ

ε ∘ᵗ δ = ε
(γᵗ , a) ∘ᵗ δᵗ = γᵗ ∘ᵗ δᵗ , coe (ap-Tm (sym ([]ᵀ-∘ᵗ γᵗ δᵗ))) (a [ δᵗ ]ᵗᵗ)

[]ᵀ-∘ᵗ ε δᵗ = sym (ε-[]ᵀ* ⌞ δᵗ ⌟)
[]ᵀ-∘ᵗ (γᵗ , a) δᵗ =
  ap-[]ᵀ₃
    (ap-▹ᵣ ([]ᵀ-∘ᵗ γᵗ δᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘ᵗ δᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌞ δᵗ ⌟)
      ([]ᵀ-∘ᵗ γᵗ δᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ δᵗ)
      (◇ ▹ _))
    (apᵈ-⟨⟩ ([]ᵀ-∘ᵗ γᵗ δᵗ) (splitl reflᵈ)) ∙
  sym (⟨⟩-[]ᵀ* ⌞ δᵗ ⌟)

[]ᵗ-∘ᵗ ε δᵗ = symᵈ (ε-[]ᵗ* ⌞ δᵗ ⌟)
[]ᵗ-∘ᵗ (γᵗ , a) δᵗ =
  apᵈ-[]ᵗ₄
    (ap-▹ᵣ ([]ᵀ-∘ᵗ γᵗ δᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘ᵗ δᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌞ δᵗ ⌟)
      ([]ᵀ-∘ᵗ γᵗ δᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ δᵗ)
      (◇ ▹ _))
    ([]ᵛ→⁺^ᵗ
      ⌞ γᵗ ∘ᵗ δᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌞ δᵗ ⌟)
      ([]ᵀ-∘ᵗ γᵗ δᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ δᵗ)
      (◇ ▹ _))
    (apᵈ-⟨⟩ ([]ᵀ-∘ᵗ γᵗ δᵗ) (splitl reflᵈ)) ∙ᵈ
  symᵈ (⟨⟩-[]ᵗ* ⌞ δᵗ ⌟)

assocᵗ : γᵗ ∘ᵗ (δᵗ ∘ᵗ θᵗ) ≡ (γᵗ ∘ᵗ δᵗ) ∘ᵗ θᵗ
assocᵗ {γᵗ = ε} = refl
assocᵗ {γᵗ = γᵗ , a} {δᵗ} {θᵗ} =
  ap-,
    assocᵗ
    (splitlr ([]ᵗ-∘ᵗ δᵗ θᵗ ∙ᵈ apᵈ-[]ᵗ* (sym ([]ᵀ-∘ᵗ γᵗ δᵗ)) refl ⌞ θᵗ ⌟))

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

[]ᵗ-pᵗ : b [ pᵗ ]ᵗᵗ ≡[ ap-Tm []ᵀ-pᵗ ] b [ p ]ᵗ ∈ Tm (Γ ▹ A) (B [ p ]ᵀ)
[]ᵗ-pᵗ = []ᵗ-∘pᵗ idᵗ ∙ᵈ apᵈ-[]ᵗ []ᵀ-idᵗ []ᵗ-idᵗ

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

,-∘ᵗ :
  {γᵗ : Tms Δ Γ} {a : Tm Δ (A [ γᵗ ]ᵀᵗ)} →
  (γᵗ , a) ∘ᵗ δᵗ ≡ (γᵗ ∘ᵗ δᵗ , coe (ap-Tm (sym ([]ᵀ-∘ᵗ γᵗ δᵗ))) (a [ δᵗ ]ᵗᵗ))
,-∘ᵗ = refl

▹-β₁ᵗ : (γᵗ : Tms Δ Γ) {a : Tm Δ (A [ γᵗ ]ᵀᵗ)} → pᵗ ∘ᵗ (γᵗ , a) ≡ γᵗ
▹-β₁ᵗ γᵗ = ∘p-,ᵗ ∙ idlᵗ

▹-β₂ᵗ :
  (γᵗ : Tms Δ Γ) {A : Ty Γ i} {a : Tm Δ (A [ γᵗ ]ᵀᵗ)} →
  qᵗ [ γᵗ , a ]ᵗᵗ
    ≡[ ap-Tm (sym ([]ᵀ-∘ᵗ pᵗ (γᵗ , a)) ∙ ap-[]ᵀᵗᵣ (▹-β₁ᵗ γᵗ)) ]
  a
▹-β₂ᵗ γᵗ {a} = apᵈ-[]ᵗ* []ᵀ-pᵗ (splitl reflᵈ) ⌞ γᵗ , a ⌟ ∙ᵈ ▹-β₂* ⌞ γᵗ ⌟

▹-ηᵗ : idᵗ ≡ (pᵗ , qᵗ) ∈ Tms (Γ ▹ A) (Γ ▹ A)
▹-ηᵗ = refl

opaque
  unfolding coe

  ap-∘ᵗᵣ : (δᵗ₀₁ : δᵗ₀ ≡ δᵗ₁) → γᵗ ∘ᵗ δᵗ₀ ≡ γᵗ ∘ᵗ δᵗ₁
  ap-∘ᵗᵣ refl = refl

  apᵈ-[]ᵗᵗ :
    (A₀₁ : A₀ ≡ A₁) → a₀ ≡[ ap-Tm A₀₁ ] a₁ → (γᵗ : Tms Δ Γ) →
    a₀ [ γᵗ ]ᵗᵗ ≡[ ap-Tm (ap-[]ᵀᵗ A₀₁ γᵗ) ] a₁ [ γᵗ ]ᵗᵗ
  apᵈ-[]ᵗᵗ refl refl _ = refl

infixl 10 _⁺ᵗ
_⁺ᵗ : (γᵗ : Tms Δ Γ) → Tms (Δ ▹ A [ γᵗ ]ᵀᵗ) (Γ ▹ A)
γᵗ ⁺ᵗ = γᵗ ∘ᵗ pᵗ , coe (ap-Tm (sym ([]ᵀ-∘ᵗ γᵗ pᵗ))) qᵗ

[]ᵀ-⁺ᵗ :
  (γᵗ : Tms Δ Γ) → B [ γᵗ ⁺ᵗ ]ᵀᵗ ≡ B [ ⌞ γᵗ ⌟ ⁺* ]ᵀ* ∈ Ty (Δ ▹ A [ γᵗ ]ᵀᵗ) i
[]ᵀ-⁺ᵗ {A} γᵗ =
  ap-[]ᵀ₃
    (ap-▹ᵣ ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘ᵗ pᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌜ p ⌝)
      ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ pᵗ ∙ᵈ []ᵗ-pᵗ)
      (◇ ▹ A))
    (apᵈ-⟨⟩ ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ) (splitl (splitl reflᵈ))) ∙
  sym ▹-ηᵀ

[]ᵗ-⁺ᵗ :
  (γᵗ : Tms Δ Γ) →
  b [ γᵗ ⁺ᵗ ]ᵗᵗ ≡[ ap-Tm ([]ᵀ-⁺ᵗ γᵗ) ]
  b [ ⌞ γᵗ ⌟ ⁺* ]ᵗ* ∈ Tm (Δ ▹ A [ γᵗ ]ᵀᵗ) (B [ ⌞ γᵗ ⌟ ⁺* ]ᵀ*)
[]ᵗ-⁺ᵗ {A} γᵗ =
  apᵈ-[]ᵗ₄
    (ap-▹ᵣ ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ))
    ([]ᵛ→⁺^ᵀ
      ⌞ γᵗ ∘ᵗ pᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌜ p ⌝)
      ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ pᵗ ∙ᵈ []ᵗ-pᵗ)
      (◇ ▹ A))
    ([]ᵛ→⁺^ᵗ
      ⌞ γᵗ ∘ᵗ pᵗ ⌟
      (⌞ γᵗ ⌟ ∘ ⌜ p ⌝)
      ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ)
      (λ _ → []ᵗ-∘ᵗ γᵗ pᵗ ∙ᵈ []ᵗ-pᵗ)
      (◇ ▹ A))
    (apᵈ-⟨⟩ ([]ᵀ-∘ᵗ γᵗ pᵗ ∙ []ᵀ-pᵗ) (splitl (splitl reflᵈ))) ∙ᵈ
  symᵈ (▹-ηᵗ-⁺^ ◇)

⟨_⟩ᵗ : Tm Γ A → Tms Γ (Γ ▹ A)
⟨ a ⟩ᵗ = idᵗ , coe (ap-Tm (sym []ᵀ-idᵗ)) a

[]ᵀ-⟨⟩ᵗ : {a : Tm Γ A} → B [ ⟨ a ⟩ᵗ ]ᵀᵗ ≡ B [ ⟨ a ⟩ ]ᵀ
[]ᵀ-⟨⟩ᵗ {A} =
  ap-[]ᵀ₃
    (ap-▹ᵣ []ᵀ-idᵗ)
    ([]ᵛ→⁺^ᵀ ⌞ idᵗ ⌟ id []ᵀ-idᵗ (λ _ → []ᵗ-idᵗ) (◇ ▹ A))
    (apᵈ-⟨⟩ []ᵀ-idᵗ (splitl reflᵈ))

[]ᵗ-⟨⟩ᵗ : {a : Tm Γ A} → b [ ⟨ a ⟩ᵗ ]ᵗᵗ ≡[ ap-Tm []ᵀ-⟨⟩ᵗ ] b [ ⟨ a ⟩ ]ᵗ
[]ᵗ-⟨⟩ᵗ {A} =
  apᵈ-[]ᵗ₄
    (ap-▹ᵣ []ᵀ-idᵗ)
    ([]ᵛ→⁺^ᵀ ⌞ idᵗ ⌟ id []ᵀ-idᵗ (λ _ → []ᵗ-idᵗ) (◇ ▹ A))
    ([]ᵛ→⁺^ᵗ ⌞ idᵗ ⌟ id []ᵀ-idᵗ (λ _ → []ᵗ-idᵗ) (◇ ▹ A))
    (apᵈ-⟨⟩ []ᵀ-idᵗ (splitl reflᵈ))

⟨⟩-∘ᵗ : (γᵗ : Tms Δ Γ) → ⟨ a ⟩ᵗ ∘ᵗ γᵗ ≡ γᵗ ⁺ᵗ ∘ᵗ ⟨ a [ γᵗ ]ᵗᵗ ⟩ᵗ
⟨⟩-∘ᵗ {a} γᵗ =
  ap-,
    (idlᵗ ∙ sym idrᵗ ∙ ap-∘ᵗᵣ (sym (▹-β₁ᵗ idᵗ)) ∙ assocᵗ)
    ( splitlr (apᵈ-[]ᵗᵗ []ᵀ-idᵗ (splitl reflᵈ) γᵗ ∙ᵈ
      symᵈ (merger (▹-β₂ᵗ idᵗ)) ∙ᵈ
      apᵈ-[]ᵗᵗ (sym ([]ᵀ-∘ᵗ γᵗ pᵗ)) refl ⟨ a [ γᵗ ]ᵗᵗ ⟩ᵗ))

▹-η′ᵗ : idᵗ ≡ pᵗ ⁺ᵗ ∘ᵗ ⟨ qᵗ ⟩ᵗ ∈ Tms (Γ ▹ A) (Γ ▹ A)
▹-η′ᵗ =
  ap-,
    (sym idrᵗ ∙ ap-∘ᵗᵣ (sym (▹-β₁ᵗ idᵗ)) ∙ assocᵗ)
    (splitr
      (symᵈ (merger (▹-β₂ᵗ idᵗ)) ∙ᵈ apᵈ-[]ᵗᵗ (sym ([]ᵀ-∘ᵗ pᵗ pᵗ)) refl ⟨ qᵗ ⟩ᵗ))

U-[]ᵗ : (γᵗ : Tms Δ Γ) → U i [ γᵗ ]ᵀᵗ ≡ U i
U-[]ᵗ γᵗ = U-[]* ⌞ γᵗ ⌟

El-[]ᵗ :
  (γᵗ : Tms Δ Γ) → El α [ γᵗ ]ᵀᵗ ≡ El (coe (ap-Tm (U-[]ᵗ γᵗ)) (α [ γᵗ ]ᵗᵗ))
El-[]ᵗ γᵗ = El-[]* ⌞ γᵗ ⌟

c-[]ᵗ : (γᵗ : Tms Δ Γ) → c A [ γᵗ ]ᵗᵗ ≡[ ap-Tm (U-[]ᵗ γᵗ) ] c (A [ γᵗ ]ᵀᵗ)
c-[]ᵗ γᵗ = c-[]* ⌞ γᵗ ⌟

Π-[]ᵗ : (γᵗ : Tms Δ Γ) → Π A B [ γᵗ ]ᵀᵗ ≡ Π (A [ γᵗ ]ᵀᵗ) (B [ γᵗ ⁺ᵗ ]ᵀᵗ)
Π-[]ᵗ γᵗ = Π-[]* ⌞ γᵗ ⌟ ∙ ap-Π (sym ([]ᵀ-⁺ᵗ γᵗ))

appᵗ : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ᵗ ]ᵀᵗ)
appᵗ f a = coe (ap-Tm (sym []ᵀ-⟨⟩ᵗ)) (app f a)

app-[]ᵗ :
  {B : Ty (Γ ▹ A) i} {f : Tm Γ (Π A B)} (γᵗ : Tms Δ Γ) →
  appᵗ f a [ γᵗ ]ᵗᵗ
    ≡[
      ap-Tm
        ( sym ([]ᵀ-∘ᵗ ⟨ a ⟩ᵗ γᵗ) ∙
          ap-[]ᵀᵗᵣ (⟨⟩-∘ᵗ γᵗ) ∙ []ᵀ-∘ᵗ (γᵗ ⁺ᵗ) ⟨ a [ γᵗ ]ᵗᵗ ⟩ᵗ) ]
  appᵗ (coe (ap-Tm (Π-[]ᵗ γᵗ)) (f [ γᵗ ]ᵗᵗ)) (a [ γᵗ ]ᵗᵗ)
app-[]ᵗ γᵗ =
  splitr
    ( apᵈ-[]ᵗᵗ []ᵀ-⟨⟩ᵗ (splitl reflᵈ) γᵗ ∙ᵈ
      app-[]* ⌞ γᵗ ⌟ ∙ᵈ
      apᵈ-app refl reflᵈ (dep (sym ([]ᵀ-⁺ᵗ γᵗ))) (splitlr reflᵈ) reflᵈ)

lam-[]ᵗ :
  (γᵗ : Tms Δ Γ) → lam b [ γᵗ ]ᵗᵗ ≡[ ap-Tm (Π-[]ᵗ γᵗ) ] lam (b [ γᵗ ⁺ᵗ ]ᵗᵗ)
lam-[]ᵗ γᵗ = lam-[]* ⌞ γᵗ ⌟ ∙ᵈ apᵈ-lam (sym ([]ᵀ-⁺ᵗ γᵗ)) (symᵈ ([]ᵗ-⁺ᵗ γᵗ))

Π-βᵗ : appᵗ (lam b) a ≡ b [ ⟨ a ⟩ᵗ ]ᵗᵗ
Π-βᵗ = dep Π-β ∙ᵈ symᵈ []ᵗ-⟨⟩ᵗ

Π-ηᵗ :
  {B : Ty (Γ ▹ A) i} {f : Tm Γ (Π A B)} →
  f ≡[ ap-Tm (ap-Π (sym []ᵀ-idᵗ ∙ ap-[]ᵀᵗᵣ ▹-η′ᵗ ∙ []ᵀ-∘ᵗ (pᵗ ⁺ᵗ) ⟨ qᵗ ⟩ᵗ)) ]
  lam (appᵗ (coe (ap-Tm (Π-[]ᵗ pᵗ)) (f [ pᵗ ]ᵗᵗ)) qᵗ)
Π-ηᵗ {A} =
  Π-η ∙ᵈ
  apᵈ-lam
    (ap-[]ᵀ₃
      (ap-▹ᵣ (sym []ᵀ-pᵗ))
      ( []ᵛ→⁺^ᵀ ⌜ p ⌝ ⌞ pᵗ ⌟ (sym []ᵀ-pᵗ) (λ _ → symᵈ []ᵗ-pᵗ) (◇ ▹ A) ∙ᵈ
        dep (sym ([]ᵀ-⁺ᵗ pᵗ)))
      (apᵈ-⟨⟩ (sym []ᵀ-pᵗ) refl) ∙ sym []ᵀ-⟨⟩ᵗ)
    (splitr
      (apᵈ-app
        refl
        (dep (sym []ᵀ-pᵗ))
        ( []ᵛ→⁺^ᵀ ⌜ p ⌝ ⌞ pᵗ ⌟ (sym []ᵀ-pᵗ) (λ _ → symᵈ []ᵗ-pᵗ) (◇ ▹ A) ∙ᵈ
          dep (sym ([]ᵀ-⁺ᵗ pᵗ)))
        (splitlr (symᵈ []ᵗ-pᵗ)) refl))
