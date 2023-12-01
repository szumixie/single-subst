{-# OPTIONS
  --with-K --rewriting --postfix-projections --hidden-argument-puns #-}

module STT.SSC.StrictSub where

open import STT.Lib
open import Data.Product
open import Data.Product.Properties
open import STT.SSC
open import STT.SSC.SNf

private variable
  Γ Δ : Con
  γ : Sub Δ Γ
  A B C : Ty
  a b f : Tm Γ A
  x : Var Γ A

module []′ʷ where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ A a _ = ∀ {Δ γ} (γʷ : Wk Δ Γ γ) → Σ[ a′ ∈ Tm Δ A ] a [ γ ] ≡ a′
  M .NTmᴰ-prop {aᴺᴰ₀} {aᴺᴰ₁} =
    funextᵢ
      (funextᵢ
        (funext λ _ → Σ-≡,≡→≡ (sym (aᴺᴰ₀ _ .proj₂) ∙ aᴺᴰ₁ _ .proj₂ , uip _ _)))
  M .varᴺᴰ x γʷ .proj₁ = var (x [ γʷ ]ᵛʷ)
  M .varᴺᴰ x γʷ .proj₂ = var-[]ʷ γʷ
  M .appᴺᴰ fᴺᴰ aᴺᴰ γʷ .proj₁ = app (fᴺᴰ γʷ .proj₁) (aᴺᴰ γʷ .proj₁)
  M .appᴺᴰ fᴺᴰ aᴺᴰ γʷ .proj₂ =
    app-[] ∙ cong₂ app (fᴺᴰ γʷ .proj₂) (aᴺᴰ γʷ .proj₂)
  M .lamᴺᴰ bᴺᴰ γʷ .proj₁ = lam (bᴺᴰ (γʷ ⁺) .proj₁)
  M .lamᴺᴰ bᴺᴰ γʷ .proj₂ = lam-[] ∙ cong lam (bᴺᴰ (γʷ ⁺) .proj₂)

  open NTmInd M public

infixl 9 _[_]′ʷ
_[_]′ʷ : Tm Γ A → Wk Δ Γ γ → Tm Δ A
a [ γʷ ]′ʷ = []′ʷ.⟦ norm a ⟧ γʷ .proj₁

tm-[]′ʷ : (γʷ : Wk Δ Γ γ) → a [ γ ] ≡ a [ γʷ ]′ʷ
tm-[]′ʷ {a} γʷ = []′ʷ.⟦ norm a ⟧ γʷ .proj₂

_[_]ᵛ′ᴺᵗ : Var Γ A → NTSub Δ Γ γ → Tm Δ A
vz [ γᴺᵗ ⁺ ]ᵛ′ᴺᵗ = var vz
vs x [ γᴺᵗ ⁺ ]ᵛ′ᴺᵗ = x [ γᴺᵗ ]ᵛ′ᴺᵗ [ p ]′ʷ
vz [ ⟨_⟩ {a} _ ]ᵛ′ᴺᵗ = a
vs x [ ⟨ a ⟩ ]ᵛ′ᴺᵗ = var x

var-[]′ᴺᵗ : (γᴺᵗ : NTSub Δ Γ γ) → var x [ γ ] ≡ x [ γᴺᵗ ]ᵛ′ᴺᵗ
var-[]′ᴺᵗ {x = vz} (γᴺᵗ ⁺) = vz-⁺
var-[]′ᴺᵗ {x = vs x} (γᴺᵗ ⁺) = vs-⁺ ∙ cong _[ p ] (var-[]′ᴺᵗ γᴺᵗ) ∙ tm-[]′ʷ p
var-[]′ᴺᵗ {x = vz} ⟨ a ⟩ = vz-⟨⟩
var-[]′ᴺᵗ {x = vs x} ⟨ a ⟩ = vs-⟨⟩

module []′ᴺᵗ where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ A a _ = ∀ {Δ γ} (γᴺᵗ : NTSub Δ Γ γ) → Σ[ a′ ∈ Tm Δ A ] a [ γ ] ≡ a′
  M .NTmᴰ-prop {aᴺᴰ₀} {aᴺᴰ₁} =
    funextᵢ
      (funextᵢ
        (funext λ _ → Σ-≡,≡→≡ (sym (aᴺᴰ₀ _ .proj₂) ∙ aᴺᴰ₁ _ .proj₂ , uip _ _)))
  M .varᴺᴰ x γᴺᵗ .proj₁ = x [ γᴺᵗ ]ᵛ′ᴺᵗ
  M .varᴺᴰ x γᴺᵗ .proj₂ = var-[]′ᴺᵗ γᴺᵗ
  M .appᴺᴰ fᴺᴰ aᴺᴰ γᴺᵗ .proj₁ = app (fᴺᴰ γᴺᵗ .proj₁) (aᴺᴰ γᴺᵗ .proj₁)
  M .appᴺᴰ fᴺᴰ aᴺᴰ γᴺᵗ .proj₂ =
    app-[] ∙ cong₂ app (fᴺᴰ γᴺᵗ .proj₂) (aᴺᴰ γᴺᵗ .proj₂)
  M .lamᴺᴰ bᴺᴰ γᴺᵗ .proj₁ = lam (bᴺᴰ (γᴺᵗ ⁺) .proj₁)
  M .lamᴺᴰ bᴺᴰ γᴺᵗ .proj₂ = lam-[] ∙ cong lam (bᴺᴰ (γᴺᵗ ⁺) .proj₂)

  open NTmInd M public

_[_]′ᴺᵗ : Tm Γ A → NTSub Δ Γ γ → Tm Δ A
a [ γᴺᵗ ]′ᴺᵗ = []′ᴺᵗ.⟦ norm a ⟧ γᴺᵗ .proj₁

tm-[]′ᴺᵗ : (γᴺᵗ : NTSub Δ Γ γ) → a [ γ ] ≡ a [ γᴺᵗ ]′ᴺᵗ
tm-[]′ᴺᵗ {a} γᴺᵗ = []′ᴺᵗ.⟦ norm a ⟧ γᴺᵗ .proj₂

infixl 9 _[_]′ᴺ
_[_]′ᴺ : Tm Γ A → NSub Δ Γ γ → Tm Δ A
a [ wk γʷ ]′ᴺ = a [ γʷ ]′ʷ
a [ ntsub γᴺᵗ ]′ᴺ = a [ γᴺᵗ ]′ᴺᵗ

tm-[]′ᴺ : (γᴺ : NSub Δ Γ γ) → a [ γ ] ≡ a [ γᴺ ]′ᴺ
tm-[]′ᴺ (wk γʷ) = tm-[]′ʷ γʷ
tm-[]′ᴺ (ntsub γᴺᵗ) = tm-[]′ᴺᵗ γᴺᵗ

_[_]′ : Tm Γ A → Sub Δ Γ → Tm Δ A
a [ γ ]′ = a [ normˢ γ ]′ᴺ

tm-[]′ : a [ γ ] ≡ a [ γ ]′
tm-[]′ {γ} = tm-[]′ᴺ (normˢ γ)

var-p′ : var x [ p ]′ ≡ (Tm (Γ ▹ A) B ∋ var (vs x))
var-p′ = refl

vz-⟨⟩′ : var vz [ ⟨ a ⟩ ]′ ≡ a
vz-⟨⟩′ = refl

vs-⟨⟩′ : var (vs x) [ ⟨ a ⟩ ]′ ≡ var x
vs-⟨⟩′ = refl

vz-p-⁺′ : var vz [ p ⁺ ]′ ≡ (Tm (Δ ▹ A ▹ B) B ∋ var vz)
vz-p-⁺′ = refl

vz-⟨⟩-⁺′ : var vz [ ⟨ a ⟩ ⁺ ]′ ≡ (Tm (Δ ▹ B) B ∋ var vz)
vz-⟨⟩-⁺′ = refl

vs-p-⁺ : var (vs x) [ p ⁺ ]′ ≡ (Tm (Δ ▹ A ▹ B) C ∋ var x [ p ]′ [ p ]′)
vs-p-⁺ = refl

vs-⟨⟩-⁺ : var (vs x) [ ⟨ a ⟩ ⁺ ]′ ≡ (Tm (Δ ▹ B) C ∋ var x [ ⟨ a ⟩ ]′ [ p ]′)
vs-⟨⟩-⁺ = refl

app-[]-p : app f b [ p ]′ ≡ (Tm (Γ ▹ A) C ∋ app (f [ p ]′) (b [ p ]′))
app-[]-p = refl

app-[]-⟨⟩ : app f b [ ⟨ a ⟩ ]′ ≡ app (f [ ⟨ a ⟩ ]′) (b [ ⟨ a ⟩ ]′)
app-[]-⟨⟩ = refl

lam-[]-p : lam b [ p ]′ ≡ (Tm (Γ ▹ A) (B ⇒ C) ∋ lam (b [ p ⁺ ]′))
lam-[]-p = refl

lam-[]-⟨⟩ : lam b [ ⟨ a ⟩ ]′ ≡ lam (b [ ⟨ a ⟩ ⁺ ]′)
lam-[]-⟨⟩ = refl
