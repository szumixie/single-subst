{-# OPTIONS --with-K --rewriting --postfix-projections #-}

module STT.SSC.SNf where

open import STT.Lib
open import STT.SSC

private variable
  Γ Δ : Con
  γ : Sub Δ Γ
  A B : Ty
  a a₀ a₁ b f : Tm Γ A
  x : Var Γ A

postulate
  NTm : (Γ : Con) (A : Ty) → Tm Γ A → Set
  NTm-prop : {aᴺ₀ aᴺ₁ : NTm Γ A a} → aᴺ₀ ≡ aᴺ₁
  varᴺ : (x : Var Γ A) → NTm Γ A (var x)

  appᴺ : NTm Γ (A ⇒ B) f → NTm Γ A a → NTm Γ B (app f a)
  lamᴺ : NTm (Γ ▹ A) B b → NTm Γ (A ⇒ B) (lam b)

ntm[_] : a₀ ≡ a₁ → NTm Γ A a₀ → NTm Γ A a₁
ntm[ refl ] aᴺ = aᴺ

private variable
  aᴺ bᴺ fᴺ : NTm Γ A a

record NTmDModel ℓ : Set (suc ℓ) where
  no-eta-equality
  field
    NTmᴰ : (Γ : Con) (A : Ty) (a : Tm Γ A) → NTm Γ A a → Set ℓ
    NTmᴰ-prop : {aᴺᴰ₀ aᴺᴰ₁ : NTmᴰ Γ A a aᴺ} → aᴺᴰ₀ ≡ aᴺᴰ₁
    varᴺᴰ : (x : Var Γ A) → NTmᴰ Γ A (var x) (varᴺ x)

    appᴺᴰ :
      NTmᴰ Γ (A ⇒ B) f fᴺ → NTmᴰ Γ A a aᴺ →
      NTmᴰ Γ B (app f a) (appᴺ fᴺ aᴺ)
    lamᴺᴰ : NTmᴰ (Γ ▹ A) B b bᴺ → NTmᴰ Γ (A ⇒ B) (lam b) (lamᴺ bᴺ)

module NTmInd {ℓ} (D : NTmDModel ℓ) where
  open NTmDModel D

  postulate
    ⟦_⟧ : (aᴺ : NTm Γ A a) → NTmᴰ Γ A a aᴺ
    ⟦⟧-varᴺ : ⟦ varᴺ x ⟧ ≡ varᴺᴰ x
    {-# REWRITE ⟦⟧-varᴺ #-}

    ⟦⟧-appᴺ : ⟦ appᴺ fᴺ aᴺ ⟧ ≡ appᴺᴰ ⟦ fᴺ ⟧ ⟦ aᴺ ⟧
    {-# REWRITE ⟦⟧-appᴺ #-}
    ⟦⟧-lamᴺ : ⟦ lamᴺ bᴺ ⟧ ≡ lamᴺᴰ ⟦ bᴺ ⟧
    {-# REWRITE ⟦⟧-lamᴺ #-}

data Wk : (Δ Γ : Con) → Sub Δ Γ → Set where
  p : Wk (Γ ▹ A) Γ p
  _⁺ : Wk Δ Γ γ → Wk (Δ ▹ A) (Γ ▹ A) (γ ⁺)

infixl 9 _[_]ᵛʷ
_[_]ᵛʷ : Var Γ A → Wk Δ Γ γ → Var Δ A
x [ p ]ᵛʷ = vs x
vz [ γʷ ⁺ ]ᵛʷ = vz
vs x [ γʷ ⁺ ]ᵛʷ = vs (x [ γʷ ]ᵛʷ)

var-[]ʷ : {γʷ : Wk Δ Γ γ} → var x [ γ ] ≡ var (x [ γʷ ]ᵛʷ)
var-[]ʷ {x = x} {γʷ = p} = var-p
var-[]ʷ {x = vz} {γʷ = γʷ ⁺} = vz-⁺
var-[]ʷ {x = vs x} {γʷ = γʷ ⁺} = vs-⁺ ∙ cong _[ p ] var-[]ʷ ∙ var-p

module []ᴺʷ where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ A a _ = ∀ {Δ γ} → Wk Δ Γ γ → NTm Δ A (a [ γ ])
  M .NTmᴰ-prop = funextᵢ (funextᵢ (funext λ _ → NTm-prop))
  M .varᴺᴰ x γʷ = ntm[ sym var-[]ʷ ] (varᴺ (x [ γʷ ]ᵛʷ))

  M .appᴺᴰ fᴺ aᴺ γʷ = ntm[ sym app-[] ] (appᴺ (fᴺ γʷ) (aᴺ γʷ))
  M .lamᴺᴰ bᴺ γʷ = ntm[ sym lam-[] ] (lamᴺ (bᴺ (γʷ ⁺)))

  open NTmInd M public

infixl 9 _[_]ᴺʷ
_[_]ᴺʷ : NTm Γ A a → Wk Δ Γ γ → NTm Δ A (a [ γ ])
_[_]ᴺʷ aᴺ = []ᴺʷ.⟦ aᴺ ⟧

data NTSub : (Δ Γ : Con) → Sub Δ Γ → Set where
  _⁺ : NTSub Δ Γ γ → NTSub (Δ ▹ A) (Γ ▹ A) (γ ⁺)
  ⟨_⟩ : NTm Γ A a → NTSub Γ (Γ ▹ A) ⟨ a ⟩

_[_]ᵛᴺᵗ : (a : Var Γ A) → NTSub Δ Γ γ → NTm Δ A (var a [ γ ])
vz [ γᴺᵗ ⁺ ]ᵛᴺᵗ = ntm[ sym vz-⁺ ] (varᴺ vz)
vs x [ γᴺᵗ ⁺ ]ᵛᴺᵗ = ntm[ sym vs-⁺ ] (x [ γᴺᵗ ]ᵛᴺᵗ [ p ]ᴺʷ)
vz [ ⟨ aᴺ ⟩ ]ᵛᴺᵗ = ntm[ sym vz-⟨⟩ ] aᴺ
vs x [ ⟨ aᴺ ⟩ ]ᵛᴺᵗ = ntm[ sym vs-⟨⟩ ] (varᴺ x)

module []ᴺᵗ where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ A a _ = ∀ {Δ γ} → NTSub Δ Γ γ → NTm Δ A (a [ γ ])
  M .NTmᴰ-prop = funextᵢ (funextᵢ (funext λ _ → NTm-prop))
  M .varᴺᴰ x γᴺᵗ = x [ γᴺᵗ ]ᵛᴺᵗ

  M .appᴺᴰ fᴺ aᴺ γᴺᵗ = ntm[ sym app-[] ] (appᴺ (fᴺ γᴺᵗ) (aᴺ γᴺᵗ))
  M .lamᴺᴰ bᴺ γᴺᵗ = ntm[ sym lam-[] ] (lamᴺ (bᴺ (γᴺᵗ ⁺)))

  open NTmInd M public

infixl 9 _[_]ᴺᵗ
_[_]ᴺᵗ : NTm Γ A a → NTSub Δ Γ γ → NTm Δ A (a [ γ ])
_[_]ᴺᵗ aᴺ = []ᴺᵗ.⟦ aᴺ ⟧

data NSub (Δ Γ : Con) (γ : Sub Δ Γ) : Set where
  wk : Wk Δ Γ γ → NSub Δ Γ γ
  ntsub : NTSub Δ Γ γ → NSub Δ Γ γ

_[_]ᴺ : NTm Γ A a → NSub Δ Γ γ → NTm Δ A (a [ γ ])
aᴺ [ wk γʷ ]ᴺ = aᴺ [ γʷ ]ᴺʷ
aᴺ [ ntsub γᴺᵗ ]ᴺ = aᴺ [ γᴺᵗ ]ᴺᵗ

module norm where
  open TmDModel

  M : TmDModel _ _
  M .Subᴰ = NSub
  M .Tmᴰ = NTm
  M ._[_]ᴰ = _[_]ᴺ
  M .pᴰ = wk p
  M .varᴰ = varᴺ
  M .var-pᴰ = NTm-prop
  M ._⁺ᴰ (wk γʷ) = wk (γʷ ⁺)
  M ._⁺ᴰ (ntsub γᴺᵗ) = ntsub (γᴺᵗ ⁺)
  M .vz-⁺ᴰ = NTm-prop
  M .vs-⁺ᴰ = NTm-prop
  M .⟨_⟩ᴰ aᴺ = ntsub ⟨ aᴺ ⟩
  M .vz-⟨⟩ᴰ = NTm-prop
  M .vs-⟨⟩ᴰ = NTm-prop
  M .appᴰ = appᴺ
  M .app-[]ᴰ = NTm-prop
  M .lamᴰ = lamᴺ
  M .lam-[]ᴰ = NTm-prop
  M .⇒-βᴰ = NTm-prop
  M .⇒-ηᴰ = NTm-prop

  open TmInd M public

norm : (a : Tm Γ A) → NTm Γ A a
norm = norm.⟦_⟧ᵗ
