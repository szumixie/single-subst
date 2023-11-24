{-# OPTIONS
  --with-K --rewriting --postfix-projections --hidden-argument-puns #-}

module STT.SSC.Properties where

open import STT.Lib
open import STT.SSC
open import STT.SSC.SNf

Tel : Set
Tel = Con

private variable
  Γ Δ : Con
  γ : Sub Δ Γ
  A B : Ty
  Ω : Tel

infixl 2 _++_
_++_ : Con → Tel → Con
Γ ++ ◇ = Γ
Γ ++ (Ω ▹ A) = (Γ ++ Ω) ▹ A

infixl 10 _⁺*
_⁺* : Sub Δ Γ → Sub (Δ ++ Ω) (Γ ++ Ω)
_⁺* {Ω = ◇} γ = γ
_⁺* {Ω = Ω ▹ A} γ = γ ⁺* ⁺

infixl 10 _⁺*ʷ
_⁺*ʷ : Wk Δ Γ γ → Wk (Δ ++ Ω) (Γ ++ Ω) (γ ⁺*)
_⁺*ʷ {Ω = ◇} γʷ = γʷ
_⁺*ʷ {Ω = Ω ▹ A} γʷ = γʷ ⁺*ʷ ⁺

var-p-⁺-⁺*ʷ :
  {x : Var (Γ ++ Ω) B} → Wk Δ Γ γ →
  var x [ p ⁺* ] [ γ ⁺ ⁺* ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ var x [ γ ⁺* ] [ p ⁺* ])
var-p-⁺-⁺*ʷ {Ω = ◇} {γ} γʷ = cong _[ γ ⁺ ] var-p ∙ vs-⁺
var-p-⁺-⁺*ʷ {Ω = Ω ▹ B} {γ} {x = vz} γʷ =
  cong _[ γ ⁺ ⁺* ⁺ ] vz-⁺ ∙ vz-⁺ ∙ sym vz-⁺ ∙ cong _[ p ⁺* ⁺ ] (sym vz-⁺)
var-p-⁺-⁺*ʷ {Ω = Ω ▹ B} {γ} {x = vs x} γʷ =
  cong _[ γ ⁺ ⁺* ⁺ ] (vs-⁺ ∙ cong _[ p ] (var-[]ʷ (p ⁺*ʷ)) ∙ var-p) ∙
  vs-⁺ ∙
  cong _[ p ]
    ( cong _[ γ ⁺ ⁺* ] (sym (var-[]ʷ (p ⁺*ʷ))) ∙
      var-p-⁺-⁺*ʷ γʷ ∙
      cong _[ p ⁺* ] (var-[]ʷ (γʷ ⁺*ʷ))) ∙
  sym vs-⁺ ∙
  cong _[ p ⁺* ⁺ ]
    (sym var-p ∙ cong _[ p ] (sym (var-[]ʷ (γʷ ⁺*ʷ))) ∙ sym vs-⁺)

module p-⁺-⁺*ʷ where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ₀ B b _ =
    ∀ {Γ Δ A Ω γ} (Γ₌ : Γ₀ ≡ (Γ ++ Ω)) → Wk Δ Γ γ →
    tm[ Γ₌ , refl ] b [ p ⁺* ] [ γ ⁺ ⁺* ] ≡
    (Tm (Δ ▹ A ++ Ω) B ∋ tm[ Γ₌ , refl ] b [ γ ⁺* ] [ p ⁺* ])
  M .NTmᴰ-prop =
    funextᵢ
      (funextᵢ
        (funextᵢ (funextᵢ (funextᵢ (funext λ _ → funext λ _ → uip _ _)))))
  M .varᴺᴰ x refl γʷ = var-p-⁺-⁺*ʷ γʷ
  M .appᴺᴰ fᴺᴰ aᴺᴰ {γ} refl γʷ =
    cong _[ γ ⁺ ⁺* ] app-[] ∙
    app-[] ∙
    cong₂ app (fᴺᴰ refl γʷ) (aᴺᴰ refl γʷ) ∙
    sym app-[] ∙
    cong _[ p ⁺* ] (sym app-[])
  M .lamᴺᴰ bᴺᴰ {γ} refl γʷ =
    cong _[ γ ⁺ ⁺* ] lam-[] ∙
    lam-[] ∙
    cong lam (bᴺᴰ refl γʷ) ∙
    sym lam-[] ∙
    cong _[ p ⁺* ] (sym lam-[])

  open NTmInd M public

p-⁺-⁺*ʷ :
  {b : Tm (Γ ++ Ω) B} → Wk Δ Γ γ →
  b [ p ⁺* ] [ γ ⁺ ⁺* ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ b [ γ ⁺* ] [ p ⁺* ])
p-⁺-⁺*ʷ {b} = p-⁺-⁺*ʷ.⟦ norm b ⟧ refl

var-p-⁺-⁺* :
  {x : Var (Γ ++ Ω) B} {γ : Sub Δ Γ} →
  var x [ p ⁺* ] [ γ ⁺ ⁺* ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ var x [ γ ⁺* ] [ p ⁺* ])
var-p-⁺-⁺* {Ω = ◇} {γ} = cong _[ γ ⁺ ] var-p ∙ vs-⁺
var-p-⁺-⁺* {Ω = Ω ▹ B} {x = vz} {γ} =
  cong _[ γ ⁺ ⁺* ⁺ ] vz-⁺ ∙ vz-⁺ ∙ sym vz-⁺ ∙ cong _[ p ⁺* ⁺ ] (sym vz-⁺)
var-p-⁺-⁺* {Ω = Ω ▹ B} {x = vs x} {γ} =
  cong _[ γ ⁺ ⁺* ⁺ ] (vs-⁺ ∙ cong _[ p ] (var-[]ʷ (p ⁺*ʷ)) ∙ var-p) ∙
  vs-⁺ ∙
  cong _[ p ] (cong _[ γ ⁺ ⁺* ] (sym (var-[]ʷ (p ⁺*ʷ))) ∙ var-p-⁺-⁺*) ∙
  sym (p-⁺-⁺*ʷ (p ⁺*ʷ)) ∙
  cong _[ p ⁺* ⁺ ] (sym vs-⁺)

module p-⁺-⁺* where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ₀ B b _ =
    ∀ {Γ Δ A Ω γ} (Γ₌ : Γ₀ ≡ (Γ ++ Ω)) →
    tm[ Γ₌ , refl ] b [ p ⁺* ] [ γ ⁺ ⁺* ] ≡
    (Tm (Δ ▹ A ++ Ω) B ∋ tm[ Γ₌ , refl ] b [ γ ⁺* ] [ p ⁺* ])
  M .NTmᴰ-prop =
    funextᵢ (funextᵢ (funextᵢ (funextᵢ (funextᵢ (funext λ _ → uip _ _)))))
  M .varᴺᴰ x refl = var-p-⁺-⁺*
  M .appᴺᴰ fᴺᴰ aᴺᴰ {γ} refl =
    cong _[ γ ⁺ ⁺* ] app-[] ∙
    app-[] ∙
    cong₂ app (fᴺᴰ refl) (aᴺᴰ refl) ∙
    sym app-[] ∙
    cong _[ p ⁺* ] (sym app-[])
  M .lamᴺᴰ bᴺᴰ {γ} refl =
    cong _[ γ ⁺ ⁺* ] lam-[] ∙
    lam-[] ∙
    cong lam (bᴺᴰ refl) ∙
    sym lam-[] ∙
    cong _[ p ⁺* ] (sym lam-[])

  open NTmInd M public

p-⁺-⁺* :
  {b : Tm (Γ ++ Ω) B} {γ : Sub Δ Γ} →
  b [ p ⁺* ] [ γ ⁺ ⁺* ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ b [ γ ⁺* ] [ p ⁺* ])
p-⁺-⁺* {b} = p-⁺-⁺*.⟦ norm b ⟧ refl
