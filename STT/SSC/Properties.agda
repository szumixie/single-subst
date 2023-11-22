{-# OPTIONS
  --with-K --rewriting --postfix-projections --hidden-argument-puns #-}

module STT.SSC.Properties where

open import STT.Lib
open import STT.SSC
open import STT.SSC.SNf

private variable
  Γ Δ : Con
  γ : Sub Δ Γ
  A B : Ty
  b : Tm Γ A

module p-⁺ where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ B b bᴺ =
    ∀ {Δ A} {γ : Sub Δ Γ} → b [ p ] [ γ ⁺ ] ≡ (Tm (Δ ▹ A) B ∋ b [ γ ] [ p ])
  M .NTmᴰ-prop = funextᵢ (funextᵢ (funextᵢ (uip _ _)))
  M .varᴺᴰ x {γ} = cong _[ γ ⁺ ] var-p ∙ vs-⁺
  M .appᴺᴰ fᴺ aᴺ {γ} =
    cong _[ γ ⁺ ] app-[] ∙
    app-[] ∙
    cong₂ app fᴺ aᴺ ∙
    sym app-[] ∙
    cong _[ p ] (sym app-[])
  M .lamᴺᴰ bᴺ {γ} =
    cong _[ γ ⁺ ] lam-[] ∙
    lam-[] ∙
    {!   !} ∙
    sym lam-[] ∙
    cong _[ p ] (sym lam-[])

  open NTmInd M public

p-⁺ : b [ p ] [ γ ⁺ ] ≡ (Tm (Δ ▹ A) B ∋ b [ γ ] [ p ])
p-⁺ {b} = p-⁺.⟦ norm b ⟧
