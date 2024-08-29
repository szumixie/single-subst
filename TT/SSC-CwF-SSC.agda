{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
#-}

module TT.SSC-CwF-SSC where

open import TT.Lib
open import TT.SSC.Syntax
open import TT.SSC.Ind
open import TT.SSC.Path
open import TT.SSC.Tel
open import TT.SSC.Lift
open import TT.SSC.Parallel
open import TT.SSC-CwF
open import TT.CwF-SSC

module S→C→S where
  open DM hiding (Subᴹ)
  open DModel hiding (Subᴹ)

  private variable
    i : ℕ
    Γ Δ : Con
    A : Ty Γ i
    a : Tm Γ A

  record Subᴹ
    (Δᴹ : C→Sᶜ (S→Cᶜ Δ) ≡ Δ) (Γᴹ : C→Sᶜ (S→Cᶜ Γ) ≡ Γ)
    (γ : Sub Δ Γ)
    : Set
    where
    eta-equality
    field
      ty : A [ coe (ap-Tms refl Γᴹ) (C→Sˢ (S→Cˢ γ)) ]ᵀᵗ ≡[ ap-Ty Δᴹ ] A [ γ ]ᵀ
      tm :
        a [ coe (ap-Tms refl Γᴹ) (C→Sˢ (S→Cˢ γ)) ]ᵗᵗ ≡[ ap-Tm₂ Δᴹ ty ] a [ γ ]ᵗ

  open Subᴹ

  M : DModel
  M .sorts .Conᴹ Γ = Lift (C→Sᶜ (S→Cᶜ Γ) ≡ Γ)
  M .sorts .DM.Subᴹ (lift Δᴹ) (lift Γᴹ) γ = Subᴹ Δᴹ Γᴹ γ
  M .sorts .Tyᴹ (lift Γᴹ) i A = Lift (C→Sᵀ (S→Cᵀ A) ≡[ ap-Ty Γᴹ ] A)
  M .sorts .Tmᴹ (lift Γᴹ) (lift Aᴹ) a = Lift (C→Sᵗ (S→Cᵗ a) ≡[ ap-Tm₂ Γᴹ Aᴹ ] a)

  M .core ._[_]ᵀᴹ {Γᴹ = lift Γᴹ} (lift Aᴹ) γᴹ .lower =
    dep (ap-[]ᵀᵗ₃ Γᴹ Aᴹ refl) ∙ᵈ γᴹ .ty
  M .core ._[_]ᵗᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} (lift aᴹ) γᴹ .lower =
    apᵈ-[]ᵗᵗ₄ Γᴹ Aᴹ aᴹ refl ∙ᵈ γᴹ .tm

  M .core .◇ᴹ .lower = refl
  M .core ._▹ᴹ_ (lift Γᴹ) (lift Aᴹ) .lower = ap-▹ Γᴹ Aᴹ

  M .core .pᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} .ty =
    apᵈ-[]ᵀᵗᵣ (ap-▹ Γᴹ Aᴹ) (splitl (apᵈ-pᵗ Γᴹ Aᴹ)) ∙ᵈ dep []ᵀ-pᵗ
  M .core .pᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} .tm =
    apᵈ-[]ᵗᵗᵣ (ap-▹ Γᴹ Aᴹ) (splitl (apᵈ-pᵗ Γᴹ Aᴹ)) ∙ᵈ []ᵗ-pᵗ
  M .core .qᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} .lower = splitl (apᵈ-q Γᴹ Aᴹ)

  M .core ._⁺ᴹ {Δᴹ = lift Δᴹ} {Γᴹ = lift Γᴹ} {γ = γ} {i} {A} {Aᴹ = lift Aᴹ} γᴹ .ty =
    apᵈ-[]ᵀᵗᵣ
      (ap-▹ Δᴹ (apᵈ-[]ᵀᵗ Γᴹ Aᴹ Δᴹ refl))
      (splitl (apᵈ-⁺ᵗ Δᴹ Γᴹ refl Aᴹ)) ∙ᵈ
    dep ([]ᵀ-⁺ᵗ (coe _ (C→Sˢ (S→Cˢ γ)))) ∙ᵈ
    []ᵛ→⁺^ᵀ
      ⌞ coe _ (C→Sˢ (S→Cˢ γ)) ⌟
      ⌜ γ ⌝
      (undep (apᵈ-[]ᵀᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .ty))
      (λ _ → apᵈ-[]ᵗᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .tm)
      (◇ ▹ A)
  M .core ._⁺ᴹ {Δᴹ = lift Δᴹ} {Γᴹ = lift Γᴹ} {γ = γ} {i} {A} {Aᴹ = lift Aᴹ} γᴹ .tm =
    apᵈ-[]ᵗᵗᵣ
      (ap-▹ Δᴹ (apᵈ-[]ᵀᵗ Γᴹ Aᴹ Δᴹ refl))
      (splitl (apᵈ-⁺ᵗ Δᴹ Γᴹ refl Aᴹ)) ∙ᵈ
    []ᵗ-⁺ᵗ (coe _ (C→Sˢ (S→Cˢ γ))) ∙ᵈ
    []ᵛ→⁺^ᵗ
      ⌞ coe _ (C→Sˢ (S→Cˢ γ)) ⌟
      ⌜ γ ⌝
      (undep (apᵈ-[]ᵀᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .ty))
      (λ _ → apᵈ-[]ᵗᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .tm)
      (◇ ▹ A)

  M .core .p-⁺ᵀᴹ = refl
  M .core .p-⁺ᵗᴹ = refl
  M .core .q-⁺ᴹ = refl

  M .core .⟨_⟩ᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} (lift aᴹ) .ty =
    apᵈ-[]ᵀᵗᵣ Γᴹ (splitl (apᵈ-⟨⟩ᵗ Γᴹ Aᴹ aᴹ)) ∙ᵈ dep []ᵀ-⟨⟩ᵗ
  M .core .⟨_⟩ᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} (lift aᴹ) .tm =
    apᵈ-[]ᵗᵗᵣ Γᴹ (splitl (apᵈ-⟨⟩ᵗ Γᴹ Aᴹ aᴹ)) ∙ᵈ []ᵗ-⟨⟩ᵗ

  M .core .p-⟨⟩ᵀᴹ = refl
  M .core .p-⟨⟩ᵗᴹ = refl
  M .core .q-⟨⟩ᴹ = refl

  M .core .⟨⟩-[]ᵀᴹ = refl
  M .core .▹-ηᵀᴹ = refl

  M .types .Uᴹ {Γᴹ = lift Γᴹ} i .lower = apᵈ-U Γᴹ
  M .types .U-[]ᴹ = refl

  M .types .Elᴹ {Γᴹ = lift Γᴹ} (lift αᴹ) .lower = apᵈ-El Γᴹ αᴹ
  M .types .El-[]ᴹ = refl

  M .types .cᴹ {Γᴹ = lift Γᴹ} (lift Aᴹ) .lower = apᵈ-c Γᴹ Aᴹ
  M .types .c-[]ᴹ = refl

  M .types .U-βᴹ = refl
  M .types .U-ηᴹ = refl

  M .types .Πᴹ {Γᴹ = lift Γᴹ} (lift Aᴹ) (lift Bᴹ) .lower = apᵈ-Π Γᴹ Aᴹ Bᴹ
  M .types .Π-[]ᴹ = refl

  M .types .appᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} {Bᴹ = lift Bᴹ} (lift fᴹ) (lift aᴹ) .lower =
    splitl (apᵈ-app Γᴹ Aᴹ Bᴹ fᴹ aᴹ)
  M .types .app-[]ᴹ = refl

  M .types .lamᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} {Bᴹ = lift Bᴹ} (lift bᴹ) .lower =
    apᵈ-lam₄ Γᴹ Aᴹ Bᴹ bᴹ
  M .types .lam-[]ᴹ = refl

  M .types .Π-βᴹ = refl
  M .types .Π-ηᴹ = refl

  open Ind M public

private variable
  i : ℕ
  Γ : Con
  A : Ty Γ i
  a : Tm Γ A

S→C→Sᶜ : C→Sᶜ (S→Cᶜ Γ) ≡ Γ
S→C→Sᶜ {Γ = Γ} = S→C→S.⟦ Γ ⟧ᶜ .lower

S→C→Sᵀ : C→Sᵀ (S→Cᵀ A) ≡[ ap-Ty S→C→Sᶜ ] A
S→C→Sᵀ {A = A} = S→C→S.⟦ A ⟧ᵀ .lower

S→C→Sᵗ : C→Sᵗ (S→Cᵗ a) ≡[ ap-Tm₂ S→C→Sᶜ S→C→Sᵀ ] a
S→C→Sᵗ {a = a} = S→C→S.⟦ a ⟧ᵗ .lower
