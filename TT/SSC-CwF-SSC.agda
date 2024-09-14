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
import TT.CwF.Syntax as C
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
      ty : A [ coe (ap-Tms refl Γᴹ) (C→T (S→Cˢ γ)) ]ᵀᵗ ≡[ ap-Ty Δᴹ ] A [ γ ]ᵀ
      tm :
        a [ coe (ap-Tms refl Γᴹ) (C→T (S→Cˢ γ)) ]ᵗᵗ ≡[ ap-Tm₂ Δᴹ ty ] a [ γ ]ᵗ

  open Subᴹ

  M : DModel
  M .sorts .Conᴹ Γ = Liftₚ (C→Sᶜ (S→Cᶜ Γ) ≡ Γ)
  M .sorts .DM.Subᴹ (liftₚ Δᴹ) (liftₚ Γᴹ) γ = Subᴹ Δᴹ Γᴹ γ
  M .sorts .Tyᴹ (liftₚ Γᴹ) i A = Liftₚ (C→Sᵀ (S→Cᵀ A) ≡[ ap-Ty Γᴹ ] A)
  M .sorts .Tmᴹ (liftₚ Γᴹ) (liftₚ Aᴹ) a =
    Liftₚ (C→Sᵗ (S→Cᵗ a) ≡[ ap-Tm₂ Γᴹ Aᴹ ] a)

  M .core ._[_]ᵀᴹ {Γᴹ = liftₚ Γᴹ} (liftₚ Aᴹ) γᴹ .lowerₚ =
    dep (ap-[]ᵀᵗ₃ Γᴹ Aᴹ refl) ∙ᵈ γᴹ .ty
  M .core ._[_]ᵗᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} (liftₚ aᴹ) γᴹ .lowerₚ =
    apᵈ-[]ᵗᵗ₄ Γᴹ Aᴹ aᴹ refl ∙ᵈ γᴹ .tm

  M .core .◇ᴹ .lowerₚ = refl
  M .core ._▹ᴹ_ (liftₚ Γᴹ) (liftₚ Aᴹ) .lowerₚ = ap-▹ Γᴹ Aᴹ

  M .core .pᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} .ty =
    apᵈ-[]ᵀᵗᵣ (ap-▹ Γᴹ Aᴹ) (splitl (apᵈ-pᵗ Γᴹ Aᴹ)) ∙ᵈ dep []ᵀ-pᵗ
  M .core .pᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} .tm =
    apᵈ-[]ᵗᵗᵣ (ap-▹ Γᴹ Aᴹ) (splitl (apᵈ-pᵗ Γᴹ Aᴹ)) ∙ᵈ []ᵗ-pᵗ
  M .core .qᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} .lowerₚ = splitl (apᵈ-q Γᴹ Aᴹ)

  M .core ._⁺ᴹ {Δᴹ = liftₚ Δᴹ} {Γᴹ = liftₚ Γᴹ} {γ = γ} {i} {A} {Aᴹ = liftₚ Aᴹ} γᴹ .ty =
    apᵈ-[]ᵀᵗᵣ
      (ap-▹ Δᴹ (apᵈ-[]ᵀᵗ Γᴹ Aᴹ Δᴹ refl))
      (splitl (apᵈ-⁺ᵗ Δᴹ Γᴹ refl Aᴹ)) ∙ᵈ
    dep ([]ᵀ-⁺ᵗ (coe _ (C→T (S→Cˢ γ)))) ∙ᵈ
    []ᵛ→⁺^ᵀ
      ⌞ coe _ (C→T (S→Cˢ γ)) ⌟
      ⌜ γ ⌝
      (undep (apᵈ-[]ᵀᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .ty))
      (λ _ → apᵈ-[]ᵗᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .tm)
      (◇ ▹ A)
  M .core ._⁺ᴹ {Δᴹ = liftₚ Δᴹ} {Γᴹ = liftₚ Γᴹ} {γ = γ} {i} {A} {Aᴹ = liftₚ Aᴹ} γᴹ .tm =
    apᵈ-[]ᵗᵗᵣ
      (ap-▹ Δᴹ (apᵈ-[]ᵀᵗ Γᴹ Aᴹ Δᴹ refl))
      (splitl (apᵈ-⁺ᵗ Δᴹ Γᴹ refl Aᴹ)) ∙ᵈ
    []ᵗ-⁺ᵗ (coe _ (C→T (S→Cˢ γ))) ∙ᵈ
    []ᵛ→⁺^ᵗ
      ⌞ coe _ (C→T (S→Cˢ γ)) ⌟
      ⌜ γ ⌝
      (undep (apᵈ-[]ᵀᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .ty))
      (λ _ → apᵈ-[]ᵗᵗᵣ (sym Δᴹ) (splitl {A₀₁ = ap-Tms Δᴹ Γᴹ} refl) ∙ᵈ γᴹ .tm)
      (◇ ▹ A)

  M .core .p-⁺ᵀᴹ = refl
  M .core .p-⁺ᵗᴹ = refl
  M .core .q-⁺ᴹ = refl

  M .core .⟨_⟩ᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} (liftₚ aᴹ) .ty =
    apᵈ-[]ᵀᵗᵣ Γᴹ (splitl (apᵈ-⟨⟩ᵗ Γᴹ Aᴹ aᴹ)) ∙ᵈ dep []ᵀ-⟨⟩ᵗ
  M .core .⟨_⟩ᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} (liftₚ aᴹ) .tm =
    apᵈ-[]ᵗᵗᵣ Γᴹ (splitl (apᵈ-⟨⟩ᵗ Γᴹ Aᴹ aᴹ)) ∙ᵈ []ᵗ-⟨⟩ᵗ

  M .core .p-⟨⟩ᵀᴹ = refl
  M .core .p-⟨⟩ᵗᴹ = refl
  M .core .q-⟨⟩ᴹ = refl

  M .core .⟨⟩-[]ᵀᴹ = refl
  M .core .▹-ηᵀᴹ = refl

  M .types .Uᴹ {Γᴹ = liftₚ Γᴹ} i .lowerₚ = apᵈ-U Γᴹ
  M .types .U-[]ᴹ = refl

  M .types .Elᴹ {Γᴹ = liftₚ Γᴹ} (liftₚ αᴹ) .lowerₚ = apᵈ-El Γᴹ αᴹ
  M .types .El-[]ᴹ = refl

  M .types .cᴹ {Γᴹ = liftₚ Γᴹ} (liftₚ Aᴹ) .lowerₚ = apᵈ-c Γᴹ Aᴹ
  M .types .c-[]ᴹ = refl

  M .types .U-βᴹ = refl
  M .types .U-ηᴹ = refl

  M .types .Liftᴹ {Γᴹ = liftₚ Γᴹ} (liftₚ Aᴹ) .lowerₚ = apᵈ-Lift Γᴹ Aᴹ
  M .types .Lift-[]ᴹ = refl

  M .types .lowerᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} (liftₚ aᴹ) .lowerₚ =
    apᵈ-lower Γᴹ Aᴹ aᴹ
  M .types .lower-[]ᴹ = refl

  M .types .liftᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} (liftₚ aᴹ) .lowerₚ =
    apᵈ-lift Γᴹ Aᴹ aᴹ
  M .types .lift-[]ᴹ = refl

  M .types .Lift-βᴹ = refl
  M .types .Lift-ηᴹ = refl

  M .types .Πᴹ {Γᴹ = liftₚ Γᴹ} (liftₚ Aᴹ) (liftₚ Bᴹ) .lowerₚ = apᵈ-Π Γᴹ Aᴹ Bᴹ
  M .types .Π-[]ᴹ = refl

  M .types .appᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} {Bᴹ = liftₚ Bᴹ} (liftₚ fᴹ) (liftₚ aᴹ) .lowerₚ =
    splitl (apᵈ-app Γᴹ Aᴹ Bᴹ fᴹ aᴹ)
  M .types .app-[]ᴹ = refl

  M .types .lamᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} {Bᴹ = liftₚ Bᴹ} (liftₚ bᴹ) .lowerₚ =
    apᵈ-lam₄ Γᴹ Aᴹ Bᴹ bᴹ
  M .types .lam-[]ᴹ = refl

  M .types .Π-βᴹ = refl
  M .types .Π-ηᴹ = refl

  open Ind M public

private variable
  i : ℕ
  Γ Δ : Con
  A : Ty Γ i
  a : Tm Γ A
  γᵗ : Tms Δ Γ

S→C→Sᶜ : C→Sᶜ (S→Cᶜ Γ) ≡ Γ
S→C→Sᶜ {Γ = Γ} = S→C→S.⟦ Γ ⟧ᶜ .lowerₚ

S→C→Sᵀ : C→Sᵀ (S→Cᵀ A) ≡[ ap-Ty S→C→Sᶜ ] A
S→C→Sᵀ {A = A} = S→C→S.⟦ A ⟧ᵀ .lowerₚ

S→C→Sᵗ : C→Sᵗ (S→Cᵗ a) ≡[ ap-Tm₂ S→C→Sᶜ S→C→Sᵀ ] a
S→C→Sᵗ {a = a} = S→C→S.⟦ a ⟧ᵗ .lowerₚ

T→C→T : C→T (T→C γᵗ) ≡[ ap-Tms S→C→Sᶜ S→C→Sᶜ ] γᵗ
T→C→T {Γ} {γᵗ = ε} = dep (ap-C→T (T→C-ε Γ)) ∙ᵈ apᵈ-ε S→C→Sᶜ
T→C→T {γᵗ = γᵗ , a} =
  dep (ap-C→T (T→C-, γᵗ a)) ∙ᵈ apᵈ-, S→C→Sᶜ S→C→Sᶜ T→C→T S→C→Sᵀ (splitl S→C→Sᵗ)
