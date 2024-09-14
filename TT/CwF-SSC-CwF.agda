{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
#-}

module TT.CwF-SSC-CwF where

open import TT.Lib
open import TT.CwF.Syntax
open import TT.CwF.Ind
open import TT.CwF-SSC
open import TT.SSC-CwF

module C→S→C where
  open DM
  open DModel

  M : DModel
  M .sorts .Conᴹ Γ = Liftₚ (S→Cᶜ (C→Sᶜ Γ) ≡ Γ)
  M .sorts .Subᴹ (liftₚ Δᴹ) (liftₚ Γᴹ) γ =
    Liftₚ (T→C (C→T γ) ≡[ ap-Sub Δᴹ Γᴹ ] γ)
  M .sorts .Tyᴹ (liftₚ Γᴹ) i A = Liftₚ (S→Cᵀ (C→Sᵀ A) ≡[ ap-Ty Γᴹ ] A)
  M .sorts .Tmᴹ (liftₚ Γᴹ) (liftₚ Aᴹ) a =
    Liftₚ (S→Cᵗ (C→Sᵗ a) ≡[ ap-Tm₂ Γᴹ Aᴹ ] a)

  M .core ._∘ᴹ_ {Δᴹ = liftₚ Δᴹ} {Γᴹ = liftₚ Γᴹ} {γ = γ} {Θᴹ = liftₚ Θᴹ} (liftₚ γᴹ) (liftₚ δᴹ) .lowerₚ =
    dep (T→C-∘ (C→T γ)) ∙ᵈ apᵈ-∘ Δᴹ Γᴹ γᴹ Θᴹ δᴹ
  M .core .assocᴹ = refl

  M .core .idᴹ {Γ} {Γᴹ = liftₚ Γᴹ} .lowerₚ = dep (T→C-id (C→Sᶜ Γ)) ∙ᵈ apᵈ-id Γᴹ
  M .core .idrᴹ = refl
  M .core .idlᴹ = refl

  M .core ._[_]ᵀᴹ {Γᴹ = liftₚ Γᴹ} {Δᴹ = liftₚ Δᴹ} {γ} (liftₚ Aᴹ) (liftₚ γᴹ) .lowerₚ =
    dep (S→C-[]ᵀᵗ (C→T γ)) ∙ᵈ apᵈ-[]ᵀ Γᴹ Aᴹ Δᴹ γᴹ
  M .core .[]ᵀ-∘ᴹ = refl
  M .core .[]ᵀ-idᴹ = refl

  M .core ._[_]ᵗᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} {Δᴹ = liftₚ Δᴹ} {γ = γ} (liftₚ aᴹ) (liftₚ γᴹ) .lowerₚ =
    S→C-[]ᵗᵗ (C→T γ) ∙ᵈ apᵈ-[]ᵗ₅ Γᴹ Aᴹ aᴹ Δᴹ γᴹ
  M .core .[]ᵗ-∘ᴹ = refl
  M .core .[]ᵗ-idᴹ = refl

  M .core .◇ᴹ .lowerₚ = refl
  M .core .εᴹ {Γ} {Γᴹ = liftₚ Γᴹ} .lowerₚ = dep (T→C-ε (C→Sᶜ Γ)) ∙ᵈ apᵈ-ε Γᴹ
  M .core .ε-∘ᴹ = refl
  M .core .◇-ηᴹ = refl

  M .core ._▹ᴹ_ (liftₚ Γᴹ) (liftₚ Aᴹ) .lowerₚ = ap-▹ Γᴹ Aᴹ
  M .core .pᴹ {Γᴹ = liftₚ Γᴹ} {i} {A} {Aᴹ = liftₚ Aᴹ} .lowerₚ =
    dep (T→C-p (C→Sᵀ A)) ∙ᵈ apᵈ-p₂ Γᴹ Aᴹ
  M .core .qᴹ {Γᴹ = liftₚ Γᴹ} {Aᴹ = liftₚ Aᴹ} .lowerₚ = splitl (apᵈ-q₂ Γᴹ Aᴹ)

  M .core ._,ᴹ_ {Δᴹ = liftₚ Δᴹ} {Γᴹ = liftₚ Γᴹ} {γ = γ} {Aᴹ = liftₚ Aᴹ} {a = a} (liftₚ γᴹ) (liftₚ aᴹ) .lowerₚ =
    dep (T→C-, (C→T γ) (C→Sᵗ a)) ∙ᵈ apᵈ-,₅ Δᴹ Γᴹ γᴹ Aᴹ (splitl aᴹ)
  M .core .,-∘ᴹ = refl

  M .core .▹-β₁ᴹ = refl
  M .core .▹-β₂ᴹ = refl
  M .core .▹-ηᴹ = refl

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
    apᵈ-lam Γᴹ Aᴹ Bᴹ bᴹ
  M .types .lam-[]ᴹ = refl

  M .types .Π-βᴹ = refl
  M .types .Π-ηᴹ = refl

  open Ind M public

private variable
  i : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A : Ty Γ i
  a : Tm Γ A

C→S→Cᶜ : S→Cᶜ (C→Sᶜ Γ) ≡ Γ
C→S→Cᶜ {Γ = Γ} = C→S→C.⟦ Γ ⟧ᶜ .lowerₚ

C→T→C : T→C (C→T γ) ≡[ ap-Sub C→S→Cᶜ C→S→Cᶜ ] γ
C→T→C {γ = γ} = C→S→C.⟦ γ ⟧ˢ .lowerₚ

C→S→Cᵀ : S→Cᵀ (C→Sᵀ A) ≡[ ap-Ty C→S→Cᶜ ] A
C→S→Cᵀ {A = A} = C→S→C.⟦ A ⟧ᵀ .lowerₚ

C→S→Cᵗ : S→Cᵗ (C→Sᵗ a) ≡[ ap-Tm₂ C→S→Cᶜ C→S→Cᵀ ] a
C→S→Cᵗ {a = a} = C→S→C.⟦ a ⟧ᵗ .lowerₚ
