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
  M .sorts .Conᴹ Γ = Lift (S→Cᶜ (C→Sᶜ Γ) ≡ Γ)
  M .sorts .Subᴹ (lift Δᴹ) (lift Γᴹ) γ = Lift (T→C (C→T γ) ≡[ ap-Sub Δᴹ Γᴹ ] γ)
  M .sorts .Tyᴹ (lift Γᴹ) i A = Lift (S→Cᵀ (C→Sᵀ A) ≡[ ap-Ty Γᴹ ] A)
  M .sorts .Tmᴹ (lift Γᴹ) (lift Aᴹ) a = Lift (S→Cᵗ (C→Sᵗ a) ≡[ ap-Tm₂ Γᴹ Aᴹ ] a)

  M .core ._∘ᴹ_ {Δᴹ = lift Δᴹ} {Γᴹ = lift Γᴹ} {γ = γ} {Θᴹ = lift Θᴹ} (lift γᴹ) (lift δᴹ) .lower =
    dep (T→C-∘ (C→T γ)) ∙ᵈ apᵈ-∘ Δᴹ Γᴹ γᴹ Θᴹ δᴹ
  M .core .assocᴹ = refl

  M .core .idᴹ {Γ} {Γᴹ = lift Γᴹ} .lower = dep (T→C-id (C→Sᶜ Γ)) ∙ᵈ apᵈ-id Γᴹ
  M .core .idrᴹ = refl
  M .core .idlᴹ = refl

  M .core ._[_]ᵀᴹ {Γᴹ = lift Γᴹ} {Δᴹ = lift Δᴹ} {γ} (lift Aᴹ) (lift γᴹ) .lower =
    dep (S→C-[]ᵀᵗ (C→T γ)) ∙ᵈ apᵈ-[]ᵀ Γᴹ Aᴹ Δᴹ γᴹ
  M .core .[]ᵀ-∘ᴹ = refl
  M .core .[]ᵀ-idᴹ = refl

  M .core ._[_]ᵗᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} {Δᴹ = lift Δᴹ} {γ = γ} (lift aᴹ) (lift γᴹ) .lower =
    S→C-[]ᵗᵗ (C→T γ) ∙ᵈ apᵈ-[]ᵗ₅ Γᴹ Aᴹ aᴹ Δᴹ γᴹ
  M .core .[]ᵗ-∘ᴹ = refl
  M .core .[]ᵗ-idᴹ = refl

  M .core .◇ᴹ .lower = refl
  M .core .εᴹ {Γ} {Γᴹ = lift Γᴹ} .lower = dep (T→C-ε (C→Sᶜ Γ)) ∙ᵈ apᵈ-ε Γᴹ
  M .core .ε-∘ᴹ = refl
  M .core .◇-ηᴹ = refl

  M .core ._▹ᴹ_ (lift Γᴹ) (lift Aᴹ) .lower = ap-▹ Γᴹ Aᴹ
  M .core .pᴹ {Γᴹ = lift Γᴹ} {i} {A} {Aᴹ = lift Aᴹ} .lower =
    dep (T→C-p (C→Sᵀ A)) ∙ᵈ apᵈ-p₂ Γᴹ Aᴹ
  M .core .qᴹ {Γᴹ = lift Γᴹ} {Aᴹ = lift Aᴹ} .lower = splitl (apᵈ-q₂ Γᴹ Aᴹ)

  M .core ._,ᴹ_ {Δᴹ = lift Δᴹ} {Γᴹ = lift Γᴹ} {γ = γ} {Aᴹ = lift Aᴹ} {a = a} (lift γᴹ) (lift aᴹ) .lower =
    dep (T→C-, (C→T γ) (C→Sᵗ a)) ∙ᵈ apᵈ-,₅ Δᴹ Γᴹ γᴹ Aᴹ (splitl aᴹ)
  M .core .,-∘ᴹ = refl

  M .core .▹-β₁ᴹ = refl
  M .core .▹-β₂ᴹ = refl
  M .core .▹-ηᴹ = refl

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
C→S→Cᶜ {Γ = Γ} = C→S→C.⟦ Γ ⟧ᶜ .lower

C→T→C : T→C (C→T γ) ≡[ ap-Sub C→S→Cᶜ C→S→Cᶜ ] γ
C→T→C {γ = γ} = C→S→C.⟦ γ ⟧ˢ .lower

C→S→Cᵀ : S→Cᵀ (C→Sᵀ A) ≡[ ap-Ty C→S→Cᶜ ] A
C→S→Cᵀ {A = A} = C→S→C.⟦ A ⟧ᵀ .lower

C→S→Cᵗ : S→Cᵗ (C→Sᵗ a) ≡[ ap-Tm₂ C→S→Cᶜ C→S→Cᵀ ] a
C→S→Cᵗ {a = a} = C→S→C.⟦ a ⟧ᵗ .lower
