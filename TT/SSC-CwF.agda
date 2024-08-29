{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
  --hidden-argument-puns
#-}

module TT.SSC-CwF where

open import TT.Lib
open import TT.CwF.Syntax
import TT.SSC.Syntax as S
open import TT.SSC.Ind
open import TT.SSC.Path as S hiding (⌜_⌝; _∘_; id)
open import TT.SSC.Lift
open import TT.SSC.Parallel as S hiding (ε; _,_; ap-,)

module S→C where
  open DM
  open DModel

  M : DModel
  M .sorts .Conᴹ _ = Con
  M .sorts .Subᴹ Δ Γ _ = Sub Δ Γ
  M .sorts .Tyᴹ A i _ = Ty A i
  M .sorts .Tmᴹ Γ A _ = Tm Γ A

  M .core ._[_]ᵀᴹ = _[_]ᵀ
  M .core ._[_]ᵗᴹ = _[_]ᵗ

  M .core .◇ᴹ = ◇
  M .core ._▹ᴹ_ = _▹_

  M .core .pᴹ = p
  M .core .qᴹ = q

  M .core ⁺ᴹ = _⁺
  M .core .p-⁺ᵀᴹ = dep (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ▹-β₁ ∙ []ᵀ-∘ )

  M .core .p-⁺ᵗᴹ = symᵈ []ᵗ-∘ ∙ᵈ apᵈ-[]ᵗᵣ ▹-β₁ ∙ᵈ []ᵗ-∘
  M .core .q-⁺ᴹ = merger ▹-β₂

  M .core .⟨_⟩ᴹ = ⟨_⟩
  M .core .p-⟨⟩ᵀᴹ = dep (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ▹-β₁ ∙ []ᵀ-id)

  M .core .p-⟨⟩ᵗᴹ = symᵈ []ᵗ-∘ ∙ᵈ apᵈ-[]ᵗᵣ ▹-β₁ ∙ᵈ []ᵗ-id
  M .core .q-⟨⟩ᴹ = merger ▹-β₂

  M .core .⟨⟩-[]ᵀᴹ = dep (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ⟨⟩-∘ ∙ []ᵀ-∘)
  M .core .▹-ηᵀᴹ = dep (sym []ᵀ-id ∙ ap-[]ᵀᵣ ▹-η′ ∙ []ᵀ-∘)

  M .types .Uᴹ = U
  M .types .U-[]ᴹ = dep U-[]

  M .types .Elᴹ = El
  M .types .El-[]ᴹ = dep El-[]

  M .types .cᴹ = c
  M .types .c-[]ᴹ = c-[]

  M .types .U-βᴹ = dep U-β
  M .types .U-ηᴹ = dep U-η

  M .types .Πᴹ = Π
  M .types .Π-[]ᴹ = dep Π-[]

  M .types .appᴹ = app
  M .types .app-[]ᴹ = app-[]

  M .types .lamᴹ = lam
  M .types .lam-[]ᴹ = lam-[]

  M .types .Π-βᴹ = dep Π-β
  M .types .Π-ηᴹ = Π-η

  open Ind M public

open S→C public using ()
  renaming (⟦_⟧ᶜ to S→Cᶜ; ⟦_⟧ˢ to S→Cˢ; ⟦_⟧ᵀ to S→Cᵀ; ⟦_⟧ᵗ to S→Cᵗ)

private variable
  i : ℕ
  Γ Δ Θ : S.Con
  A A₀ A₁ : S.Ty Γ i
  a₀ a₁ : S.Tm Γ A
  γᵗ δᵗ : Tms Δ Γ

opaque
  unfolding coe

  ap-S→Cᵀ : A₀ ≡ A₁ → S→Cᵀ A₀ ≡ S→Cᵀ A₁
  ap-S→Cᵀ refl = refl

  ap-S→Cᵗ :
    (A₀₁ : A₀ ≡ A₁) → a₀ ≡[ S.ap-Tm A₀₁ ] a₁ →
    S→Cᵗ a₀ ≡[ ap-Tm (ap-S→Cᵀ A₀₁) ] S→Cᵗ a₁
  ap-S→Cᵗ refl refl = refl

S*→C : Sub* Δ Γ → Sub (S→Cᶜ Δ) (S→Cᶜ Γ)
S*→C S.⌜ γ ⌝ = S→Cˢ γ
S*→C (γ* S.∘ δ*) = S*→C γ* ∘ S*→C δ*
S*→C S.id = id

S→C-[]ᵀ* : (γ* : Sub* Δ Γ) → S→Cᵀ (A [ γ* ]ᵀ*) ≡ S→Cᵀ A [ S*→C γ* ]ᵀ
S→C-[]ᵀ* S.⌜ γ ⌝ = refl
S→C-[]ᵀ* (γ* S.∘ δ*) = S→C-[]ᵀ* δ* ∙ ap-[]ᵀ (S→C-[]ᵀ* γ*) ∙ sym []ᵀ-∘
S→C-[]ᵀ* S.id = sym []ᵀ-id

S→C-[]ᵗ* :
  {A : S.Ty Γ i} {a : S.Tm Γ A} (γ* : Sub* Δ Γ) →
  S→Cᵗ (a [ γ* ]ᵗ*) ≡[ ap-Tm (S→C-[]ᵀ* γ*) ] S→Cᵗ a [ S*→C γ* ]ᵗ
S→C-[]ᵗ* S.⌜ γ ⌝ = reflᵈ
S→C-[]ᵗ* (γ* S.∘ δ*) =
  S→C-[]ᵗ* δ* ∙ᵈ apᵈ-[]ᵗ (S→C-[]ᵀ* γ*) (S→C-[]ᵗ* γ*) ∙ᵈ symᵈ []ᵗ-∘
S→C-[]ᵗ* S.id = symᵈ []ᵗ-id

S→C-ε* : (Γ : S.Con) → S*→C (ε* {Γ = Γ}) ≡ ε
S→C-ε* S.◇ = ◇-η
S→C-ε* (Γ S.▹ A) = ap-∘ₗ (S→C-ε* Γ) ∙ ε-∘

S→C-⁺* :
  {A : S.Ty Γ i} (γ* : Sub* Δ Γ) →
  S*→C (_⁺* {A = A} γ*) ≡[ ap-Subₗ (ap-▹ᵣ (S→C-[]ᵀ* γ*)) ] S*→C γ* ⁺
S→C-⁺* S.⌜ γ ⌝ = reflᵈ
S→C-⁺* (γ* S.∘ δ*) =
  apᵈ-∘
    (ap-▹ᵣ (S→C-[]ᵀ* γ*))
    refl
    (S→C-⁺* γ*)
    (ap-▹ᵣ (S→C-[]ᵀ* δ* ∙ ap-[]ᵀ (S→C-[]ᵀ* γ*) ∙ sym []ᵀ-∘ ∙ []ᵀ-∘))
    (S→C-⁺* δ* ∙ᵈ apᵈ-⁺ (S→C-[]ᵀ* γ*)) ∙ᵈ
  symᵈ ⁺-∘
S→C-⁺* S.id = symᵈ ⁺-id

T→C : Tms Δ Γ → Sub (S→Cᶜ Δ) (S→Cᶜ Γ)
T→C γᵗ = S*→C ⌞ γᵗ ⌟

S→C-[]ᵀᵗ : (γᵗ : Tms Δ Γ) → S→Cᵀ (A [ γᵗ ]ᵀᵗ) ≡ S→Cᵀ A [ T→C γᵗ ]ᵀ
S→C-[]ᵀᵗ γᵗ = S→C-[]ᵀ* ⌞ γᵗ ⌟

S→C-[]ᵗᵗ :
  {A : S.Ty Γ i} {a : S.Tm Γ A} (γᵗ : Tms Δ Γ) →
  S→Cᵗ (a [ γᵗ ]ᵗᵗ) ≡[ ap-Tm (S→C-[]ᵀᵗ γᵗ) ] S→Cᵗ a [ T→C γᵗ ]ᵗ
S→C-[]ᵗᵗ γᵗ = S→C-[]ᵗ* ⌞ γᵗ ⌟

S→C-εᵗ : (Γ : S.Con) → T→C (S.ε {Γ}) ≡ ε
S→C-εᵗ Γ = S→C-ε* Γ

S→C-,ᵗ :
  (γᵗ : Tms Δ Γ) {A : S.Ty Γ i} (a : S.Tm Δ (A S.[ γᵗ ]ᵀᵗ)) →
  T→C (γᵗ S., a) ≡ (T→C γᵗ , coe (ap-Tm (S→C-[]ᵀᵗ γᵗ)) (S→Cᵗ a))
S→C-,ᵗ γᵗ a =
  ap-∘₃ (ap-▹ᵣ (S→C-[]ᵀᵗ γᵗ)) (S→C-⁺* ⌞ γᵗ ⌟) (apᵈ-⟨⟩ (S→C-[]ᵀᵗ γᵗ) refl) ∙ ⁺-⟨⟩

S→C-∘ᵗ : (γᵗ : Tms Δ Γ) {δᵗ : Tms Θ Δ} → T→C (γᵗ ∘ᵗ δᵗ) ≡ T→C γᵗ ∘ T→C δᵗ
S→C-∘ᵗ {Δ} {Θ} S.ε = S→C-εᵗ Θ ∙ sym ε-∘ ∙ ap-∘ₗ (sym (S→C-εᵗ Δ))
S→C-∘ᵗ (γᵗ S., a) {δᵗ} =
  S→C-,ᵗ (γᵗ ∘ᵗ δᵗ) (coe (S.ap-Tm (sym ([]ᵀ-∘ᵗ γᵗ δᵗ))) (a [ δᵗ ]ᵗᵗ)) ∙
  ap-,
    (S→C-∘ᵗ γᵗ)
    (splitlr (splitl (S→C-[]ᵗᵗ δᵗ ∙ᵈ apᵈ-[]ᵗ (S→C-[]ᵀᵗ γᵗ) refl))) ∙
  sym ,-∘ ∙
  ap-∘ₗ (sym (S→C-,ᵗ γᵗ a))

S→C-∘pᵗ : (γᵗ : Tms Δ Γ) → T→C (_∘pᵗ {A = A} γᵗ) ≡ T→C γᵗ ∘ p
S→C-∘pᵗ S.ε = refl
S→C-∘pᵗ (γᵗ S., a) =
  S→C-,ᵗ (γᵗ ∘pᵗ) (coe (S.ap-Tm (sym ([]ᵀ-∘pᵗ γᵗ))) (a S.[ S.p ]ᵗ)) ∙
  ap-, (S→C-∘pᵗ γᵗ) (splitlr (splitl (apᵈ-[]ᵗ (S→C-[]ᵀᵗ γᵗ) refl))) ∙
  sym ,-∘ ∙
  ap-∘ₗ (sym (S→C-,ᵗ γᵗ a))

S→C-idᵗ : (Γ : S.Con) → T→C (idᵗ {Γ = Γ}) ≡ id
S→C-idᵗ S.◇ = refl
S→C-idᵗ (Γ S.▹ A) =
  S→C-,ᵗ pᵗ {A = A} (coe (S.ap-Tm (sym []ᵀ-pᵗ)) S.q) ∙
  ap-,
    (S→C-∘pᵗ (idᵗ {Γ = Γ}) ∙ ap-∘ₗ (S→C-idᵗ Γ) ∙ idl)
    (splitl (splitl reflᵈ)) ∙
  sym ▹-η

S→C-pᵗ : (A : S.Ty Γ i) → T→C (pᵗ {A = A}) ≡ p
S→C-pᵗ {Γ} A = S→C-∘pᵗ (idᵗ {Γ = Γ}) ∙ ap-∘ₗ (S→C-idᵗ Γ) ∙ idl
