{-# OPTIONS --with-K --rewriting #-}

module STT.SSC where

open import STT.Lib

infixr 0 _⇒_
data Ty : Set where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

infixl 2 _▹_
data Con : Set where
  ◇ : Con
  _▹_ : Con → Ty → Con

private variable
  Γ Γ₀ Γ₁ Δ : Con
  A A₀ A₁ B : Ty

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ B → Var (Γ ▹ A) B

postulate
  Tm : Con → Ty → Set

infixl 10 _⁺
data Sub : Con → Con → Set where
  p : Sub (Γ ▹ A) Γ
  _⁺ : Sub Δ Γ → Sub (Δ ▹ A) (Γ ▹ A)
  ⟨_⟩ : Tm Γ A → Sub Γ (Γ ▹ A)

private variable
  γ : Sub Δ Γ
  a a₀ a₁ b f : Tm Γ A
  x : Var Γ A

postulate
  _[_] : Tm Γ A → Sub Δ Γ → Tm Δ A
  var : Var Γ A → Tm Γ A
  var-p : var x [ p ] ≡ (Tm (Γ ▹ A) B ∋ var (vs x))

  vz-⁺ : var vz [ γ ⁺ ] ≡ (Tm (Δ ▹ A) A ∋ var vz)
  vs-⁺ : var (vs x) [ γ ⁺ ] ≡ (Tm (Δ ▹ A) B ∋ var x [ γ ] [ p ])

  vz-⟨⟩ : var vz [ ⟨ a ⟩ ] ≡ a
  vs-⟨⟩ : var (vs x) [ ⟨ a ⟩ ] ≡ var x

  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  app-[] : app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  lam-[] : lam b [ γ ] ≡ lam (b [ γ ⁺ ])

  ⇒-β : app (lam b) a ≡ b [ ⟨ a ⟩ ]
  ⇒-η : f ≡ lam (app (f [ p ]) (var vz))

tm[_,_] : Γ₀ ≡ Γ₁ → A₀ ≡ A₁ → Tm Γ₀ A₀ → Tm Γ₁ A₁
tm[ refl , refl ] a = a

record TmDModel ℓ₀ ℓ₁ : Set (suc (ℓ₀ ⊔ ℓ₁)) where
  no-eta-equality
  infixl 9 _[_]ᴰ
  field
    Subᴰ : (Δ Γ : Con) → Sub Δ Γ → Set ℓ₀
    Tmᴰ : (Γ : Con) (A : Ty) → Tm Γ A → Set ℓ₁
    _[_]ᴰ : Tmᴰ Γ A a → (γᴰ : Subᴰ Δ Γ γ) → Tmᴰ Δ A (a [ γ ])

  tmᴰ[_] : a₀ ≡ a₁ → Tmᴰ Γ A a₀ → Tmᴰ Γ A a₁
  tmᴰ[_] = subst (Tmᴰ _ _)

  field
    pᴰ : Subᴰ (Γ ▹ A) Γ p
    varᴰ : (x : Var Γ A) → Tmᴰ Γ A (var x)
    var-pᴰ :
      tmᴰ[ var-p ] (varᴰ x [ pᴰ ]ᴰ) ≡ (Tmᴰ (Γ ▹ A) B (var (vs x)) ∋ varᴰ (vs x))

  infixl 10 _⁺ᴰ
  field
    _⁺ᴰ : (γᴰ : Subᴰ Δ Γ γ) → Subᴰ (Δ ▹ A) (Γ ▹ A) (γ ⁺)
    vz-⁺ᴰ :
      {γᴰ : Subᴰ Δ Γ γ} →
      tmᴰ[ vz-⁺ ] (varᴰ vz [ γᴰ ⁺ᴰ ]ᴰ) ≡ (Tmᴰ (Δ ▹ A) A (var vz) ∋ varᴰ vz)
    vs-⁺ᴰ :
      {γᴰ : Subᴰ Δ Γ γ} →
      tmᴰ[ vs-⁺ ] (varᴰ (vs x) [ γᴰ ⁺ᴰ ]ᴰ) ≡
      (Tmᴰ (Δ ▹ A) B (var x [ γ ] [ p ]) ∋ varᴰ x [ γᴰ ]ᴰ [ pᴰ ]ᴰ)

    ⟨_⟩ᴰ : Tmᴰ Γ A a → Subᴰ Γ (Γ ▹ A) ⟨ a ⟩
    vz-⟨⟩ᴰ : {aᴰ : Tmᴰ Γ A a} → tmᴰ[ vz-⟨⟩ ] (varᴰ vz [ ⟨ aᴰ ⟩ᴰ ]ᴰ) ≡ aᴰ
    vs-⟨⟩ᴰ : {aᴰ : Tmᴰ Γ A a} → tmᴰ[ vs-⟨⟩ ] (varᴰ (vs x) [ ⟨ aᴰ ⟩ᴰ ]ᴰ) ≡ varᴰ x

  field
    appᴰ : Tmᴰ Γ (A ⇒ B) f → Tmᴰ Γ A a → Tmᴰ Γ B (app f a)
    app-[]ᴰ :
      {fᴰ : Tmᴰ Γ (A ⇒ B) f} {aᴰ : Tmᴰ Γ A a} {γᴰ : Subᴰ Δ Γ γ} →
      tmᴰ[ app-[] ] (appᴰ fᴰ aᴰ [ γᴰ ]ᴰ) ≡ appᴰ (fᴰ [ γᴰ ]ᴰ) (aᴰ [ γᴰ ]ᴰ)

    lamᴰ : Tmᴰ (Γ ▹ A) B b → Tmᴰ Γ (A ⇒ B) (lam b)
    lam-[]ᴰ :
      {bᴰ : Tmᴰ (Γ ▹ A) B b} {γᴰ : Subᴰ Δ Γ γ} →
      tmᴰ[ lam-[] ] (lamᴰ bᴰ [ γᴰ ]ᴰ) ≡ lamᴰ (bᴰ [ γᴰ ⁺ᴰ ]ᴰ)

    ⇒-βᴰ :
      {bᴰ : Tmᴰ (Γ ▹ A) B b} {aᴰ : Tmᴰ Γ A a} →
      tmᴰ[ ⇒-β ] (appᴰ (lamᴰ bᴰ) aᴰ) ≡ bᴰ [ ⟨ aᴰ ⟩ᴰ ]ᴰ
    ⇒-ηᴰ :
      {fᴰ : Tmᴰ Γ (A ⇒ B) f} →
      tmᴰ[ ⇒-η ] fᴰ ≡ lamᴰ (appᴰ (fᴰ [ pᴰ ]ᴰ) (varᴰ vz))

module TmInd {ℓˢ ℓᵗ} (D : TmDModel ℓˢ ℓᵗ) where
  open TmDModel D

  postulate
    ⟦_⟧ᵗ : (a : Tm Γ A) → Tmᴰ Γ A a

  ⟦_⟧ˢ : (γ : Sub Δ Γ) → Subᴰ Δ Γ γ
  ⟦ p ⟧ˢ = pᴰ
  ⟦ γ ⁺ ⟧ˢ = ⟦ γ ⟧ˢ ⁺ᴰ
  ⟦ ⟨ a ⟩ ⟧ˢ = ⟨ ⟦ a ⟧ᵗ ⟩ᴰ

  postulate
    ⟦⟧-[] : ⟦ a [ γ ] ⟧ᵗ ≡ ⟦ a ⟧ᵗ [ ⟦ γ ⟧ˢ ]ᴰ
    {-# REWRITE ⟦⟧-[] #-}
    ⟦⟧-var : ⟦ var x ⟧ᵗ ≡ varᴰ x
    {-# REWRITE ⟦⟧-var #-}

    ⟦⟧-app : ⟦ app f a ⟧ᵗ ≡ appᴰ ⟦ f ⟧ᵗ ⟦ a ⟧ᵗ
    {-# REWRITE ⟦⟧-app #-}
    ⟦⟧-lam : ⟦ lam b ⟧ᵗ ≡ lamᴰ ⟦ b ⟧ᵗ
    {-# REWRITE ⟦⟧-lam #-}
