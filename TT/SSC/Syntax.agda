{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Syntax where

open import TT.Lib

private variable
  i i₀ i₁ j : ℕ

data Con : Set

postulate
  Ty : Con → ℕ → Set

infixl 2 _▹_
data Con where
  ◇ : Con
  _▹_ : (Γ : Con) → Ty Γ i → Con

private variable
  Γ Γ₀ Γ₁ Δ Δ₀ Δ₁ : Con
  A A₀ A₁ B B₀ B₁ : Ty Γ i

postulate
  Tm : (Γ : Con) → Ty Γ i → Set

data Sub : Con → Con → Set

infixl 9 _[_]ᵀ
postulate
  _[_]ᵀ : Ty Γ i → Sub Δ Γ → Ty Δ i

infixl 10 _⁺
data Sub where
  p : Sub (Γ ▹ A) Γ
  _⁺ : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A)
  ⟨_⟩ : Tm Γ A → Sub Γ (Γ ▹ A)

infixl 9 _[_]ᵗ
postulate
  _[_]ᵗ : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ)
  q : Tm (Γ ▹ A) (A [ p ]ᵀ)

private variable
  γ γ₀ γ₁ : Sub Δ Γ
  a a₀ a₁ b b₀ b₁ f f₀ f₁ α α₀ α₁ : Tm Γ A

opaque
  unfolding coe

  ap-Ty : Γ₀ ≡ Γ₁ → Ty Γ₀ i ≡ Ty Γ₁ i
  ap-Ty refl = refl

  ap-Ty₂ : Γ₀ ≡ Γ₁ → i₀ ≡ i₁ → Ty Γ₀ i₀ ≡ Ty Γ₁ i₁
  ap-Ty₂ refl refl = refl

  ap-Tm : (A₀₁ : A₀ ≡ A₁) → Tm Γ A₀ ≡ Tm Γ A₁
  ap-Tm refl = refl

  ap-Tm₂ : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → Tm Γ₀ A₀ ≡ Tm Γ₁ A₁
  ap-Tm₂ refl refl = refl

postulate
  p-⁺ᵀ : B [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ B [ γ ]ᵀ [ p ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ) j
  p-⁺ᵗ :
    b [ p ]ᵗ [ γ ⁺ ]ᵗ ≡[ ap-Tm p-⁺ᵀ ]
    b [ γ ]ᵗ [ p ]ᵗ ∈ Tm (Δ ▹ A [ γ ]ᵀ) (B [ γ ]ᵀ [ p ]ᵀ)
  q-⁺ : q [ γ ⁺ ]ᵗ ≡[ ap-Tm p-⁺ᵀ ] q ∈ Tm (Δ ▹ A [ γ ]ᵀ) (A [ γ ]ᵀ [ p ]ᵀ)

  p-⟨⟩ᵀ : B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B
  p-⟨⟩ᵗ : b [ p ]ᵗ [ ⟨ a ⟩ ]ᵗ ≡[ ap-Tm p-⟨⟩ᵀ ] b
  q-⟨⟩ : q [ ⟨ a ⟩ ]ᵗ ≡[ ap-Tm p-⟨⟩ᵀ ] a

  ⟨⟩-[]ᵀ : B [ ⟨ a ⟩ ]ᵀ [ γ ]ᵀ ≡ B [ γ ⁺ ]ᵀ [ ⟨ a [ γ ]ᵗ ⟩ ]ᵀ
  ▹-ηᵀ : B ≡ B [ p ⁺ ]ᵀ [ ⟨ q ⟩ ]ᵀ

postulate
  U : (i : ℕ) → Ty Γ (suc i)
  U-[] : U i [ γ ]ᵀ ≡ U i

  El : Tm Γ (U i) → Ty Γ i
  El-[] : El α [ γ ]ᵀ ≡ El (coe (ap-Tm U-[]) (α [ γ ]ᵗ))

  c : Ty Γ i → Tm Γ (U i)
  c-[] : c A [ γ ]ᵗ ≡[ ap-Tm U-[] ] c (A [ γ ]ᵀ)

  U-β : El (c A) ≡ A
  U-η : α ≡ c (El α)

postulate
  Π : (A : Ty Γ i) → Ty (Γ ▹ A) i → Ty Γ i
  Π-[] : Π A B [ γ ]ᵀ ≡ Π (A [ γ ]ᵀ) (B [ γ ⁺ ]ᵀ)

  app : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]ᵀ)
  app-[] :
    app f a [ γ ]ᵗ ≡[ ap-Tm ⟨⟩-[]ᵀ ]
    app (coe (ap-Tm Π-[]) (f [ γ ]ᵗ)) (a [ γ ]ᵗ)

  lam : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  lam-[] : lam b [ γ ]ᵗ ≡[ ap-Tm Π-[] ] lam (b [ γ ⁺ ]ᵗ)

ap-Π : B₀ ≡ B₁ → Π A B₀ ≡ Π A B₁
ap-Π refl = refl

postulate
  Π-β : app (lam b) a ≡ b [ ⟨ a ⟩ ]ᵗ
  Π-η : f ≡[ ap-Tm (ap-Π ▹-ηᵀ) ] lam (app (coe (ap-Tm Π-[]) (f [ p ]ᵗ)) q)

opaque
  unfolding coe

  ap-Sub : Δ₀ ≡ Δ₁ → Γ₀ ≡ Γ₁ → Sub Δ₀ Γ₀ ≡ Sub Δ₁ Γ₁
  ap-Sub refl refl = refl

  ap-[]ᵀ : A₀ ≡ A₁ → A₀ [ γ ]ᵀ ≡ A₁ [ γ ]ᵀ
  ap-[]ᵀ refl = refl

  ap-[]ᵀ₃ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → γ₀ ≡[ ap-Sub refl Γ₀₁ ] γ₁ →
    A₀ [ γ₀ ]ᵀ ≡ A₁ [ γ₁ ]ᵀ
  ap-[]ᵀ₃ refl refl refl = refl

  apᵈ-[]ᵀ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ →
    (Δ₀₁ : Δ₀ ≡ Δ₁) → γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁ →
    A₀ [ γ₀ ]ᵀ ≡[ ap-Ty Δ₀₁ ] A₁ [ γ₁ ]ᵀ
  apᵈ-[]ᵀ refl refl refl refl = refl

  apᵈ-[]ᵗ :
    (A₀₁ : A₀ ≡ A₁) →
    a₀ ≡[ ap-Tm A₀₁ ] a₁ → a₀ [ γ ]ᵗ ≡[ ap-Tm (ap-[]ᵀ A₀₁) ] a₁ [ γ ]ᵗ
  apᵈ-[]ᵗ refl refl = refl

  apᵈ-[]ᵗ₄ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) → a₀ ≡[ ap-Tm₂ Γ₀₁ A₀₁ ] a₁ →
    (γ₀₁ : γ₀ ≡[ ap-Sub refl Γ₀₁ ] γ₁) →
    a₀ [ γ₀ ]ᵗ ≡[ ap-Tm (ap-[]ᵀ₃ Γ₀₁ A₀₁ γ₀₁) ] a₁ [ γ₁ ]ᵗ
  apᵈ-[]ᵗ₄ refl refl refl refl = refl

  apᵈ-[]ᵗ₅ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) → a₀ ≡[ ap-Tm₂ Γ₀₁ A₀₁ ] a₁ →
    (Δ₀₁ : Δ₀ ≡ Δ₁) (γ₀₁ : γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁) →
    a₀ [ γ₀ ]ᵗ ≡[ ap-Tm₂ Δ₀₁ (apᵈ-[]ᵀ Γ₀₁ A₀₁ Δ₀₁ γ₀₁) ] a₁ [ γ₁ ]ᵗ
  apᵈ-[]ᵗ₅ refl refl refl refl refl = refl

  ap-▹ᵣ : A₀ ≡ A₁ → (Γ ▹ A₀) ≡ (Γ ▹ A₁)
  ap-▹ᵣ refl = refl

  ap-▹ : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → (Γ₀ ▹ A₀) ≡ (Γ₁ ▹ A₁)
  ap-▹ refl refl = refl

  apᵈ-p :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    p ≡[ ap-Sub (ap-▹ Γ₀₁ A₀₁) Γ₀₁ ] p
  apᵈ-p refl refl = refl

  apᵈ-q :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    q
      ≡[
        ap-Tm₂ (ap-▹ Γ₀₁ A₀₁) (apᵈ-[]ᵀ Γ₀₁ A₀₁ (ap-▹ Γ₀₁ A₀₁) (apᵈ-p Γ₀₁ A₀₁)) ]
    q
  apᵈ-q refl refl = refl

  apᵈ-⟨⟩ :
    (A₀₁ : A₀ ≡ A₁) →
    a₀ ≡[ ap-Tm A₀₁ ] a₁ → ⟨ a₀ ⟩ ≡[ ap-Sub refl (ap-▹ᵣ A₀₁) ] ⟨ a₁ ⟩
  apᵈ-⟨⟩ refl refl = refl

  apᵈ-⟨⟩₃ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    a₀ ≡[ ap-Tm₂ Γ₀₁ A₀₁ ] a₁ → ⟨ a₀ ⟩ ≡[ ap-Sub Γ₀₁ (ap-▹ Γ₀₁ A₀₁) ] ⟨ a₁ ⟩
  apᵈ-⟨⟩₃ refl refl refl = refl

  apᵈ-U : (Γ₀₁ : Γ₀ ≡ Γ₁) → U i ≡[ ap-Ty Γ₀₁ ] U i
  apᵈ-U refl = refl

  ap-El : α₀ ≡ α₁ → El α₀ ≡ El α₁
  ap-El refl = refl

  apᵈ-El :
    (Γ₀₁ : Γ₀ ≡ Γ₁) →
    α₀ ≡[ ap-Tm₂ Γ₀₁ (apᵈ-U Γ₀₁) ] α₁ → El α₀ ≡[ ap-Ty Γ₀₁ ] El α₁
  apᵈ-El refl refl = refl

  apᵈ-c :
    (Γ₀₁ : Γ₀ ≡ Γ₁) →
    A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → c A₀ ≡[ ap-Tm₂ Γ₀₁ (apᵈ-U Γ₀₁) ] c A₁
  apᵈ-c refl refl = refl

  apᵈ-Π :
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) → B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁ →
    Π A₀ B₀ ≡[ ap-Ty Γ₀₁ ] Π A₁ B₁
  apᵈ-Π refl refl refl = refl

  ap-app : f₀ ≡ f₁ → app f₀ a ≡ app f₁ a
  ap-app refl = refl

  apᵈ-app :
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) (B₀₁ : B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁) →
    f₀ ≡[ ap-Tm₂ Γ₀₁ (apᵈ-Π Γ₀₁ A₀₁ B₀₁) ] f₁ →
    (a₀₁ : a₀ ≡[ ap-Tm₂ Γ₀₁ A₀₁ ] a₁) →
    app f₀ a₀
      ≡[ ap-Tm₂ Γ₀₁ (apᵈ-[]ᵀ (ap-▹ Γ₀₁ A₀₁) B₀₁ Γ₀₁ (apᵈ-⟨⟩₃ Γ₀₁ A₀₁ a₀₁)) ]
    app f₁ a₁
  apᵈ-app refl refl refl refl refl = refl

  apᵈ-lam :
    (B₀₁ : B₀ ≡ B₁) → b₀ ≡[ ap-Tm B₀₁ ] b₁ → lam b₀ ≡[ ap-Tm (ap-Π B₀₁) ] lam b₁
  apᵈ-lam refl refl = refl

  apᵈ-lam₄ :
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) (B₀₁ : B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁) →
    b₀ ≡[ ap-Tm₂ (ap-▹ Γ₀₁ A₀₁) B₀₁ ] b₁ →
    lam b₀ ≡[ ap-Tm₂ Γ₀₁ (apᵈ-Π Γ₀₁ A₀₁ B₀₁) ] lam b₁
  apᵈ-lam₄ refl refl refl refl = refl
