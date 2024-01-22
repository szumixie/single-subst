{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check #-}

module TT.CwF.Syntax where

open import TT.Lib

private variable
  i : ℕ

data Con : Set

postulate
  Ty : Con → ℕ → Set

infixl 2 _▹_
data Con where
  ◇ : Con
  _▹_ : (Γ : Con) → Ty Γ i → Con

postulate
  Sub : Con → Con → Set

private variable
  Γ Δ Θ : Con
  γ γ₀ γ₁ δ δ₀ δ₁ θ : Sub Δ Γ
  A A₀ A₁ B B₀ B₁ : Ty Γ i

infixl 9 _∘_
postulate
  _∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  assoc : γ ∘ (δ ∘ θ) ≡ (γ ∘ δ) ∘ θ

  id : Sub Γ Γ
  idr : γ ∘ id ≡ γ
  idl : id ∘ γ ≡ γ

infixl 9 _[_]ᵀ
postulate
  _[_]ᵀ : Ty Γ i → Sub Δ Γ → Ty Δ i
  []ᵀ-∘ : A [ γ ∘ δ ]ᵀ ≡ A [ γ ]ᵀ [ δ ]ᵀ
  []ᵀ-id : A [ id ]ᵀ ≡ A

postulate
  Tm : (Γ : Con) → Ty Γ i → Set

private variable
  a a₀ a₁ b f α : Tm Γ A

ap-[]ᵀ : A₀ ≡ A₁ → A₀ [ γ ]ᵀ ≡ A₁ [ γ ]ᵀ
ap-[]ᵀ refl = refl

ap-[]ᵀᵣ : γ₀ ≡ γ₁ → A [ γ₀ ]ᵀ ≡ A [ γ₁ ]ᵀ
ap-[]ᵀᵣ refl = refl

ap-Tm : A₀ ≡ A₁ → Tm Γ A₀ ≡ Tm Γ A₁
ap-Tm refl = refl

infixl 9 _[_]ᵗ
postulate
  _[_]ᵗ : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ)
  []ᵗ-∘ : a [ γ ∘ δ ]ᵗ ≡[ ap-Tm []ᵀ-∘ ] a [ γ ]ᵗ [ δ ]ᵗ
  []ᵗ-id : a [ id ]ᵗ ≡[ ap-Tm []ᵀ-id ] a

infixl 4 _,_
postulate
  ε : Sub Δ ◇
  ε-∘ : ε ∘ γ ≡ ε
  ◇-η : id ≡ ε

  p : Sub (Γ ▹ A) Γ
  q : Tm (Γ ▹ A) (A [ p ]ᵀ)

  _,_ : (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ) → Sub Δ (Γ ▹ A)
  ,-∘ : (γ , a) ∘ δ ≡ (γ ∘ δ , coe (ap-Tm (sym []ᵀ-∘)) (a [ δ ]ᵗ))

  ▹-β₁ : p ∘ (γ , a) ≡ γ
  ▹-β₂ : q [ γ , a ]ᵗ ≡[ ap-Tm (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ▹-β₁) ] a
  ▹-η : id ≡ (p , q) ∈ Sub (Γ ▹ A) (Γ ▹ A)

opaque
  unfolding coe

  ap-∘ᵣ : (δ₀₁ : δ₀ ≡ δ₁) → γ ∘ δ₀ ≡ γ ∘ δ₁
  ap-∘ᵣ refl = refl

  apᵈ-[]ᵗ :
    (A₀₁ : A₀ ≡ A₁) →
    a₀ ≡[ ap-Tm A₀₁ ] a₁ → a₀ [ γ ]ᵗ ≡[ ap-Tm (ap-[]ᵀ A₀₁) ] a₁ [ γ ]ᵗ
  apᵈ-[]ᵗ refl refl = refl

  ap-, :
    (γ₀₁ : γ₀ ≡ γ₁) → a₀ ≡[ ap-Tm (ap-[]ᵀᵣ γ₀₁) ] a₁ → (γ₀ , a₀) ≡ (γ₁ , a₁)
  ap-, refl refl = refl

infixl 10 _⁺
_⁺ : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A)
γ ⁺ = γ ∘ p , coe (ap-Tm (sym []ᵀ-∘)) q

⟨_⟩ : Tm Γ A → Sub Γ (Γ ▹ A)
⟨ a ⟩ = id , coe (ap-Tm (sym []ᵀ-id)) a

⟨⟩-∘ : ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]ᵗ ⟩
⟨⟩-∘ =
  ,-∘ ∙
  ap-,
    (idl ∙ sym idr ∙ ap-∘ᵣ (sym ▹-β₁) ∙ assoc)
    (splitlr
      ( apᵈ-[]ᵗ []ᵀ-id (splitl reflᵈ) ∙ᵈ
        symᵈ (merger ▹-β₂) ∙ᵈ
        apᵈ-[]ᵗ (sym []ᵀ-∘) refl)) ∙
  sym ,-∘

▹-η′ : id ≡ p ⁺ ∘ ⟨ q ⟩ ∈ Sub (Γ ▹ A) (Γ ▹ A)
▹-η′ =
  ▹-η ∙
  ap-,
    (sym idr ∙ ap-∘ᵣ (sym ▹-β₁) ∙ assoc)
    (splitr (symᵈ (merger ▹-β₂) ∙ᵈ apᵈ-[]ᵗ (sym []ᵀ-∘) refl)) ∙
  sym ,-∘

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
    app f a [ γ ]ᵗ ≡[ ap-Tm (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ⟨⟩-∘ ∙ []ᵀ-∘) ]
    app (coe (ap-Tm Π-[]) (f [ γ ]ᵗ)) (a [ γ ]ᵗ)

  lam : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  lam-[] : lam b [ γ ]ᵗ ≡[ ap-Tm Π-[] ] lam (b [ γ ⁺ ]ᵗ)

ap-Π : B₀ ≡ B₁ → Π A B₀ ≡ Π A B₁
ap-Π refl = refl

postulate
  Π-β : app (lam b) a ≡ b [ ⟨ a ⟩ ]ᵗ
  Π-η :
    f ≡[ ap-Tm (ap-Π (sym []ᵀ-id ∙ ap-[]ᵀᵣ ▹-η′ ∙ []ᵀ-∘)) ]
    lam (app (coe (ap-Tm Π-[]) (f [ p ]ᵗ)) q)
