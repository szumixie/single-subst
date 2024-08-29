{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.CwF.Syntax where

open import TT.Lib

private variable
  i i₀ i₁ : ℕ

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
  Γ Γ₀ Γ₁ Δ Δ₀ Δ₁ Θ Θ₀ Θ₁ : Con
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
  a a₀ a₁ b b₀ b₁ f f₀ f₁ α α₀ α₁ : Tm Γ A

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

  ap-[]ᵀ : A₀ ≡ A₁ → A₀ [ γ ]ᵀ ≡ A₁ [ γ ]ᵀ
  ap-[]ᵀ refl = refl

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

opaque
  unfolding coe

  ap-Subₗ : Δ₀ ≡ Δ₁ → Sub Δ₀ Γ ≡ Sub Δ₁ Γ
  ap-Subₗ refl = refl

  ap-Sub : Δ₀ ≡ Δ₁ → Γ₀ ≡ Γ₁ → Sub Δ₀ Γ₀ ≡ Sub Δ₁ Γ₁
  ap-Sub refl refl = refl

  postulate
    Sub-inj-Δ : Sub Δ₀ Γ₀ ≡ Sub Δ₁ Γ₁ → Δ₀ ≡ Δ₁
    Sub-inj-Γ : Sub Δ₀ Γ₀ ≡ Sub Δ₁ Γ₁ → Γ₀ ≡ Γ₁

  ap-∘ₗ : γ₀ ≡ γ₁ → γ₀ ∘ δ ≡ γ₁ ∘ δ
  ap-∘ₗ refl = refl

  ap-∘₃ :
    (Δ₀₁ : Δ₀ ≡ Δ₁) → γ₀ ≡[ ap-Subₗ Δ₀₁ ] γ₁ → δ₀ ≡[ ap-Sub refl Δ₀₁ ] δ₁ →
    γ₀ ∘ δ₀ ≡ γ₁ ∘ δ₁
  ap-∘₃ refl refl refl = refl

  apᵈ-∘ᵣ : (Θ₀₁ : Θ₀ ≡ Θ₁) → δ₀ ≡[ ap-Subₗ Θ₀₁ ] δ₁ → γ ∘ δ₀ ≡[ ap-Subₗ Θ₀₁ ] γ ∘ δ₁
  apᵈ-∘ᵣ refl refl = refl

  apᵈ-∘ :
    (Δ₀₁ : Δ₀ ≡ Δ₁) (Γ₀₁ : Γ₀ ≡ Γ₁) → γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁ →
    (Θ₀₁ : Θ₀ ≡ Θ₁) → δ₀ ≡[ ap-Sub Θ₀₁ Δ₀₁ ] δ₁ →
    γ₀ ∘ δ₀ ≡[ ap-Sub Θ₀₁ Γ₀₁ ] γ₁ ∘ δ₁
  apᵈ-∘ refl refl refl refl refl = refl

  apᵈ-id : (Γ₀₁ : Γ₀ ≡ Γ₁) → id ≡[ ap-Sub Γ₀₁ Γ₀₁ ] id
  apᵈ-id refl = refl

  ap-Ty : Γ₀ ≡ Γ₁ → Ty Γ₀ i ≡ Ty Γ₁ i
  ap-Ty refl = refl

  ap-Ty₂ : Γ₀ ≡ Γ₁ → i₀ ≡ i₁ → Ty Γ₀ i₀ ≡ Ty Γ₁ i₁
  ap-Ty₂ refl refl = refl

  postulate
    Ty-inj-Γ : Ty Γ₀ i₀ ≡ Ty Γ₁ i₁ → Γ₀ ≡ Γ₁
    Ty-inj-i : Ty Γ₀ i₀ ≡ Ty Γ₁ i₁ → i₀ ≡ i₁

  apᵈ-[]ᵀᵣ :
    (Δ₀₁ : Δ₀ ≡ Δ₁) → γ₀ ≡[ ap-Subₗ Δ₀₁ ] γ₁ →
    A [ γ₀ ]ᵀ ≡[ ap-Ty Δ₀₁ ] A [ γ₁ ]ᵀ
  apᵈ-[]ᵀᵣ refl refl = refl

  apᵈ-[]ᵀ₃ :
    A₀ ≡ A₁ → (Δ₀₁ : Δ₀ ≡ Δ₁) → γ₀ ≡[ ap-Subₗ Δ₀₁ ] γ₁ →
    A₀ [ γ₀ ]ᵀ ≡[ ap-Ty Δ₀₁ ] A₁ [ γ₁ ]ᵀ
  apᵈ-[]ᵀ₃ refl refl refl = refl

  apᵈ-[]ᵀ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ →
    (Δ₀₁ : Δ₀ ≡ Δ₁) → γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁ →
    A₀ [ γ₀ ]ᵀ ≡[ ap-Ty Δ₀₁ ] A₁ [ γ₁ ]ᵀ
  apᵈ-[]ᵀ refl refl refl refl = refl

  ap-Tm₂ : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → Tm Γ₀ A₀ ≡ Tm Γ₁ A₁
  ap-Tm₂ refl refl = refl

  ap-Tm₃ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (i₀₁ : i₀ ≡ i₁) →
    A₀ ≡[ ap-Ty₂ Γ₀₁ i₀₁ ] A₁ → Tm Γ₀ A₀ ≡ Tm Γ₁ A₁
  ap-Tm₃ refl refl refl = refl

  postulate
    Tm-inj-Γ : Tm Γ₀ A₀ ≡ Tm Γ₁ A₁ → Γ₀ ≡ Γ₁
    Tm-inj-i : {A₀ : Ty Γ₀ i₀} {A₁ : Ty Γ₁ i₁} → Tm Γ₀ A₀ ≡ Tm Γ₁ A₁ → i₀ ≡ i₁
    Tm-inj-A :
      (e : Tm Γ₀ A₀ ≡ Tm Γ₁ A₁) → A₀ ≡[ ap-Ty₂ (Tm-inj-Γ e) (Tm-inj-i e) ] A₁

  apᵈ-[]ᵗᵣ : (γ₀₁ : γ₀ ≡ γ₁) → a [ γ₀ ]ᵗ ≡[ ap-Tm (ap-[]ᵀᵣ γ₀₁) ] a [ γ₁ ]ᵗ
  apᵈ-[]ᵗᵣ refl = refl

  apᵈ-[]ᵗ₄ :
    (A₀₁ : A₀ ≡ A₁) → a₀ ≡[ ap-Tm A₀₁ ] a₁ →
    (Δ₀₁ : Δ₀ ≡ Δ₁) (γ₀₁ : γ₀ ≡[ ap-Subₗ Δ₀₁ ] γ₁) →
    a₀ [ γ₀ ]ᵗ ≡[ ap-Tm₂ Δ₀₁ (apᵈ-[]ᵀ₃ A₀₁ Δ₀₁ γ₀₁) ] a₁ [ γ₁ ]ᵗ
  apᵈ-[]ᵗ₄ refl refl refl refl = refl

  apᵈ-[]ᵗ₅ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) → a₀ ≡[ ap-Tm₂ Γ₀₁ A₀₁ ] a₁ →
    (Δ₀₁ : Δ₀ ≡ Δ₁) (γ₀₁ : γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁) →
    a₀ [ γ₀ ]ᵗ ≡[ ap-Tm₂ Δ₀₁ (apᵈ-[]ᵀ Γ₀₁ A₀₁ Δ₀₁ γ₀₁) ] a₁ [ γ₁ ]ᵗ
  apᵈ-[]ᵗ₅ refl refl refl refl refl = refl

  apᵈ-ε : (Γ₀₁ : Γ₀ ≡ Γ₁) → ε ≡[ ap-Subₗ Γ₀₁ ] ε
  apᵈ-ε refl = refl

  ap-▹ᵣ : A₀ ≡ A₁ → (Γ ▹ A₀) ≡ (Γ ▹ A₁)
  ap-▹ᵣ refl = refl

  ap-▹ : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → (Γ₀ ▹ A₀) ≡ (Γ₁ ▹ A₁)
  ap-▹ refl refl = refl

  apᵈ-p : (A₀₁ : A₀ ≡ A₁) → p ≡[ ap-Subₗ (ap-▹ᵣ A₀₁) ] p
  apᵈ-p refl = refl

  apᵈ-p₂ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    p ≡[ ap-Sub (ap-▹ Γ₀₁ A₀₁) Γ₀₁ ] p
  apᵈ-p₂ refl refl = refl

  apᵈ-q :
    (A₀₁ : A₀ ≡ A₁) →
    q ≡[ ap-Tm₂ (ap-▹ᵣ A₀₁) (apᵈ-[]ᵀ₃ A₀₁ (ap-▹ᵣ A₀₁) (apᵈ-p A₀₁)) ] q
  apᵈ-q refl = refl

  apᵈ-q₂ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    q
      ≡[
        ap-Tm₂
          (ap-▹ Γ₀₁ A₀₁)
          (apᵈ-[]ᵀ Γ₀₁ A₀₁ (ap-▹ Γ₀₁ A₀₁) (apᵈ-p₂ Γ₀₁ A₀₁)) ]
    q
  apᵈ-q₂ refl refl = refl

  apᵈ-, :
    (Δ₀₁ : Δ₀ ≡ Δ₁) (γ₀₁ : γ₀ ≡[ ap-Subₗ Δ₀₁ ] γ₁) →
    a₀ ≡[ ap-Tm₂ Δ₀₁ (apᵈ-[]ᵀᵣ Δ₀₁ γ₀₁) ] a₁ →
    (γ₀ , a₀) ≡[ ap-Subₗ Δ₀₁ ] (γ₁ , a₁)
  apᵈ-, refl refl refl = refl

  apᵈ-,₅ :
    (Δ₀₁ : Δ₀ ≡ Δ₁) (Γ₀₁ : Γ₀ ≡ Γ₁) (γ₀₁ : γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁) →
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    a₀ ≡[ ap-Tm₂ Δ₀₁ (apᵈ-[]ᵀ Γ₀₁ A₀₁ Δ₀₁ γ₀₁) ] a₁ →
    (γ₀ , a₀) ≡[ ap-Sub Δ₀₁ (ap-▹ Γ₀₁ A₀₁) ] (γ₁ , a₁)
  apᵈ-,₅ refl refl refl refl refl = refl

  apᵈ-⁺ : (A₀₁ : A₀ ≡ A₁) → γ ⁺ ≡[ ap-Sub (ap-▹ᵣ (ap-[]ᵀ A₀₁)) (ap-▹ᵣ A₀₁) ] γ ⁺
  apᵈ-⁺ refl = refl

  apᵈ-⟨⟩ :
    (A₀₁ : A₀ ≡ A₁) →
    a₀ ≡[ ap-Tm A₀₁ ] a₁ → ⟨ a₀ ⟩ ≡[ ap-Sub refl (ap-▹ᵣ A₀₁) ] ⟨ a₁ ⟩
  apᵈ-⟨⟩ refl refl = refl

  apᵈ-⟨⟩₃ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    a₀ ≡[ ap-Tm₂ Γ₀₁ A₀₁ ] a₁ → ⟨ a₀ ⟩ ≡[ ap-Sub Γ₀₁ (ap-▹ Γ₀₁ A₀₁) ] ⟨ a₁ ⟩
  apᵈ-⟨⟩₃ refl refl refl = refl

⁺-⟨⟩ : γ ⁺ ∘ ⟨ a ⟩ ≡ (γ , a)
⁺-⟨⟩ =
  ,-∘ ∙
  ap-,
    (sym assoc ∙ ap-∘ᵣ ▹-β₁ ∙ idr)
    (splitl (apᵈ-[]ᵗ []ᵀ-∘ (splitl reflᵈ) ∙ᵈ merger ▹-β₂))

⁺-∘ :
  (γ ∘ δ) ⁺ ≡[ ap-Subₗ (ap-▹ᵣ []ᵀ-∘) ]
  γ ⁺ ∘ δ ⁺ ∈ Sub (Θ ▹ A [ γ ]ᵀ [ δ ]ᵀ) (Γ ▹ A)
⁺-∘ =
  apᵈ-,
    (ap-▹ᵣ []ᵀ-∘)
    ( dep (sym assoc) ∙ᵈ
      apᵈ-∘ᵣ
        (ap-▹ᵣ []ᵀ-∘)
        (apᵈ-∘ᵣ (ap-▹ᵣ []ᵀ-∘) (apᵈ-p []ᵀ-∘) ∙ᵈ dep (sym ▹-β₁)) ∙ᵈ
      dep assoc)
    (splitlr
      ( symᵈ (merger {A₂₁ = ap-Tm (ap-[]ᵀ []ᵀ-∘ ∙ sym []ᵀ-∘)} ▹-β₂) ∙ᵈ
        apᵈ-[]ᵗ₄
          (sym []ᵀ-∘)
          refl
          (ap-▹ᵣ []ᵀ-∘)
          (apᵈ-,
            (ap-▹ᵣ []ᵀ-∘)
            (apᵈ-∘ᵣ (ap-▹ᵣ []ᵀ-∘) (apᵈ-p []ᵀ-∘))
            (splitlr (apᵈ-q []ᵀ-∘))))) ∙ᵈ
  dep (sym ,-∘)

⁺-id : id ⁺ ≡[ ap-Subₗ (ap-▹ᵣ []ᵀ-id) ] id ∈ Sub (Γ ▹ A) (Γ ▹ A)
⁺-id =
  apᵈ-, (ap-▹ᵣ []ᵀ-id) (dep idl ∙ᵈ apᵈ-p []ᵀ-id) (splitl (apᵈ-q []ᵀ-id)) ∙ᵈ
  dep (sym ▹-η)

opaque
  unfolding coe

  apᵈ-U : (Γ₀₁ : Γ₀ ≡ Γ₁) → U i ≡[ ap-Ty Γ₀₁ ] U i
  apᵈ-U refl = refl

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
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) (B₀₁ : B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁) →
    b₀ ≡[ ap-Tm₂ (ap-▹ Γ₀₁ A₀₁) B₀₁ ] b₁ →
    lam b₀ ≡[ ap-Tm₂ Γ₀₁ (apᵈ-Π Γ₀₁ A₀₁ B₀₁) ] lam b₁
  apᵈ-lam refl refl refl refl = refl
