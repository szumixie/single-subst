{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check #-}

module TT.SSC where

open import TT.Lib

infixl 2 _▹_
infixl 9 _[_]ᵀ _[_]ᵗ
infixl 10 _⁺

private variable
  i j : ℕ

data Con : Set

postulate
  Ty : Con → ℕ → Set

data Con where
  ◇ : Con
  _▹_ : (Γ : Con) → Ty Γ i → Con

private variable
  Γ Γ₀ Γ₁ Δ Δ₀ Δ₁ : Con
  A A₀ A₁ B : Ty Γ i

postulate
  Tm : (Γ : Con) → Ty Γ i → Set

data Sub : Con → Con → Set

postulate
  _[_]ᵀ : Ty Γ i → Sub Δ Γ → Ty Δ i

data Sub where
  p : Sub (Γ ▹ A) Γ
  _⁺ : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A)
  ⟨_⟩ : Tm Γ A → Sub Γ (Γ ▹ A)

postulate
  _[_]ᵗ : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ)
  q     : Tm (Γ ▹ A) (A [ p ]ᵀ)

private variable
  γ γ₀ γ₁ : Sub Δ Γ
  a a₀ a₁ b f α : Tm Γ A

opaque
  unfolding coe

  ap-Ty : Γ₀ ≡ Γ₁ → Ty Γ₀ i ≡ Ty Γ₁ i
  ap-Ty refl = refl

  ap-Tm : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → Tm Γ₀ A₀ ≡ Tm Γ₁ A₁
  ap-Tm refl refl = refl

postulate
  q-⁺ :
    (e : A [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ A [ γ ]ᵀ [ p ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ) i) →
    q [ γ ⁺ ]ᵗ ≡[ ap-Tm refl (dep e) ] q ∈ Tm (Δ ▹ A [ γ ]ᵀ) (A [ γ ]ᵀ [ p ]ᵀ)
  p-⁺ :
    (e : B [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ B [ γ ]ᵀ [ p ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ) i) →
    a [ p ]ᵗ [ γ ⁺ ]ᵗ ≡[ ap-Tm refl (dep e) ]
    a [ γ ]ᵗ [ p ]ᵗ ∈ Tm (Δ ▹ A [ γ ]ᵀ) (B [ γ ]ᵀ [ p ]ᵀ)
  q-⟨⟩ : (e : A [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ A) → q [ ⟨ a ⟩ ]ᵗ ≡[ ap-Tm refl (dep e) ] a
  p-⟨⟩ : (e : B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B) → b [ p ]ᵗ [ ⟨ a ⟩ ]ᵗ ≡[ ap-Tm refl (dep e) ] b

postulate
  U : (i : ℕ) → Ty Γ (suc i)
  U-[] : U i [ γ ]ᵀ ≡ U i

  El : Tm Γ (U i) → Ty Γ i
  El-[] : El α [ γ ]ᵀ ≡ El (coe (ap-Tm refl (dep U-[])) (α [ γ ]ᵗ))

  c : Ty Γ i → Tm Γ (U i)
  c-[] : c A [ γ ]ᵗ ≡[ ap-Tm refl (dep U-[]) ] c (A [ γ ]ᵀ)

  U-β : El (c A) ≡ A
  U-η : α ≡ c (El α)

  Π : (A : Ty Γ i) → Ty (Γ ▹ A) i → Ty Γ i
  Π-[] : Π A B [ γ ]ᵀ ≡ Π (A [ γ ]ᵀ) (B [ γ ⁺ ]ᵀ)

  app : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]ᵀ)
  app-[] :
    (e : B [ ⟨ a ⟩ ]ᵀ [ γ ]ᵀ ≡ B [ γ ⁺ ]ᵀ [ ⟨ a [ γ ]ᵗ ⟩ ]ᵀ) →
    app f a [ γ ]ᵗ ≡[ ap-Tm refl (dep e) ]
    app (coe (ap-Tm refl (dep Π-[])) (f [ γ ]ᵗ)) (a [ γ ]ᵗ)

  lam : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  lam-[] : lam b [ γ ]ᵗ ≡[ ap-Tm refl (dep Π-[]) ] lam (b [ γ ⁺ ]ᵗ)

  Π-β : app (lam b) a ≡ b [ ⟨ a ⟩ ]ᵗ
  Π-η : (e : B ≡ B [ p ⁺ ]ᵀ [ ⟨ q ⟩ ]ᵀ) →
    f ≡
    lam
      (coe (ap-Tm refl (dep (sym e)))
        (app (coe (ap-Tm refl (dep Π-[])) (f [ p ]ᵗ)) q))

opaque
  unfolding coe

  ap-Sub : Δ₀ ≡ Δ₁ → Γ₀ ≡ Γ₁ → Sub Δ₀ Γ₀ ≡ Sub Δ₁ Γ₁
  ap-Sub refl refl = refl

  ap-[]ᵀ : A₀ ≡ A₁ → A₀ [ γ ]ᵀ ≡ A₁ [ γ ]ᵀ
  ap-[]ᵀ refl = refl

  apᵈ-[]ᵀ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (Δ₀₁ : Δ₀ ≡ Δ₁) →
    A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁ →
    A₀ [ γ₀ ]ᵀ ≡[ ap-Ty Δ₀₁ ] A₁ [ γ₁ ]ᵀ
  apᵈ-[]ᵀ refl refl refl refl = refl

  ap-[]ᵗ : a₀ ≡ a₁ → a₀ [ γ ]ᵗ ≡ a₁ [ γ ]ᵗ
  ap-[]ᵗ refl = refl

  apᵈ-[]ᵗ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (Δ₀₁ : Δ₀ ≡ Δ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    a₀ ≡[ ap-Tm Γ₀₁ A₀₁ ] a₁ → (γ₀₁ : γ₀ ≡[ ap-Sub Δ₀₁ Γ₀₁ ] γ₁) →
    a₀ [ γ₀ ]ᵗ ≡[ ap-Tm Δ₀₁ (apᵈ-[]ᵀ Γ₀₁ Δ₀₁ A₀₁ γ₀₁) ] a₁ [ γ₁ ]ᵗ
  apᵈ-[]ᵗ refl refl refl refl refl = refl

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
        ap-Tm (ap-▹ Γ₀₁ A₀₁) (apᵈ-[]ᵀ Γ₀₁ (ap-▹ Γ₀₁ A₀₁) A₀₁ (apᵈ-p Γ₀₁ A₀₁)) ]
    q
  apᵈ-q refl refl = refl

private
  module Util
    (Conᴹ : Con → Set) (Tyᴹ : ∀ {Γ} → Conᴹ Γ → (i : ℕ) → Ty Γ i → Set)
    where
    ap-Tyᴹ : {Γᴹ : Conᴹ Γ} → A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ ≡ Tyᴹ Γᴹ i A₁
    ap-Tyᴹ refl = refl

    module _ (Tmᴹ : ∀ {Γ A} (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set) where
      opaque
        unfolding coe

        ap-Tmᴹ :
          {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁}
          (A₀₁ : A₀ ≡ A₁) →
          Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
          a₀ ≡[ ap-Tm refl (dep A₀₁) ] a₁ →
          Tmᴹ Γᴹ Aᴹ₀ a₀ ≡ Tmᴹ Γᴹ Aᴹ₁ a₁
        ap-Tmᴹ refl refl refl = refl

record DModel : Set₁ where
  no-eta-equality
  infixl 2 _▹ᴹ_
  infixl 9 _[_]ᵀᴹ _[_]ᵗᴹ
  infixl 10 _⁺ᴹ

  field
    Conᴹ : Con → Set
    Subᴹ : Conᴹ Δ → Conᴹ Γ → Sub Δ Γ → Set

    Tyᴹ : Conᴹ Γ → (i : ℕ) → Ty Γ i → Set
    _[_]ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} →
      Tyᴹ Γᴹ i A → Subᴹ Δᴹ Γᴹ γ → Tyᴹ Δᴹ i (A [ γ ]ᵀ)

    Tmᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set
    _[_]ᵗᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} →
      Tmᴹ Γᴹ Aᴹ a → (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Tmᴹ Δᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (a [ γ ]ᵗ)

    ◇ᴹ : Conᴹ ◇
    _▹ᴹ_ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Conᴹ (Γ ▹ A)
    pᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Subᴹ (Γᴹ ▹ᴹ Aᴹ) Γᴹ p

  ap-Tyᴹ : {Γᴹ : Conᴹ Γ} → A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ ≡ Tyᴹ Γᴹ i A₁
  ap-Tyᴹ = Util.ap-Tyᴹ Conᴹ Tyᴹ

  ap-Tmᴹ :
    {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁}
    (A₀₁ : A₀ ≡ A₁) →
    Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
    a₀ ≡[ ap-Tm refl (dep A₀₁) ] a₁ →
    Tmᴹ Γᴹ Aᴹ₀ a₀ ≡ Tmᴹ Γᴹ Aᴹ₁ a₁
  ap-Tmᴹ = Util.ap-Tmᴹ Conᴹ Tyᴹ Tmᴹ

  field
    qᴹ  : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Tmᴹ (Γᴹ ▹ᴹ Aᴹ) (Aᴹ [ pᴹ ]ᵀᴹ) q
    _⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A}
      (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Subᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Γᴹ ▹ᴹ Aᴹ) (γ ⁺)
    q-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ}
      (e : A [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ A [ γ ]ᵀ [ p ]ᵀ)
      (eᴹ : Aᴹ [ pᴹ ]ᵀᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ e ] Aᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) →
      qᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ e eᴹ (q-⁺ e) ]
      qᴹ ∈ Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Aᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) q
    p-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {bᴹ : Tmᴹ Γᴹ Bᴹ b} {γᴹ : Subᴹ Δᴹ Γᴹ γ}
      (e : B [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ B [ γ ]ᵀ [ p ]ᵀ)
      (eᴹ : Bᴹ [ pᴹ ]ᵀᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ e ] Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) →
      bᴹ [ pᴹ ]ᵗᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ e eᴹ (p-⁺ e) ]
      bᴹ [ γᴹ ]ᵗᴹ [ pᴹ ]ᵗᴹ
        ∈ Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (b [ γ ]ᵗ [ p ]ᵗ)
    ⟨_⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Tmᴹ Γᴹ Aᴹ a → Subᴹ Γᴹ (Γᴹ ▹ᴹ Aᴹ) ⟨ a ⟩
    q-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {aᴹ : Tmᴹ Γᴹ Aᴹ a}
      (e : A [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ A)
      (eᴹ : Aᴹ [ pᴹ ]ᵀᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ e ] Aᴹ) →
      qᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ e eᴹ (q-⟨⟩ e) ] aᴹ
    p-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {bᴹ : Tmᴹ Γᴹ Bᴹ b} {aᴹ : Tmᴹ Γᴹ Aᴹ a}
      (e : B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B)
      (eᴹ : Bᴹ [ pᴹ ]ᵀᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ e ] Bᴹ) →
      bᴹ [ pᴹ ]ᵗᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ e eᴹ (p-⟨⟩ e) ] bᴹ

  field
    Uᴹ : {Γᴹ : Conᴹ Γ} (i : ℕ) → Tyᴹ Γᴹ (suc i) (U i)
    U-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      Uᴹ i [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ U-[] ] Uᴹ i

    Elᴹ : {Γᴹ : Conᴹ Γ} → Tmᴹ Γᴹ (Uᴹ i) α → Tyᴹ Γᴹ i (El α)
    El-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {αᴹ : Tmᴹ Γᴹ (Uᴹ i) α} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      Elᴹ αᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ El-[] ]
      Elᴹ (coe (ap-Tmᴹ U-[] U-[]ᴹ refl) (αᴹ [ γᴹ ]ᵗᴹ))

    cᴹ : {Γᴹ : Conᴹ Γ} → Tyᴹ Γᴹ i A → Tmᴹ Γᴹ (Uᴹ i) (c A)
    c-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      cᴹ Aᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ U-[] U-[]ᴹ c-[] ] cᴹ (Aᴹ [ γᴹ ]ᵀᴹ)

    U-βᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Elᴹ (cᴹ Aᴹ) ≡[ ap-Tyᴹ U-β ] Aᴹ
    U-ηᴹ :
      {Γᴹ : Conᴹ Γ} {αᴹ : Tmᴹ Γᴹ (Uᴹ i) α} →
      αᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep U-η) ] cᴹ (Elᴹ αᴹ)

    Πᴹ : {Γᴹ : Conᴹ Γ} (Aᴹ : Tyᴹ Γᴹ i A) → Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B → Tyᴹ Γᴹ i (Π A B)
    Π-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      Πᴹ Aᴹ Bᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ Π-[] ] Πᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ)

    appᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B} →
      Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f →
      (aᴹ : Tmᴹ Γᴹ Aᴹ a) → Tmᴹ Γᴹ (Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ) (app f a)
    app-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ}
      (e : B [ ⟨ a ⟩ ]ᵀ [ γ ]ᵀ ≡ B [ γ ⁺ ]ᵀ [ ⟨ a [ γ ]ᵗ ⟩ ]ᵀ)
      (eᴹ : Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ e ] Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ aᴹ [ γᴹ ]ᵗᴹ ⟩ᴹ ]ᵀᴹ) →
      appᴹ fᴹ aᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ e eᴹ (app-[] e) ]
      appᴹ (coe (ap-Tmᴹ Π-[] Π-[]ᴹ refl) (fᴹ [ γᴹ ]ᵗᴹ)) (aᴹ [ γᴹ ]ᵗᴹ)

    lamᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B} →
      Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (lam b)
    lam-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {bᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      lamᴹ bᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ Π-[] Π-[]ᴹ lam-[] ] lamᴹ (bᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ)

    Π-βᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {bᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      appᴹ (lamᴹ bᴹ) aᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep Π-β) ] bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ
    Π-ηᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f}
      (e : B ≡ B [ p ⁺ ]ᵀ [ ⟨ q ⟩ ]ᵀ)
      (eᴹ : Bᴹ ≡[ ap-Tyᴹ e ] Bᴹ [ pᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ qᴹ ⟩ᴹ ]ᵀᴹ) →
      fᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep (Π-η e)) ]
      lamᴹ
        (coe (ap-Tmᴹ (sym e) (symᵈ eᴹ) refl)
          (appᴹ (coe (ap-Tmᴹ Π-[] Π-[]ᴹ refl) (fᴹ [ pᴹ ]ᵗᴹ)) qᴹ))

module Ind (M : DModel) where
  open DModel M

  ⟦_⟧ᶜ : (Γ : Con) → Conᴹ Γ

  postulate
    ⟦_⟧ᵀ : (A : Ty Γ i) → Tyᴹ ⟦ Γ ⟧ᶜ i A

  ⟦ ◇ ⟧ᶜ = ◇ᴹ
  ⟦ Γ ▹ A ⟧ᶜ = ⟦ Γ ⟧ᶜ ▹ᴹ ⟦ A ⟧ᵀ

  postulate
    ⟦_⟧ᵗ : (a : Tm Γ A) → Tmᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ a

  ⟦_⟧ˢ : (γ : Sub Δ Γ) → Subᴹ ⟦ Δ ⟧ᶜ ⟦ Γ ⟧ᶜ γ

  postulate
    ⟦⟧-[]ᵀ : ⟦ A [ γ ]ᵀ ⟧ᵀ ↝ ⟦ A ⟧ᵀ [ ⟦ γ ⟧ˢ ]ᵀᴹ
    {-# REWRITE ⟦⟧-[]ᵀ #-}

  ⟦ p ⟧ˢ = pᴹ
  ⟦ γ ⁺ ⟧ˢ = ⟦ γ ⟧ˢ ⁺ᴹ
  ⟦ ⟨ a ⟩ ⟧ˢ = ⟨ ⟦ a ⟧ᵗ ⟩ᴹ

  postulate
    ⟦⟧-q   : ⟦ q {Γ}{_}{A} ⟧ᵗ ↝ qᴹ
    ⟦⟧-[]ᵗ : ⟦ a [ γ ]ᵗ ⟧ᵗ ↝ ⟦ a ⟧ᵗ [ ⟦ γ ⟧ˢ ]ᵗᴹ
    {-# REWRITE ⟦⟧-[]ᵗ ⟦⟧-q #-}

  postulate
    ⟦⟧-U : ⟦ U i ⟧ᵀ ↝ Uᴹ i ∈ Tyᴹ ⟦ Γ ⟧ᶜ (suc i) (U i)
    {-# REWRITE ⟦⟧-U #-}
    ⟦⟧-El : ⟦ El α ⟧ᵀ ↝ Elᴹ ⟦ α ⟧ᵗ
    {-# REWRITE ⟦⟧-El #-}
    ⟦⟧-c : ⟦ c A ⟧ᵗ ↝ cᴹ ⟦ A ⟧ᵀ
    {-# REWRITE ⟦⟧-c #-}

    ⟦⟧-Π : ⟦ Π A B ⟧ᵀ ↝ Πᴹ ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
    {-# REWRITE ⟦⟧-Π #-}
    ⟦⟧-app : ⟦ app f a ⟧ᵗ ↝ appᴹ ⟦ f ⟧ᵗ ⟦ a ⟧ᵗ
    {-# REWRITE ⟦⟧-app #-}
    ⟦⟧-lam : ⟦ lam b ⟧ᵗ ↝ lamᴹ ⟦ b ⟧ᵗ
    {-# REWRITE ⟦⟧-lam #-}

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
