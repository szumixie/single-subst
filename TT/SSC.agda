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
  A A₀ A₁ B B₀ B₁ : Ty Γ i

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

data Var : (Γ : Con) → Ty Γ i → Set where
  vz : Var (Γ ▹ A) (A [ p ]ᵀ)
  vs : Var Γ B → Var (Γ ▹ A) (B [ p ]ᵀ)

private variable
  γ γ₀ γ₁ : Sub Δ Γ
  a a₀ a₁ b b₀ b₁ f f₀ f₁ α α₀ α₁ : Tm Γ A
  x x₀ x₁ : Var Γ A

opaque
  unfolding coe

  ap-Ty : Γ₀ ≡ Γ₁ → Ty Γ₀ i ≡ Ty Γ₁ i
  ap-Ty refl = refl

  ap-Tm : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → Tm Γ₀ A₀ ≡ Tm Γ₁ A₁
  ap-Tm refl refl = refl

postulate
  var : Var Γ A → Tm Γ A
  var-p : var x [ p ]ᵗ ≡ var (vs x) ∈ Tm (Γ ▹ A) (B [ p ]ᵀ)

postulate
  p-⁺ᵀ : B [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ B [ γ ]ᵀ [ p ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ) i
  vz-⁺ :
    var vz [ γ ⁺ ]ᵗ ≡[ ap-Tm refl (dep p-⁺ᵀ) ]
    var vz ∈ Tm (Δ ▹ A [ γ ]ᵀ) (A [ γ ]ᵀ [ p ]ᵀ)
  vs-⁺ :
    var (vs x) [ γ ⁺ ]ᵗ ≡[ ap-Tm refl (dep p-⁺ᵀ) ]
    var x [ γ ]ᵗ [ p ]ᵗ ∈ Tm (Δ ▹ A [ γ ]ᵀ) (B [ γ ]ᵀ [ p ]ᵀ)

  p-⟨⟩ᵀ : B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B
  vz-⟨⟩ : var vz [ ⟨ a ⟩ ]ᵗ ≡[ ap-Tm refl (dep p-⟨⟩ᵀ) ] a
  vs-⟨⟩ : var (vs x) [ ⟨ a ⟩ ]ᵗ ≡[ ap-Tm refl (dep p-⟨⟩ᵀ) ] var x

  ⟨⟩-[]ᵀ : B [ ⟨ a ⟩ ]ᵀ [ γ ]ᵀ ≡ B [ γ ⁺ ]ᵀ [ ⟨ a [ γ ]ᵗ ⟩ ]ᵀ
  ▹-ηᵀ : B ≡ B [ p ⁺ ]ᵀ [ ⟨ var vz ⟩ ]ᵀ

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
    app f a [ γ ]ᵗ ≡[ ap-Tm refl (dep ⟨⟩-[]ᵀ) ]
    app (coe (ap-Tm refl (dep Π-[])) (f [ γ ]ᵗ)) (a [ γ ]ᵗ)

  lam : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  lam-[] : lam b [ γ ]ᵗ ≡[ ap-Tm refl (dep Π-[]) ] lam (b [ γ ⁺ ]ᵗ)

  Π-β : app (lam b) a ≡ b [ ⟨ a ⟩ ]ᵗ
  Π-η :
    f ≡
    lam
      (coe (ap-Tm refl (dep (sym ▹-ηᵀ)))
        (app (coe (ap-Tm refl (dep Π-[])) (f [ p ]ᵗ)) (var vz)))

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

  coe-[]ᵗ :
    (A₀₁ : A₀ ≡ A₁) →
    coe (ap-Tm refl (dep (ap-[]ᵀ A₀₁))) (a [ γ ]ᵗ) ≡
    coe (ap-Tm refl (dep A₀₁)) a [ γ ]ᵗ
  coe-[]ᵗ refl = refl

  ap-▹ : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → (Γ₀ ▹ A₀) ≡ (Γ₁ ▹ A₁)
  ap-▹ refl refl = refl

  apᵈ-p :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    p ≡[ ap-Sub (ap-▹ Γ₀₁ A₀₁) Γ₀₁ ] p
  apᵈ-p refl refl = refl

  ap-Var : (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → Var Γ₀ A₀ ≡ Var Γ₁ A₁
  ap-Var refl refl = refl

  apᵈ-var :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    x₀ ≡[ ap-Var Γ₀₁ A₀₁ ] x₁ → var x₀ ≡[ ap-Tm Γ₀₁ A₀₁ ] var x₁
  apᵈ-var refl refl refl = refl

  coe-var :
    (A₀₁ : A₀ ≡ A₁) →
    coe (ap-Tm refl (dep A₀₁)) (var x) ≡ var (coe (ap-Var refl (dep A₀₁)) x)
  coe-var refl = refl

  apᵈ-vz :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    vz
      ≡[
        ap-Var (ap-▹ Γ₀₁ A₀₁) (apᵈ-[]ᵀ Γ₀₁ (ap-▹ Γ₀₁ A₀₁) A₀₁ (apᵈ-p Γ₀₁ A₀₁)) ]
    vz
  apᵈ-vz refl refl = refl

  apᵈ-⟨⟩ :
    (Γ₀₁ : Γ₀ ≡ Γ₁) (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) →
    a₀ ≡[ ap-Tm Γ₀₁ A₀₁ ] a₁ → ⟨ a₀ ⟩ ≡[ ap-Sub Γ₀₁ (ap-▹ Γ₀₁ A₀₁) ] ⟨ a₁ ⟩
  apᵈ-⟨⟩ refl refl refl = refl

  apᵈ-U : (Γ₀₁ : Γ₀ ≡ Γ₁) → U i ≡[ ap-Ty Γ₀₁ ] U i
  apᵈ-U refl = refl

  apᵈ-El :
    (Γ₀₁ : Γ₀ ≡ Γ₁) →
    α₀ ≡[ ap-Tm Γ₀₁ (apᵈ-U Γ₀₁) ] α₁ → El α₀ ≡[ ap-Ty Γ₀₁ ] El α₁
  apᵈ-El refl refl = refl

  apᵈ-c :
    (Γ₀₁ : Γ₀ ≡ Γ₁) →
    A₀ ≡[ ap-Ty Γ₀₁ ] A₁ → c A₀ ≡[ ap-Tm Γ₀₁ (apᵈ-U Γ₀₁) ] c A₁
  apᵈ-c refl refl = refl

  apᵈ-Π :
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) → B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁ →
    Π A₀ B₀ ≡[ ap-Ty Γ₀₁ ] Π A₁ B₁
  apᵈ-Π refl refl refl = refl

  apᵈ-app :
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) (B₀₁ : B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁) →
    f₀ ≡[ ap-Tm Γ₀₁ (apᵈ-Π Γ₀₁ A₀₁ B₀₁) ] f₁ →
    (a₀₁ : a₀ ≡[ ap-Tm Γ₀₁ A₀₁ ] a₁) →
    app f₀ a₀
      ≡[ ap-Tm Γ₀₁ (apᵈ-[]ᵀ (ap-▹ Γ₀₁ A₀₁) Γ₀₁ B₀₁ (apᵈ-⟨⟩ Γ₀₁ A₀₁ a₀₁)) ]
    app f₁ a₁
  apᵈ-app refl refl refl refl refl = refl

  apᵈ-lam :
    (Γ₀₁ : Γ₀ ≡ Γ₁)
    (A₀₁ : A₀ ≡[ ap-Ty Γ₀₁ ] A₁) (B₀₁ : B₀ ≡[ ap-Ty (ap-▹ Γ₀₁ A₀₁) ] B₁) →
    b₀ ≡[ ap-Tm (ap-▹ Γ₀₁ A₀₁) B₀₁ ] b₁ →
    lam b₀ ≡[ ap-Tm Γ₀₁ (apᵈ-Π Γ₀₁ A₀₁ B₀₁) ] lam b₁
  apᵈ-lam refl refl refl refl = refl

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
          (A₀₁ : A₀ ≡ A₁) → Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
          a₀ ≡[ ap-Tm refl (dep A₀₁) ] a₁ → Tmᴹ Γᴹ Aᴹ₀ a₀ ≡ Tmᴹ Γᴹ Aᴹ₁ a₁
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
    (A₀₁ : A₀ ≡ A₁) → Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
    a₀ ≡[ ap-Tm refl (dep A₀₁) ] a₁ → Tmᴹ Γᴹ Aᴹ₀ a₀ ≡ Tmᴹ Γᴹ Aᴹ₁ a₁
  ap-Tmᴹ = Util.ap-Tmᴹ Conᴹ Tyᴹ Tmᴹ

  field
    Varᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Var Γ A → Set
    varᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Varᴹ Γᴹ Aᴹ x → Tmᴹ Γᴹ Aᴹ (var x)

    vzᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Varᴹ (Γᴹ ▹ᴹ Aᴹ) (Aᴹ [ pᴹ ]ᵀᴹ) vz
    vsᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} →
      Varᴹ Γᴹ Bᴹ x → Varᴹ (Γᴹ ▹ᴹ Aᴹ) (Bᴹ [ pᴹ ]ᵀᴹ) (vs x)
    var-pᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} {xᴹ : Varᴹ Γᴹ Bᴹ x} →
      varᴹ xᴹ [ pᴹ ]ᵗᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep var-p) ]
      varᴹ (vsᴹ xᴹ) ∈ Tmᴹ (Γᴹ ▹ᴹ Aᴹ) (Bᴹ [ pᴹ ]ᵀᴹ) (var (vs x))

    _⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A}
      (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Subᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Γᴹ ▹ᴹ Aᴹ) (γ ⁺)
    p-⁺ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      Bᴹ [ pᴹ ]ᵀᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ p-⁺ᵀ ]
      Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ ∈ Tyᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) j (B [ γ ]ᵀ [ p ]ᵀ)

    vz-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      varᴹ vzᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⁺ᵀ p-⁺ᵀᴹ vz-⁺ ]
      varᴹ vzᴹ ∈ Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Aᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (var vz)
    vs-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {xᴹ : Varᴹ Γᴹ Bᴹ x} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      varᴹ (vsᴹ xᴹ) [ γᴹ ⁺ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⁺ᵀ p-⁺ᵀᴹ vs-⁺ ]
      varᴹ xᴹ [ γᴹ ]ᵗᴹ [ pᴹ ]ᵗᴹ
        ∈ Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (var x [ γ ]ᵗ [ p ]ᵗ)

    ⟨_⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Tmᴹ Γᴹ Aᴹ a → Subᴹ Γᴹ (Γᴹ ▹ᴹ Aᴹ) ⟨ a ⟩
    p-⟨⟩ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      Bᴹ [ pᴹ ]ᵀᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ p-⟨⟩ᵀ ] Bᴹ

    vz-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      varᴹ vzᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⟨⟩ᵀ p-⟨⟩ᵀᴹ vz-⟨⟩ ] aᴹ
    vs-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {xᴹ : Varᴹ Γᴹ Bᴹ x} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      varᴹ (vsᴹ xᴹ) [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⟨⟩ᵀ p-⟨⟩ᵀᴹ vs-⟨⟩ ] varᴹ xᴹ

    ⟨⟩-[]ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) j B}
      {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ ⟨⟩-[]ᵀ ]
      Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ aᴹ [ γᴹ ]ᵗᴹ ⟩ᴹ ]ᵀᴹ
    ▹-ηᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) j B} →
      Bᴹ ≡[ ap-Tyᴹ ▹-ηᵀ ] Bᴹ [ pᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ varᴹ vzᴹ ⟩ᴹ ]ᵀᴹ

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
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      appᴹ fᴹ aᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ ⟨⟩-[]ᵀ ⟨⟩-[]ᵀᴹ app-[] ]
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
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} →
      fᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep Π-η) ]
      lamᴹ
        (coe (ap-Tmᴹ (sym ▹-ηᵀ) (symᵈ ▹-ηᵀᴹ) refl)
          (appᴹ (coe (ap-Tmᴹ Π-[] Π-[]ᴹ refl) (fᴹ [ pᴹ ]ᵗᴹ)) (varᴹ vzᴹ)))

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
    ⟦⟧-[]ᵗ : ⟦ a [ γ ]ᵗ ⟧ᵗ ↝ ⟦ a ⟧ᵗ [ ⟦ γ ⟧ˢ ]ᵗᴹ
    {-# REWRITE ⟦⟧-[]ᵗ #-}

  ⟦_⟧ᵛ : (x : Var Γ A) → Varᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ x
  ⟦ vz ⟧ᵛ = vzᴹ
  ⟦ vs x ⟧ᵛ = vsᴹ ⟦ x ⟧ᵛ

  postulate
    ⟦⟧-var : ⟦ var x ⟧ᵗ ↝ varᴹ ⟦ x ⟧ᵛ
    {-# REWRITE ⟦⟧-var #-}

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
