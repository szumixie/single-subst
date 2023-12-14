{-# OPTIONS --with-K --rewriting #-}

module TT.SSC where

open import TT.Lib

private variable
  ℓᶜ ℓˢ ℓᵀ ℓᵗ ℓᵛ : Level
  i j : ℕ

data Con : Set

postulate
  Ty : Con → ℕ → Set

infixl 2 _▹_
data Con where
  ◇ : Con
  _▹_ : (Γ : Con) → Ty Γ i → Con

private variable
  Γ Γ₀ Γ₁ Δ : Con
  A A₀ A₁ B : Ty Γ i

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

data Var : (Γ : Con) → Ty Γ i → Set where
  vz : Var (Γ ▹ A) (A [ p ]ᵀ)
  vs : Var Γ B → Var (Γ ▹ A) (B [ p ]ᵀ)

private variable
  γ : Sub Δ Γ
  a b f α : Tm Γ A
  x : Var Γ A

ty[_] : Γ₀ ≡ Γ₁ → Ty Γ₀ i → Ty Γ₁ i
ty[ refl ] A = A

tm[_,_] : (Γ₀₁ : Γ₀ ≡ Γ₁) → ty[ Γ₀₁ ] A₀ ≡ A₁ → Tm Γ₀ A₀ → Tm Γ₁ A₁
tm[ refl , refl ] a = a

postulate
  var : Var Γ A → Tm Γ A
  var-p : var x [ p ]ᵗ ≡ (Tm (Γ ▹ A) (B [ p ]ᵀ) ∋ var (vs x))

postulate
  p-⁺ᵀ : B [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ (Ty (Δ ▹ A [ γ ]ᵀ) i ∋ B [ γ ]ᵀ [ p ]ᵀ)
  vz-⁺ :
    tm[ refl , p-⁺ᵀ ] (var vz [ γ ⁺ ]ᵗ) ≡
    (Tm (Δ ▹ A [ γ ]ᵀ) (A [ γ ]ᵀ [ p ]ᵀ) ∋ var vz)
  vs-⁺ :
    tm[ refl , p-⁺ᵀ ] (var (vs x) [ γ ⁺ ]ᵗ) ≡
    (Tm (Δ ▹ A [ γ ]ᵀ) (B [ γ ]ᵀ [ p ]ᵀ) ∋ var x [ γ ]ᵗ [ p ]ᵗ)

  p-⟨⟩ᵀ : B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B
  vz-⟨⟩ : tm[ refl , p-⟨⟩ᵀ ] (var vz [ ⟨ a ⟩ ]ᵗ) ≡ a
  vs-⟨⟩ : tm[ refl , p-⟨⟩ᵀ ] (var (vs x) [ ⟨ a ⟩ ]ᵗ) ≡ var x

  ⟨⟩-[]ᵀ : B [ ⟨ a ⟩ ]ᵀ [ γ ]ᵀ ≡ B [ γ ⁺ ]ᵀ [ ⟨ a [ γ ]ᵗ ⟩ ]ᵀ
  ▹-ηᵀ : B ≡ B [ p ⁺ ]ᵀ [ ⟨ var vz ⟩ ]ᵀ

postulate
  U : (i : ℕ) → Ty Γ (suc i)
  U-[] : U i [ γ ]ᵀ ≡ U i

  El : Tm Γ (U i) → Ty Γ i
  El-[] : El α [ γ ]ᵀ ≡ El (tm[ refl , U-[] ] (α [ γ ]ᵗ))

  c : Ty Γ i → Tm Γ (U i)
  c-[] : tm[ refl , U-[] ] (c A [ γ ]ᵗ) ≡ c (A [ γ ]ᵀ)

  U-β : El (c A) ≡ A
  U-η : α ≡ c (El α)

  Π : (A : Ty Γ i) → Ty (Γ ▹ A) i → Ty Γ i
  Π-[] : Π A B [ γ ]ᵀ ≡ Π (A [ γ ]ᵀ) (B [ γ ⁺ ]ᵀ)

  app : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]ᵀ)
  app-[] :
    tm[ refl , ⟨⟩-[]ᵀ ] (app f a [ γ ]ᵗ) ≡
    app (tm[ refl , Π-[] ] (f [ γ ]ᵗ)) (a [ γ ]ᵗ)

  lam : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  lam-[] : tm[ refl , Π-[] ] (lam b [ γ ]ᵗ) ≡ lam (b [ γ ⁺ ]ᵗ)

  Π-β : app (lam b) a ≡ b [ ⟨ a ⟩ ]ᵗ
  Π-η :
    f ≡
    lam (tm[ refl , sym ▹-ηᵀ ] (app (tm[ refl , Π-[] ] (f [ p ]ᵗ)) (var vz)))

private variable
  Γ₀₁ : Γ₀ ≡ Γ₁
  A₀₁ : A₀ ≡ A₁
  a₀ a₁ : Tm Γ A

ty[]-shiftr : ty[ Γ₀₁ ] A₀ ≡ A₁ → A₀ ≡ ty[ sym Γ₀₁ ] A₁
ty[]-shiftr {Γ₀₁ = refl} A₀₁ = A₀₁

tm[]-shiftr :
  tm[ Γ₀₁ , A₀₁ ] a₀ ≡ a₁ → a₀ ≡
  tm[ sym Γ₀₁ , sym (ty[]-shiftr {Γ₀₁ = Γ₀₁} A₀₁) ] a₁
tm[]-shiftr {Γ₀₁ = refl} {A₀₁ = refl} a₀₁ = a₀₁

var[_] : A₀ ≡ A₁ → Var Γ A₀ → Var Γ A₁
var[ refl ] x = x

tm[]-var : tm[ refl , A₀₁ ] (var x) ≡ var (var[ A₀₁ ] x)
tm[]-var {A₀₁ = refl} = refl

private
  module Util
    (Conᴹ : Con → Set ℓᶜ) (Tyᴹ : ∀ {Γ} → Conᴹ Γ → (i : ℕ) → Ty Γ i → Set ℓᵀ)
    where
    tyᴹ[_] : {Γᴹ : Conᴹ Γ} → A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ → Tyᴹ Γᴹ i A₁
    tyᴹ[ refl ] Aᴹ₀ = Aᴹ₀

    tyᴹ[]-shiftr :
      {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁} →
      tyᴹ[ A₀₁ ] Aᴹ₀ ≡ Aᴹ₁ → Aᴹ₀ ≡ tyᴹ[ sym A₀₁ ] Aᴹ₁
    tyᴹ[]-shiftr {A₀₁ = refl} A₀₁ = A₀₁

    module _ (Tmᴹ : ∀ {Γ A} (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set ℓᵗ) where
      tmᴹ[_,_,_] :
        {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁}
        (A₀₁ : A₀ ≡ A₁) → tyᴹ[ A₀₁ ] Aᴹ₀ ≡ Aᴹ₁ → tm[ refl , A₀₁ ] a₀ ≡ a₁ →
        Tmᴹ Γᴹ Aᴹ₀ a₀ → Tmᴹ Γᴹ Aᴹ₁ a₁
      tmᴹ[ refl ,  refl , refl ] aᴹ₀ = aᴹ₀

record DModel ℓᶜ ℓˢ ℓᵀ ℓᵗ ℓᵛ : Set (ℓ.suc (ℓᶜ ⊔ ℓˢ ⊔ ℓᵀ ⊔ ℓᵗ ⊔ ℓᵛ)) where
  no-eta-equality
  infixl 9 _[_]ᵀᴹ _[_]ᵗᴹ
  field
    Conᴹ : Con → Set ℓᶜ
    Subᴹ : Conᴹ Δ → Conᴹ Γ → Sub Δ Γ → Set ℓˢ

    Tyᴹ : Conᴹ Γ → (i : ℕ) → Ty Γ i → Set ℓᵀ
    _[_]ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} →
      Tyᴹ Γᴹ i A → Subᴹ Δᴹ Γᴹ γ → Tyᴹ Δᴹ i (A [ γ ]ᵀ)

    Tmᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set ℓᵗ
    _[_]ᵗᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} →
      Tmᴹ Γᴹ Aᴹ a → (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Tmᴹ Δᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (a [ γ ]ᵗ)

  tyᴹ[_] : {Γᴹ : Conᴹ Γ} → A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ → Tyᴹ Γᴹ i A₁
  tyᴹ[_] = Util.tyᴹ[_] Conᴹ Tyᴹ

  tyᴹ[]-shiftr :
    {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁} →
    tyᴹ[ A₀₁ ] Aᴹ₀ ≡ Aᴹ₁ → Aᴹ₀ ≡ tyᴹ[ sym A₀₁ ] Aᴹ₁
  tyᴹ[]-shiftr = Util.tyᴹ[]-shiftr Conᴹ Tyᴹ

  tmᴹ[_,_,_] :
    {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁}
    (A₀₁ : A₀ ≡ A₁) → tyᴹ[ A₀₁ ] Aᴹ₀ ≡ Aᴹ₁ → tm[ refl , A₀₁ ] a₀ ≡ a₁ →
    Tmᴹ Γᴹ Aᴹ₀ a₀ → Tmᴹ Γᴹ Aᴹ₁ a₁
  tmᴹ[_,_,_] = Util.tmᴹ[_,_,_] Conᴹ Tyᴹ Tmᴹ

  infixl 2 _▹ᴹ_
  field
    ◇ᴹ : Conᴹ ◇
    _▹ᴹ_ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Conᴹ (Γ ▹ A)
    pᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Subᴹ (Γᴹ ▹ᴹ Aᴹ) Γᴹ p

  field
    Varᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Var Γ A → Set ℓᵛ
    varᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Varᴹ Γᴹ Aᴹ x → Tmᴹ Γᴹ Aᴹ (var x)

    vzᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Varᴹ (Γᴹ ▹ᴹ Aᴹ) (Aᴹ [ pᴹ ]ᵀᴹ) vz
    vsᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} →
      Varᴹ Γᴹ Bᴹ x → Varᴹ (Γᴹ ▹ᴹ Aᴹ) (Bᴹ [ pᴹ ]ᵀᴹ) (vs x)
    var-pᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} {xᴹ : Varᴹ Γᴹ Bᴹ x} →
      tmᴹ[ refl , refl , var-p ] (varᴹ xᴹ [ pᴹ ]ᵗᴹ) ≡
      (Tmᴹ (Γᴹ ▹ᴹ Aᴹ) (Bᴹ [ pᴹ ]ᵀᴹ) (var (vs x)) ∋ varᴹ (vsᴹ xᴹ))

  infixl 10 _⁺ᴹ
  field
    _⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A}
      (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Subᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Γᴹ ▹ᴹ Aᴹ) (γ ⁺)
    p-⁺ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tyᴹ[ p-⁺ᵀ ] (Bᴹ [ pᴹ ]ᵀᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ) ≡
      (Tyᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) j (B [ γ ]ᵀ [ p ]ᵀ) ∋ Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ)

    vz-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ p-⁺ᵀ , p-⁺ᵀᴹ , vz-⁺ ] (varᴹ vzᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ) ≡
      (Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Aᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (var vz) ∋ varᴹ vzᴹ)
    vs-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {xᴹ : Varᴹ Γᴹ Bᴹ x} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ p-⁺ᵀ , p-⁺ᵀᴹ , vs-⁺ ] (varᴹ (vsᴹ xᴹ) [ γᴹ ⁺ᴹ ]ᵗᴹ) ≡
      (Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (var x [ γ ]ᵗ [ p ]ᵗ)
        ∋ varᴹ xᴹ [ γᴹ ]ᵗᴹ [ pᴹ ]ᵗᴹ)

    ⟨_⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Tmᴹ Γᴹ Aᴹ a → Subᴹ Γᴹ (Γᴹ ▹ᴹ Aᴹ) ⟨ a ⟩
    p-⟨⟩ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tyᴹ[ p-⟨⟩ᵀ ] (Bᴹ [ pᴹ ]ᵀᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ) ≡ Bᴹ

    vz-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tmᴹ[ p-⟨⟩ᵀ , p-⟨⟩ᵀᴹ , vz-⟨⟩ ] (varᴹ vzᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ) ≡ aᴹ
    vs-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {xᴹ : Varᴹ Γᴹ Bᴹ x} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tmᴹ[ p-⟨⟩ᵀ , p-⟨⟩ᵀᴹ , vs-⟨⟩ ] (varᴹ (vsᴹ xᴹ) [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ) ≡ varᴹ xᴹ

    ⟨⟩-[]ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) j B}
      {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tyᴹ[ ⟨⟩-[]ᵀ ] (Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ [ γᴹ ]ᵀᴹ) ≡
      Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ aᴹ [ γᴹ ]ᵗᴹ ⟩ᴹ ]ᵀᴹ
    ▹-ηᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) j B} →
      tyᴹ[ ▹-ηᵀ ] Bᴹ ≡ Bᴹ [ pᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ varᴹ vzᴹ ⟩ᴹ ]ᵀᴹ

  field
    Uᴹ : {Γᴹ : Conᴹ Γ} (i : ℕ) → Tyᴹ Γᴹ (suc i) (U i)
    U-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tyᴹ[ U-[] ] (Uᴹ i [ γᴹ ]ᵀᴹ) ≡ Uᴹ i

    Elᴹ : {Γᴹ : Conᴹ Γ} → Tmᴹ Γᴹ (Uᴹ i) α → Tyᴹ Γᴹ i (El α)
    El-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {αᴹ : Tmᴹ Γᴹ (Uᴹ i) α} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tyᴹ[ El-[] ] (Elᴹ αᴹ [ γᴹ ]ᵀᴹ) ≡
      Elᴹ (tmᴹ[ U-[] , U-[]ᴹ , refl ] (αᴹ [ γᴹ ]ᵗᴹ))

    cᴹ : {Γᴹ : Conᴹ Γ} → Tyᴹ Γᴹ i A → Tmᴹ Γᴹ (Uᴹ i) (c A)
    c-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ U-[] , U-[]ᴹ , c-[] ] (cᴹ Aᴹ [ γᴹ ]ᵗᴹ) ≡ cᴹ (Aᴹ [ γᴹ ]ᵀᴹ)

    U-βᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → tyᴹ[ U-β ] (Elᴹ (cᴹ Aᴹ)) ≡ Aᴹ
    U-ηᴹ :
      {Γᴹ : Conᴹ Γ} {αᴹ : Tmᴹ Γᴹ (Uᴹ i) α} →
      tmᴹ[ refl , refl , U-η ] αᴹ ≡ cᴹ (Elᴹ αᴹ)

    Πᴹ : {Γᴹ : Conᴹ Γ} (Aᴹ : Tyᴹ Γᴹ i A) → Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B → Tyᴹ Γᴹ i (Π A B)
    Π-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tyᴹ[ Π-[] ] (Πᴹ Aᴹ Bᴹ [ γᴹ ]ᵀᴹ) ≡ Πᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ)

    appᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B} →
      Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f →
      (aᴹ : Tmᴹ Γᴹ Aᴹ a) → Tmᴹ Γᴹ (Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ) (app f a)
    app-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ ⟨⟩-[]ᵀ , ⟨⟩-[]ᵀᴹ , app-[] ] (appᴹ fᴹ aᴹ [ γᴹ ]ᵗᴹ) ≡
      appᴹ (tmᴹ[ Π-[] , Π-[]ᴹ , refl ] (fᴹ [ γᴹ ]ᵗᴹ)) (aᴹ [ γᴹ ]ᵗᴹ)

    lamᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B} →
      Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (lam b)
    lam-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {bᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ Π-[] , Π-[]ᴹ , lam-[] ] (lamᴹ bᴹ [ γᴹ ]ᵗᴹ) ≡ lamᴹ (bᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ)

    Π-βᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {bᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tmᴹ[ refl , refl , Π-β ] (appᴹ (lamᴹ bᴹ) aᴹ) ≡ bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ
    Π-ηᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} →
      tmᴹ[ refl , refl , Π-η ] fᴹ ≡
      lamᴹ
        (tmᴹ[ sym ▹-ηᵀ , sym (tyᴹ[]-shiftr ▹-ηᵀᴹ) , refl ]
          (appᴹ (tmᴹ[ Π-[] , Π-[]ᴹ , refl ] (fᴹ [ pᴹ ]ᵗᴹ)) (varᴹ vzᴹ)))

module Ind (D : DModel ℓᶜ ℓˢ ℓᵀ ℓᵗ ℓᵛ) where
  open DModel D

  ⟦_⟧ᶜ : (Γ : Con) → Conᴹ Γ

  postulate
    ⟦_⟧ᵀ : (A : Ty Γ i) → Tyᴹ ⟦ Γ ⟧ᶜ i A

  ⟦ ◇ ⟧ᶜ = ◇ᴹ
  ⟦ Γ ▹ A ⟧ᶜ = ⟦ Γ ⟧ᶜ ▹ᴹ ⟦ A ⟧ᵀ

  postulate
    ⟦_⟧ᵗ : (a : Tm Γ A) → Tmᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ a

  ⟦_⟧ˢ : (γ : Sub Δ Γ) → Subᴹ ⟦ Δ ⟧ᶜ ⟦ Γ ⟧ᶜ γ

  postulate
    ⟦⟧-[]ᵀ : ⟦ A [ γ ]ᵀ ⟧ᵀ ≡ ⟦ A ⟧ᵀ [ ⟦ γ ⟧ˢ ]ᵀᴹ
    {-# REWRITE ⟦⟧-[]ᵀ #-}

  ⟦ p ⟧ˢ = pᴹ
  ⟦ γ ⁺ ⟧ˢ = ⟦ γ ⟧ˢ ⁺ᴹ
  ⟦ ⟨ a ⟩ ⟧ˢ = ⟨ ⟦ a ⟧ᵗ ⟩ᴹ

  postulate
    ⟦⟧-[]ᵗ : ⟦ a [ γ ]ᵗ ⟧ᵗ ≡ ⟦ a ⟧ᵗ [ ⟦ γ ⟧ˢ ]ᵗᴹ
    {-# REWRITE ⟦⟧-[]ᵗ #-}

  ⟦_⟧ᵛ : (x : Var Γ A) → Varᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ x
  ⟦ vz ⟧ᵛ = vzᴹ
  ⟦ vs x ⟧ᵛ = vsᴹ ⟦ x ⟧ᵛ

  postulate
    ⟦⟧-var : ⟦ var x ⟧ᵗ ≡ varᴹ ⟦ x ⟧ᵛ
    {-# REWRITE ⟦⟧-var #-}

    ⟦⟧-U : ⟦ U i ⟧ᵀ ≡ (Tyᴹ ⟦ Γ ⟧ᶜ (suc i) (U i) ∋ Uᴹ i)
    {-# REWRITE ⟦⟧-U #-}
    ⟦⟧-El : ⟦ El α ⟧ᵀ ≡ Elᴹ ⟦ α ⟧ᵗ
    {-# REWRITE ⟦⟧-El #-}
    ⟦⟧-c : ⟦ c A ⟧ᵗ ≡ cᴹ ⟦ A ⟧ᵀ
    {-# REWRITE ⟦⟧-c #-}

    ⟦⟧-Π : ⟦ Π A B ⟧ᵀ ≡ Πᴹ ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
    {-# REWRITE ⟦⟧-Π #-}
    ⟦⟧-app : ⟦ app f a ⟧ᵗ ≡ appᴹ ⟦ f ⟧ᵗ ⟦ a ⟧ᵗ
    {-# REWRITE ⟦⟧-app #-}
    ⟦⟧-lam : ⟦ lam b ⟧ᵗ ≡ lamᴹ ⟦ b ⟧ᵗ
    {-# REWRITE ⟦⟧-lam #-}

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
