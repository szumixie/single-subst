{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check #-}

module TT.CwF.Ind where

open import TT.Lib
open import TT.CwF.Syntax

private variable
  i : ℕ
  Γ Δ : Con
  γ γ₀ γ₁ δ δ₀ δ₁ : Sub Δ Γ
  A A₀ A₁ B B₀ B₁ : Ty Γ i
  a a₀ a₁ b f α : Tm Γ A

module DM where
  record Sorts : Set₁ where
    no-eta-equality
    field
      Conᴹ : Con → Set
      Subᴹ : Conᴹ Δ → Conᴹ Γ → Sub Δ Γ → Set
      Tyᴹ : Conᴹ Γ → (i : ℕ) → Ty Γ i → Set
      Tmᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set

    private variable
      Γᴹ Δᴹ : Conᴹ Γ
      Aᴹ₀ Aᴹ₁ : Tyᴹ Γᴹ i A

    opaque
      unfolding coe

      ap-Subᴹ : γ₀ ≡ γ₁ → Subᴹ Δᴹ Γᴹ γ₀ ≡ Subᴹ Δᴹ Γᴹ γ₁
      ap-Subᴹ refl = refl

      ap-Tyᴹ : A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ ≡ Tyᴹ Γᴹ i A₁
      ap-Tyᴹ refl = refl

      ap-Tmᴹ :
        (A₀₁ : A₀ ≡ A₁) → Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
        a₀ ≡[ ap-Tm A₀₁ ] a₁ → Tmᴹ Γᴹ Aᴹ₀ a₀ ≡ Tmᴹ Γᴹ Aᴹ₁ a₁
      ap-Tmᴹ refl refl refl = refl

  module _ (sorts : Sorts) where
    open Sorts sorts

    private variable
      Γᴹ Δᴹ Θᴹ : Conᴹ Γ
      γᴹ γᴹ₀ γᴹ₁ δᴹ δᴹ₀ δᴹ₁ θᴹ : Subᴹ Δᴹ Γᴹ γ
      Aᴹ Aᴹ₀ Aᴹ₁ Bᴹ Bᴹ₀ Bᴹ₁ : Tyᴹ Γᴹ i A
      aᴹ aᴹ₀ aᴹ₁ bᴹ fᴹ αᴹ : Tmᴹ Γᴹ Aᴹ a

    private
      module Core-util
        (_[_]ᵀᴹ :
          ∀ {Γ i A Δ γ} {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} →
          Tyᴹ Γᴹ i A → Subᴹ Δᴹ Γᴹ γ → Tyᴹ Δᴹ i (A [ γ ]ᵀ))
        where
        opaque
          unfolding coe

          apᵈ-[]ᵀᴹᵣ :
            (γ₀₁ : γ₀ ≡ γ₁) → γᴹ₀ ≡[ ap-Subᴹ γ₀₁ ] γᴹ₁ →
            Aᴹ [ γᴹ₀ ]ᵀᴹ ≡[ ap-Tyᴹ (ap-[]ᵀᵣ γ₀₁) ] Aᴹ [ γᴹ₁ ]ᵀᴹ
          apᵈ-[]ᵀᴹᵣ refl refl = refl

    record Core : Set where
      no-eta-equality

      infixl 9 _∘ᴹ_ _[_]ᵀᴹ _[_]ᵗᴹ
      field
        _∘ᴹ_ : Subᴹ Δᴹ Γᴹ γ → Subᴹ Θᴹ Δᴹ δ → Subᴹ Θᴹ Γᴹ (γ ∘ δ)
        assocᴹ : γᴹ ∘ᴹ (δᴹ ∘ᴹ θᴹ) ≡[ ap-Subᴹ assoc ] (γᴹ ∘ᴹ δᴹ) ∘ᴹ θᴹ

        idᴹ : Subᴹ Γᴹ Γᴹ id
        idrᴹ : γᴹ ∘ᴹ idᴹ ≡[ ap-Subᴹ idr ] γᴹ
        idlᴹ : idᴹ ∘ᴹ γᴹ ≡[ ap-Subᴹ idl ] γᴹ

        _[_]ᵀᴹ : Tyᴹ Γᴹ i A → Subᴹ Δᴹ Γᴹ γ → Tyᴹ Δᴹ i (A [ γ ]ᵀ)
        []ᵀ-∘ᴹ : Aᴹ [ γᴹ ∘ᴹ δᴹ ]ᵀᴹ ≡[ ap-Tyᴹ []ᵀ-∘ ] Aᴹ [ γᴹ ]ᵀᴹ [ δᴹ ]ᵀᴹ
        []ᵀ-idᴹ : Aᴹ [ idᴹ ]ᵀᴹ ≡[ ap-Tyᴹ []ᵀ-id ] Aᴹ

        _[_]ᵗᴹ :
          Tmᴹ Γᴹ Aᴹ a → (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Tmᴹ Δᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (a [ γ ]ᵗ)
        []ᵗ-∘ᴹ :
          aᴹ [ γᴹ ∘ᴹ δᴹ ]ᵗᴹ ≡[ ap-Tmᴹ []ᵀ-∘ []ᵀ-∘ᴹ []ᵗ-∘ ] aᴹ [ γᴹ ]ᵗᴹ [ δᴹ ]ᵗᴹ
        []ᵗ-idᴹ : aᴹ [ idᴹ ]ᵗᴹ ≡[ ap-Tmᴹ []ᵀ-id []ᵀ-idᴹ []ᵗ-id ] aᴹ

      apᵈ-[]ᵀᴹᵣ :
        (γ₀₁ : γ₀ ≡ γ₁) → γᴹ₀ ≡[ ap-Subᴹ γ₀₁ ] γᴹ₁ →
        Aᴹ [ γᴹ₀ ]ᵀᴹ ≡[ ap-Tyᴹ (ap-[]ᵀᵣ γ₀₁) ] Aᴹ [ γᴹ₁ ]ᵀᴹ
      apᵈ-[]ᵀᴹᵣ = Core-util.apᵈ-[]ᵀᴹᵣ _[_]ᵀᴹ

      infixl 2 _▹ᴹ_
      infixl 4 _,ᴹ_
      field
        ◇ᴹ : Conᴹ ◇
        εᴹ : Subᴹ Γᴹ ◇ᴹ ε
        ε-∘ᴹ : εᴹ ∘ᴹ γᴹ ≡[ ap-Subᴹ ε-∘ ] εᴹ
        ◇-ηᴹ : idᴹ ≡[ ap-Subᴹ ◇-η ] εᴹ

        _▹ᴹ_ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Conᴹ (Γ ▹ A)
        pᴹ : Subᴹ (Γᴹ ▹ᴹ Aᴹ) Γᴹ p
        qᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) (Aᴹ [ pᴹ ]ᵀᴹ) q

        _,ᴹ_ :
          (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Tmᴹ Δᴹ (Aᴹ [ γᴹ ]ᵀᴹ) a →
          Subᴹ Δᴹ (Γᴹ ▹ᴹ Aᴹ) (γ , a)
        ,-∘ᴹ :
          (γᴹ ,ᴹ aᴹ) ∘ᴹ δᴹ ≡[ ap-Subᴹ ,-∘ ]
          ( γᴹ ∘ᴹ δᴹ ,ᴹ
            coe (ap-Tmᴹ (sym []ᵀ-∘) (symᵈ []ᵀ-∘ᴹ) refl) (aᴹ [ δᴹ ]ᵗᴹ))

        ▹-β₁ᴹ : pᴹ ∘ᴹ (γᴹ ,ᴹ aᴹ) ≡[ ap-Subᴹ ▹-β₁ ] γᴹ
        ▹-β₂ᴹ :
          qᴹ [ γᴹ ,ᴹ aᴹ ]ᵗᴹ
            ≡[
              ap-Tmᴹ
                (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ▹-β₁)
                (symᵈ []ᵀ-∘ᴹ ∙ᵈ apᵈ-[]ᵀᴹᵣ ▹-β₁ ▹-β₁ᴹ)
                ▹-β₂ ]
          aᴹ
        ▹-ηᴹ :
          idᴹ ≡[ ap-Subᴹ ▹-η ] (pᴹ ,ᴹ qᴹ) ∈ Subᴹ (Γᴹ ▹ᴹ Aᴹ) (Γᴹ ▹ᴹ Aᴹ) (p , q)

      opaque
        unfolding coe

        apᵈ-∘ᴹᵣ :
          (δ₀₁ : δ₀ ≡ δ₁) → δᴹ₀ ≡[ ap-Subᴹ δ₀₁ ] δᴹ₁ →
          γᴹ ∘ᴹ δᴹ₀ ≡[ ap-Subᴹ (ap-∘ᵣ δ₀₁) ] γᴹ ∘ᴹ δᴹ₁
        apᵈ-∘ᴹᵣ refl refl = refl

        apᵈ-[]ᵀᴹ :
          (A₀₁ : A₀ ≡ A₁) → Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
          Aᴹ₀ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ (ap-[]ᵀ A₀₁) ] Aᴹ₁ [ γᴹ ]ᵀᴹ
        apᵈ-[]ᵀᴹ refl refl = refl

        apᵈ-[]ᵗᴹ :
          (A₀₁ : A₀ ≡ A₁) (Aᴹ₀₁ : Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁)
          (a₀₁ : a₀ ≡[ ap-Tm A₀₁ ] a₁) → aᴹ₀ ≡[ ap-Tmᴹ A₀₁ Aᴹ₀₁ a₀₁ ] aᴹ₁ →
          aᴹ₀ [ γᴹ ]ᵗᴹ
            ≡[ ap-Tmᴹ (ap-[]ᵀ A₀₁) (apᵈ-[]ᵀᴹ A₀₁ Aᴹ₀₁) (apᵈ-[]ᵗ A₀₁ a₀₁) ]
          aᴹ₁ [ γᴹ ]ᵗᴹ
        apᵈ-[]ᵗᴹ refl refl refl refl = refl

        apᵈ-,ᴹ :
          (γ₀₁ : γ₀ ≡ γ₁) (γᴹ₀₁ : γᴹ₀ ≡[ ap-Subᴹ γ₀₁ ] γᴹ₁)
          (a₀₁ : a₀ ≡[ ap-Tm (ap-[]ᵀᵣ γ₀₁) ] a₁) →
          aᴹ₀ ≡[ ap-Tmᴹ (ap-[]ᵀᵣ γ₀₁) (apᵈ-[]ᵀᴹᵣ γ₀₁ γᴹ₀₁) a₀₁ ] aᴹ₁ →
          (γᴹ₀ ,ᴹ aᴹ₀) ≡[ ap-Subᴹ (ap-, γ₀₁ a₀₁) ] (γᴹ₁ ,ᴹ aᴹ₁)
        apᵈ-,ᴹ refl refl refl refl = refl

      _⁺ᴹ : (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Subᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Γᴹ ▹ᴹ Aᴹ) (γ ⁺)
      γᴹ ⁺ᴹ = γᴹ ∘ᴹ pᴹ ,ᴹ coe (ap-Tmᴹ (sym []ᵀ-∘) (symᵈ []ᵀ-∘ᴹ) refl) qᴹ

      ⟨_⟩ᴹ : Tmᴹ Γᴹ Aᴹ a → Subᴹ Γᴹ (Γᴹ ▹ᴹ Aᴹ) ⟨ a ⟩
      ⟨ aᴹ ⟩ᴹ = idᴹ ,ᴹ coe (ap-Tmᴹ (sym []ᵀ-id) (symᵈ []ᵀ-idᴹ) refl) aᴹ

      ⟨⟩-∘ᴹ : ⟨ aᴹ ⟩ᴹ ∘ᴹ γᴹ ≡[ ap-Subᴹ ⟨⟩-∘ ] γᴹ ⁺ᴹ ∘ᴹ ⟨ aᴹ [ γᴹ ]ᵗᴹ ⟩ᴹ
      ⟨⟩-∘ᴹ =
        ,-∘ᴹ ∙ᵈ
        apᵈ-,ᴹ
          (idl ∙ sym idr ∙ ap-∘ᵣ (sym ▹-β₁) ∙ assoc)
          (idlᴹ ∙ᵈ symᵈ idrᴹ ∙ᵈ apᵈ-∘ᴹᵣ (sym ▹-β₁) (symᵈ ▹-β₁ᴹ) ∙ᵈ assocᴹ)
          (splitlr
            ( apᵈ-[]ᵗ []ᵀ-id (splitl reflᵈ) ∙ᵈ
              symᵈ (merger ▹-β₂) ∙ᵈ
              apᵈ-[]ᵗ (sym []ᵀ-∘) refl))
          (splitlr
            ( apᵈ-[]ᵗᴹ []ᵀ-id []ᵀ-idᴹ (splitl reflᵈ) (splitl reflᵈ) ∙ᵈ
              symᵈ (merger ▹-β₂ᴹ) ∙ᵈ
              apᵈ-[]ᵗᴹ (sym []ᵀ-∘) (symᵈ []ᵀ-∘ᴹ) refl refl)) ∙ᵈ
        symᵈ ,-∘ᴹ

      ▹-η′ᴹ :
        idᴹ ≡[ ap-Subᴹ ▹-η′ ]
        pᴹ ⁺ᴹ ∘ᴹ ⟨ qᴹ ⟩ᴹ ∈ Subᴹ (Γᴹ ▹ᴹ Aᴹ) (Γᴹ ▹ᴹ Aᴹ) (p ⁺ ∘ ⟨ q ⟩)
      ▹-η′ᴹ =
        ▹-ηᴹ ∙ᵈ
        apᵈ-,ᴹ
          (sym idr ∙ ap-∘ᵣ (sym ▹-β₁) ∙ assoc)
          (symᵈ idrᴹ ∙ᵈ apᵈ-∘ᴹᵣ (sym ▹-β₁) (symᵈ ▹-β₁ᴹ) ∙ᵈ assocᴹ)
          (splitr (symᵈ (merger ▹-β₂) ∙ᵈ apᵈ-[]ᵗ (sym []ᵀ-∘) refl))
          (splitr
            ( symᵈ (merger ▹-β₂ᴹ) ∙ᵈ
              apᵈ-[]ᵗᴹ (sym []ᵀ-∘) (symᵈ []ᵀ-∘ᴹ) refl refl)) ∙ᵈ
        symᵈ ,-∘ᴹ

    private
      module Types-util
        (core : Core)
        (open Core core)
        (Πᴹ :
          ∀ {Γ i A B} {Γᴹ : Conᴹ Γ} (Aᴹ : Tyᴹ Γᴹ i A) →
          Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B → Tyᴹ Γᴹ i (Π A B))
        where
        opaque
          unfolding coe

          apᵈ-Πᴹ :
            (B₀₁ : B₀ ≡ B₁) → Bᴹ₀ ≡[ ap-Tyᴹ B₀₁ ] Bᴹ₁ →
            Πᴹ Aᴹ Bᴹ₀ ≡[ ap-Tyᴹ (ap-Π B₀₁) ] Πᴹ Aᴹ Bᴹ₁
          apᵈ-Πᴹ refl refl = refl

    record Types (core : Core) : Set where
      no-eta-equality
      open Core core

      field
        Uᴹ : (i : ℕ) → Tyᴹ Γᴹ (suc i) (U i)
        U-[]ᴹ : Uᴹ i [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ U-[] ] Uᴹ i

        Elᴹ : Tmᴹ Γᴹ (Uᴹ i) α → Tyᴹ Γᴹ i (El α)
        El-[]ᴹ :
          Elᴹ αᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ El-[] ]
          Elᴹ (coe (ap-Tmᴹ U-[] U-[]ᴹ refl) (αᴹ [ γᴹ ]ᵗᴹ))

        cᴹ : Tyᴹ Γᴹ i A → Tmᴹ Γᴹ (Uᴹ i) (c A)
        c-[]ᴹ : cᴹ Aᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ U-[] U-[]ᴹ c-[] ] cᴹ (Aᴹ [ γᴹ ]ᵀᴹ)

        U-βᴹ : Elᴹ (cᴹ Aᴹ) ≡[ ap-Tyᴹ U-β ] Aᴹ
        U-ηᴹ : αᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep U-η) ] cᴹ (Elᴹ αᴹ)

      field
        Πᴹ : (Aᴹ : Tyᴹ Γᴹ i A) → Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B → Tyᴹ Γᴹ i (Π A B)
        Π-[]ᴹ :
          Πᴹ Aᴹ Bᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ Π-[] ] Πᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ)

        appᴹ :
          Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f →
          (aᴹ : Tmᴹ Γᴹ Aᴹ a) → Tmᴹ Γᴹ (Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ) (app f a)
        app-[]ᴹ :
          appᴹ fᴹ aᴹ [ γᴹ ]ᵗᴹ
            ≡[
              ap-Tmᴹ
                (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ⟨⟩-∘ ∙ []ᵀ-∘)
                (symᵈ []ᵀ-∘ᴹ ∙ᵈ apᵈ-[]ᵀᴹᵣ ⟨⟩-∘ ⟨⟩-∘ᴹ ∙ᵈ []ᵀ-∘ᴹ)
                app-[] ]
          appᴹ (coe (ap-Tmᴹ Π-[] Π-[]ᴹ refl) (fᴹ [ γᴹ ]ᵗᴹ)) (aᴹ [ γᴹ ]ᵗᴹ)

        lamᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (lam b)
        lam-[]ᴹ :
          lamᴹ bᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ Π-[] Π-[]ᴹ lam-[] ] lamᴹ (bᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ)

      apᵈ-Πᴹ :
        (B₀₁ : B₀ ≡ B₁) → Bᴹ₀ ≡[ ap-Tyᴹ B₀₁ ] Bᴹ₁ →
        Πᴹ Aᴹ Bᴹ₀ ≡[ ap-Tyᴹ (ap-Π B₀₁) ] Πᴹ Aᴹ Bᴹ₁
      apᵈ-Πᴹ = Types-util.apᵈ-Πᴹ core Πᴹ

      field
        Π-βᴹ :
          appᴹ (lamᴹ bᴹ) aᴹ ≡[ ap-Tmᴹ refl reflᵈ (dep Π-β) ] bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ
        Π-ηᴹ :
          fᴹ ≡[
            ap-Tmᴹ
              (ap-Π (sym []ᵀ-id ∙ ap-[]ᵀᵣ ▹-η′ ∙ []ᵀ-∘))
              (apᵈ-Πᴹ
                (sym []ᵀ-id ∙ ap-[]ᵀᵣ ▹-η′ ∙ []ᵀ-∘)
                (symᵈ []ᵀ-idᴹ ∙ᵈ apᵈ-[]ᵀᴹᵣ ▹-η′ ▹-η′ᴹ ∙ᵈ []ᵀ-∘ᴹ))
              Π-η ]
          lamᴹ (appᴹ (coe (ap-Tmᴹ Π-[] Π-[]ᴹ refl) (fᴹ [ pᴹ ]ᵗᴹ)) qᴹ)

  open Sorts public
  open Core public
  open Types public

record DModel : Set₁ where
  no-eta-equality
  open DM

  field
    sorts : Sorts
    core : Core sorts
    types : Types sorts core

  open Sorts sorts public
  open Core core public
  open Types types public

module Ind (M : DModel) where
  open DModel M

  ⟦_⟧ᶜ : (Γ : Con) → Conᴹ Γ

  postulate
    ⟦_⟧ᵀ : (A : Ty Γ i) → Tyᴹ ⟦ Γ ⟧ᶜ i A

  ⟦ ◇ ⟧ᶜ = ◇ᴹ
  ⟦ Γ ▹ A ⟧ᶜ = ⟦ Γ ⟧ᶜ ▹ᴹ ⟦ A ⟧ᵀ

  postulate
    ⟦_⟧ˢ : (γ : Sub Δ Γ) → Subᴹ ⟦ Δ ⟧ᶜ ⟦ Γ ⟧ᶜ γ
    ⟦⟧-∘ : ⟦ γ ∘ δ ⟧ˢ ↝ ⟦ γ ⟧ˢ ∘ᴹ ⟦ δ ⟧ˢ
    {-# REWRITE ⟦⟧-∘ #-}
    ⟦⟧-id : ⟦ id ⟧ˢ ↝ idᴹ ∈ Subᴹ ⟦ Γ ⟧ᶜ ⟦ Γ ⟧ᶜ id
    {-# REWRITE ⟦⟧-id #-}

  postulate
    ⟦⟧-[]ᵀ : ⟦ A [ γ ]ᵀ ⟧ᵀ ↝ ⟦ A ⟧ᵀ [ ⟦ γ ⟧ˢ ]ᵀᴹ
    {-# REWRITE ⟦⟧-[]ᵀ #-}

  postulate
    ⟦_⟧ᵗ : (a : Tm Γ A) → Tmᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ a
    ⟦⟧-[]ᵗ : ⟦ a [ γ ]ᵗ ⟧ᵗ ↝ ⟦ a ⟧ᵗ [ ⟦ γ ⟧ˢ ]ᵗᴹ
    {-# REWRITE ⟦⟧-[]ᵗ #-}

  opaque
    unfolding coe

    apᵈ-⟦⟧ᵀ : (A₀₁ : A₀ ≡ A₁) → ⟦ A₀ ⟧ᵀ ≡[ ap-Tyᴹ A₀₁ ] ⟦ A₁ ⟧ᵀ
    apᵈ-⟦⟧ᵀ refl = refl

    apᵈ-⟦⟧ᵗ :
      (A₀₁ : A₀ ≡ A₁) (a₀₁ : a₀ ≡[ ap-Tm A₀₁ ] a₁) →
      ⟦ a₀ ⟧ᵗ ≡[ ap-Tmᴹ A₀₁ (apᵈ-⟦⟧ᵀ A₀₁) a₀₁ ] ⟦ a₁ ⟧ᵗ
    apᵈ-⟦⟧ᵗ refl refl = refl

  postulate
    ⟦⟧-ε : ⟦ ε ⟧ˢ ↝ εᴹ ∈ Subᴹ ⟦ Γ ⟧ᶜ ⟦ ◇ ⟧ᶜ ε
    {-# REWRITE ⟦⟧-ε #-}
    ⟦⟧-p : ⟦ p ⟧ˢ ↝ pᴹ ∈ Subᴹ ⟦ Γ ▹ A ⟧ᶜ ⟦ Γ ⟧ᶜ p
    {-# REWRITE ⟦⟧-p #-}
    ⟦⟧-q : ⟦ q ⟧ᵗ ↝ qᴹ ∈ Tmᴹ ⟦ Γ ▹ A ⟧ᶜ ⟦ A [ p ]ᵀ ⟧ᵀ q
    {-# REWRITE ⟦⟧-q #-}
    ⟦⟧-, : ⟦ γ , a ⟧ˢ ↝ (⟦ γ ⟧ˢ ,ᴹ ⟦ a ⟧ᵗ)
    {-# REWRITE ⟦⟧-, #-}

  postulate
    ⟦⟧-U : ⟦ U i ⟧ᵀ ↝ Uᴹ i ∈ Tyᴹ ⟦ Γ ⟧ᶜ (suc i) (U i)
    {-# REWRITE ⟦⟧-U #-}
    ⟦⟧-El : ⟦ El α ⟧ᵀ ↝ Elᴹ ⟦ α ⟧ᵗ
    {-# REWRITE ⟦⟧-El #-}
    ⟦⟧-c : ⟦ c A ⟧ᵗ ↝ cᴹ ⟦ A ⟧ᵀ
    {-# REWRITE ⟦⟧-c #-}

    ⟦⟧-Π : ⟦ Π A B ⟧ᵀ ↝ Πᴹ ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
    {-# REWRITE ⟦⟧-Π #-}
    ⟦⟧-app :
      {A : Ty Γ i} {B : Ty (Γ ▹ A) i} {f : Tm Γ (Π A B)} {a : Tm Γ A} →
      ⟦ app f a ⟧ᵗ ↝
      coe
        (ap-Tmᴹ
          refl
          (apᵈ-[]ᵀᴹᵣ
            refl
            (apᵈ-,ᴹ refl reflᵈ reflᵈ (splitl (apᵈ-⟦⟧ᵗ (sym []ᵀ-id) refl))))
          reflᵈ)
        (appᴹ ⟦ f ⟧ᵗ ⟦ a ⟧ᵗ)
    {-# REWRITE ⟦⟧-app #-}
    ⟦⟧-lam : ⟦ lam b ⟧ᵗ ↝ lamᴹ ⟦ b ⟧ᵗ
    {-# REWRITE ⟦⟧-lam #-}
