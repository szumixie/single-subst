{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Ind where

open import TT.Lib
open import TT.SSC.Syntax

private variable
  i j : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
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
      Γᴹ : Conᴹ Γ
      Aᴹ₀ Aᴹ₁ : Tyᴹ Γᴹ i A

    opaque
      unfolding coe

      ap-Tyᴹ : A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ ≡ Tyᴹ Γᴹ i A₁
      ap-Tyᴹ refl = refl

      ap-Tmᴹ :
        (A₀₁ : A₀ ≡ A₁) → Aᴹ₀ ≡[ ap-Tyᴹ A₀₁ ] Aᴹ₁ →
        a₀ ≡[ ap-Tm A₀₁ ] a₁ → Tmᴹ Γᴹ Aᴹ₀ a₀ ≡ Tmᴹ Γᴹ Aᴹ₁ a₁
      ap-Tmᴹ refl refl refl = refl

  module _ (sorts : Sorts) where
    open Sorts sorts

    private variable
      Γᴹ Δᴹ : Conᴹ Γ
      γᴹ : Subᴹ Δᴹ Γᴹ γ
      Aᴹ Bᴹ Bᴹ₀ Bᴹ₁ : Tyᴹ Γᴹ i A
      aᴹ bᴹ fᴹ αᴹ : Tmᴹ Γᴹ Aᴹ a

    record Core : Set where
      no-eta-equality

      infixl 9 _[_]ᵀᴹ _[_]ᵗᴹ
      infixl 2 _▹ᴹ_
      infixl 10 _⁺ᴹ
      field
        _[_]ᵀᴹ : Tyᴹ Γᴹ i A → Subᴹ Δᴹ Γᴹ γ → Tyᴹ Δᴹ i (A [ γ ]ᵀ)
        _[_]ᵗᴹ :
          Tmᴹ Γᴹ Aᴹ a → (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Tmᴹ Δᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (a [ γ ]ᵗ)

        ◇ᴹ : Conᴹ ◇
        _▹ᴹ_ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Conᴹ (Γ ▹ A)

        pᴹ : Subᴹ (Γᴹ ▹ᴹ Aᴹ) Γᴹ p
        qᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) (Aᴹ [ pᴹ ]ᵀᴹ) q

        _⁺ᴹ : (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Subᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Γᴹ ▹ᴹ Aᴹ) (γ ⁺)
        p-⁺ᵀᴹ :
          Bᴹ [ pᴹ ]ᵀᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ p-⁺ᵀ ]
          Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ ∈ Tyᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) j (B [ γ ]ᵀ [ p ]ᵀ)

        p-⁺ᵗᴹ :
          bᴹ [ pᴹ ]ᵗᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⁺ᵀ p-⁺ᵀᴹ p-⁺ᵗ ]
          bᴹ [ γᴹ ]ᵗᴹ [ pᴹ ]ᵗᴹ
            ∈ Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (b [ γ ]ᵗ [ p ]ᵗ)
        q-⁺ᴹ :
          qᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⁺ᵀ p-⁺ᵀᴹ q-⁺ ]
          qᴹ ∈ Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Aᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) q

        ⟨_⟩ᴹ : Tmᴹ Γᴹ Aᴹ a → Subᴹ Γᴹ (Γᴹ ▹ᴹ Aᴹ) ⟨ a ⟩
        p-⟨⟩ᵀᴹ : Bᴹ [ pᴹ ]ᵀᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ ≡[ ap-Tyᴹ p-⟨⟩ᵀ ] Bᴹ

        p-⟨⟩ᵗᴹ : bᴹ [ pᴹ ]ᵗᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⟨⟩ᵀ p-⟨⟩ᵀᴹ p-⟨⟩ᵗ ] bᴹ
        q-⟨⟩ᴹ : qᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ ≡[ ap-Tmᴹ p-⟨⟩ᵀ p-⟨⟩ᵀᴹ q-⟨⟩ ] aᴹ

        ⟨⟩-[]ᵀᴹ :
          Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ [ γᴹ ]ᵀᴹ ≡[ ap-Tyᴹ ⟨⟩-[]ᵀ ]
          Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ aᴹ [ γᴹ ]ᵗᴹ ⟩ᴹ ]ᵀᴹ
        ▹-ηᵀᴹ : Bᴹ ≡[ ap-Tyᴹ ▹-ηᵀ ] Bᴹ [ pᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ qᴹ ⟩ᴹ ]ᵀᴹ

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
          appᴹ fᴹ aᴹ [ γᴹ ]ᵗᴹ ≡[ ap-Tmᴹ ⟨⟩-[]ᵀ ⟨⟩-[]ᵀᴹ app-[] ]
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
          fᴹ ≡[ ap-Tmᴹ (ap-Π ▹-ηᵀ) (apᵈ-Πᴹ ▹-ηᵀ ▹-ηᵀᴹ) Π-η ]
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
    ⟦⟧-q : ⟦ q ⟧ᵗ ↝ qᴹ ∈ Tmᴹ ⟦ Γ ▹ A ⟧ᶜ ⟦ A [ p ]ᵀ ⟧ᵀ q
    {-# REWRITE ⟦⟧-q #-}

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
