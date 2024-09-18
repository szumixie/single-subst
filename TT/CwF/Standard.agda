{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
#-}

module TT.CwF.Standard where

open import TT.Lib
open import TT.IRUniv
open import TT.CwF.Ind

open DM
open DModel

opaque
  unfolding coe

  M : DModel
  M .sorts .Conᴹ _ = Uω
  M .sorts .Subᴹ Δ Γ _ = Elω Δ → Elω Γ
  M .sorts .Tyᴹ Γ i _ = Elω Γ → U i
  M .sorts .Tmᴹ Γ A _ = (γ : Elω Γ) → El (A γ)

  M .core ._∘ᴹ_ γ δ θ = γ (δ θ)
  M .core .assocᴹ = refl

  M .core .idᴹ γ = γ
  M .core .idrᴹ = refl
  M .core .idlᴹ = refl

  M .core ._[_]ᵀᴹ A γ δ = A (γ δ)
  M .core .[]ᵀ-∘ᴹ = refl
  M .core .[]ᵀ-idᴹ = refl

  M .core ._[_]ᵗᴹ a γ δ = a (γ δ)
  M .core .[]ᵗ-∘ᴹ = refl
  M .core .[]ᵗ-idᴹ = refl

  M .core .◇ᴹ = `⊤
  M .core .εᴹ γ = ⋆
  M .core .ε-∘ᴹ = refl
  M .core .◇-ηᴹ = refl

  M .core ._▹ᴹ_ Γ A = `Σ Γ λ γ → base (`Lift (A γ))
  M .core .pᴹ (γ ,, a) = γ
  M .core .qᴹ (γ ,, a) = a

  M .core ._,ᴹ_ γ a δ = γ δ ,, a δ
  M .core .,-∘ᴹ = refl

  M .core .▹-β₁ᴹ = refl
  M .core .▹-β₂ᴹ = refl
  M .core .▹-ηᴹ = refl

  M .types .Uᴹ i γ = base `U
  M .types .U-[]ᴹ = refl

  M .types .Elᴹ A γ = A γ
  M .types .El-[]ᴹ = refl

  M .types .cᴹ A γ = A γ
  M .types .c-[]ᴹ = refl

  M .types .U-βᴹ = refl
  M .types .U-ηᴹ = refl

  M .types .Liftᴹ A γ = base (`Lift (A γ))
  M .types .Lift-[]ᴹ = refl

  M .types .lowerᴹ A γ = A γ
  M .types .lower-[]ᴹ = refl

  M .types .liftᴹ A γ = A γ
  M .types .lift-[]ᴹ = refl

  M .types .Lift-βᴹ = refl
  M .types .Lift-ηᴹ = refl

  M .types .Πᴹ A B γ = `Π (A γ) λ a → B (γ ,, a)
  M .types .Π-[]ᴹ = refl

  M .types .appᴹ f a γ = f γ (a γ)
  M .types .app-[]ᴹ = refl

  M .types .lamᴹ b γ a = b (γ ,, a)
  M .types .lam-[]ᴹ = refl

  M .types .Π-βᴹ = refl
  M .types .Π-ηᴹ = refl
