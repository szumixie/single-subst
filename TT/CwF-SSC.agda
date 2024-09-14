{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
#-}

module TT.CwF-SSC where

open import TT.Lib
open import TT.SSC.Syntax
open import TT.SSC.Parallel
import TT.CwF.Syntax as C
open import TT.CwF.Ind

module C→S where
  open DM
  open DModel

  M : DModel
  M .sorts .Conᴹ _ = Con
  M .sorts .Subᴹ Δ Γ _ = Tms Δ Γ
  M .sorts .Tyᴹ Γ i _ = Ty Γ i
  M .sorts .Tmᴹ Γ A _ = Tm Γ A

  M .core ._∘ᴹ_ = _∘ᵗ_
  M .core .assocᴹ = dep assocᵗ

  M .core .idᴹ = idᵗ
  M .core .idrᴹ = dep idrᵗ
  M .core .idlᴹ = dep idlᵗ

  M .core ._[_]ᵀᴹ = _[_]ᵀᵗ
  M .core .[]ᵀ-∘ᴹ {γᴹ = γᵗ} {δᴹ = δᵗ} = dep ([]ᵀ-∘ᵗ γᵗ δᵗ)
  M .core .[]ᵀ-idᴹ = dep []ᵀ-idᵗ

  M .core ._[_]ᵗᴹ = _[_]ᵗᵗ
  M .core .[]ᵗ-∘ᴹ {γᴹ = γᵗ} {δᴹ = δᵗ} = []ᵗ-∘ᵗ γᵗ δᵗ
  M .core .[]ᵗ-idᴹ = []ᵗ-idᵗ

  M .core .◇ᴹ = ◇
  M .core .εᴹ = ε
  M .core .ε-∘ᴹ = reflᵈ
  M .core .◇-ηᴹ = reflᵈ

  M .core ._▹ᴹ_ = _▹_
  M .core .pᴹ = pᵗ
  M .core .qᴹ = qᵗ

  M .core ._,ᴹ_ = _,_
  M .core .,-∘ᴹ = reflᵈ

  M .core .▹-β₁ᴹ {γᴹ = γᵗ} = dep (▹-β₁ᵗ γᵗ)
  M .core .▹-β₂ᴹ {γᴹ = γᵗ} = ▹-β₂ᵗ γᵗ
  M .core .▹-ηᴹ = reflᵈ

  M .types .Uᴹ = U
  M .types .U-[]ᴹ {γᴹ = γᵗ} = dep (U-[]ᵗ γᵗ)

  M .types .Elᴹ = El
  M .types .El-[]ᴹ {γᴹ = γᵗ} = dep (El-[]ᵗ γᵗ)

  M .types .cᴹ = c
  M .types .c-[]ᴹ {γᴹ = γᵗ} = c-[]ᵗ γᵗ

  M .types .U-βᴹ = dep U-β
  M .types .U-ηᴹ = dep U-η

  M .types .Liftᴹ = Lift
  M .types .Lift-[]ᴹ {γᴹ = γᵗ} = dep (Lift-[]ᵗ γᵗ)

  M .types .lowerᴹ = lower
  M .types .lower-[]ᴹ {γᴹ = γᵗ} = dep (lower-[]ᵗ γᵗ)

  M .types .liftᴹ = lift
  M .types .lift-[]ᴹ {γᴹ = γᵗ} = lift-[]ᵗ γᵗ

  M .types .Lift-βᴹ = dep Lift-β
  M .types .Lift-ηᴹ = dep Lift-η

  M .types .Πᴹ = Π
  M .types .Π-[]ᴹ {γᴹ = γᵗ} = dep (Π-[]ᵗ γᵗ)

  M .types .appᴹ = appᵗ
  M .types .app-[]ᴹ {γᴹ = γᵗ} = app-[]ᵗ γᵗ

  M .types .lamᴹ = lam
  M .types .lam-[]ᴹ {γᴹ = γᵗ} = lam-[]ᵗ γᵗ

  M .types .Π-βᴹ = dep Π-βᵗ
  M .types .Π-ηᴹ = Π-ηᵗ

  open Ind M public

open C→S public using ()
  renaming (⟦_⟧ᶜ to C→Sᶜ; ⟦_⟧ˢ to C→T; ⟦_⟧ᵀ to C→Sᵀ; ⟦_⟧ᵗ to C→Sᵗ)

private variable
  Γ Δ : C.Con
  γ₀ γ₁ : C.Sub Δ Γ

ap-C→T : γ₀ ≡ γ₁ → C→T γ₀ ≡ C→T γ₁
ap-C→T refl = refl
