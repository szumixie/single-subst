{-# OPTIONS --with-K --rewriting #-}

module STT.Lib where

open import Level public
open import Function public using (_∋_)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; cong; cong₂; subst) renaming (trans to infixr 9 _∙_)
open import Agda.Builtin.Equality.Rewrite
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK public

postulate
  funext : ∀ {ℓ₀ ℓ₁} → Extensionality ℓ₀ ℓ₁

funextᵢ : ∀ {ℓ₀ ℓ₁} → ExtensionalityImplicit ℓ₀ ℓ₁
funextᵢ = implicit-extensionality funext
