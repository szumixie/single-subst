{-# OPTIONS --with-K --rewriting #-}

module Lib where

open import Level public using (Level; _⊔_)
module ℓ = Level
open import Function public using (_∋_)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; cong; subst) renaming (trans to infixr 9 _∙_)
open import Agda.Builtin.Equality.Rewrite using ()
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK public using (uip)
open import Data.Unit public using (⊤; tt)
open import Data.Nat public using (ℕ; zero; suc)

postulate
  funext : ∀ {ℓ₀ ℓ₁} → Extensionality ℓ₀ ℓ₁

funextᵢ : ∀ {ℓ₀ ℓ₁} → ExtensionalityImplicit ℓ₀ ℓ₁
funextᵢ = implicit-extensionality funext

max : ℕ → ℕ → ℕ
max zero n = n
max m zero = m
max (suc m) (suc n) = suc (max m n)
