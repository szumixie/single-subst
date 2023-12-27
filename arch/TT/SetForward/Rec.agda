{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.HLevels

import TT.SetForward as I
open import TT.SetForward.Model

module TT.SetForward.Rec {ℓ}{ℓ'}(M : Model {ℓ}{ℓ'}) where

open Model M

⟦_⟧C : I.Con → Con
⟦_⟧S : ∀{Δ Γ} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
⟦_⟧T : ∀{Γ} → I.Ty Γ → Ty ⟦ Γ ⟧C
⟦_⟧t : ∀{Γ A} → I.Tm Γ A → Tm ⟦ Γ ⟧C ⟦ A ⟧T

⟦ I.ConSet Γ₀ Γ₁ Γe₀ Γe₁ i j ⟧C = ConSet ⟦ Γ₀ ⟧C ⟦ Γ₁ ⟧C (λ i → ⟦ Γe₀ i ⟧C) (λ i → ⟦ Γe₁ i ⟧C) i j
⟦ I.◆ ⟧C = ◆
⟦ Γ I.▹ A ⟧C = ⟦ Γ ⟧C ▹ ⟦ A ⟧T

⟦ A I.[ σ ]T                                ⟧T = ⟦ A ⟧T [ ⟦ σ ⟧S ]T
⟦ I.TySet A₀ A₁ Ae₀ Ae₁ i j                 ⟧T = TySet ⟦ A₀ ⟧T ⟦ A₁ ⟧T (λ i → ⟦ Ae₀ i ⟧T) (λ i → ⟦ Ae₁ i ⟧T) i j
⟦ (A I.[ σ ∣ δ ]T) i                        ⟧T = (⟦ A ⟧T [ ⟦ σ ⟧S ∣ ⟦ δ ⟧S ]T) i
⟦ (A I.[id]T) i                             ⟧T = (⟦ A ⟧T [id]T) i
⟦ (A I.[π₁ σ ∣ δ ]T) i                      ⟧T = (⟦ A ⟧T [π₁ ⟦ σ ⟧S ∣ ⟦ δ ⟧S ]T) i
⟦ (A I.[id^]T) i                            ⟧T = (⟦ A ⟧T [id^]T) i
⟦ (A I.[∘^]) i                              ⟧T = (⟦ A ⟧T [∘^]) i
⟦ (A I.[π₁^]) i                             ⟧T = (⟦ A ⟧T [π₁^]) i
⟦ I.Π A B                                   ⟧T = Π ⟦ A ⟧T ⟦ B ⟧T
⟦ I.Π[] A B σ i                             ⟧T = Π[] ⟦ A ⟧T ⟦ B ⟧T ⟦ σ ⟧S i
⟦ I.U                                       ⟧T = U
⟦ I.U[ σ ] i                                ⟧T = U[ ⟦ σ ⟧S ] i
⟦ I.El a                                    ⟧T = El ⟦ a ⟧t
⟦ I.El a [ σ ] i                            ⟧T = El ⟦ a ⟧t [ ⟦ σ ⟧S ] i

⟦ I.SubSet σ₀ σ₁ σe₀ σe₁ i j                ⟧S = SubSet ⟦ σ₀ ⟧S ⟦ σ₁ ⟧S (λ i → ⟦ σe₀ i ⟧S) (λ i → ⟦ σe₁ i ⟧S) i j
⟦ σ I.∘ δ                                   ⟧S = ⟦ σ ⟧S ∘ ⟦ δ ⟧S
⟦ I.ass σ δ ν i                             ⟧S = ass ⟦ σ ⟧S ⟦ δ ⟧S ⟦ ν ⟧S i
⟦ I.id                                      ⟧S = id
⟦ I.idl {σ = σ} i                           ⟧S = idl {σ = ⟦ σ ⟧S} i
⟦ I.idr {σ = σ} i                           ⟧S = idr {σ = ⟦ σ ⟧S} i
⟦ I.ε                                       ⟧S = ε
⟦ I.◆η σ i                                  ⟧S = ◆η ⟦ σ ⟧S i
⟦ σ I.,s t                                  ⟧S = ⟦ σ ⟧S ,s ⟦ t ⟧t
⟦ I.π₁ σ                                    ⟧S = π₁ ⟦ σ ⟧S
⟦ I.▹β₁ {σ = σ}{t = t} i                    ⟧S = ▹β₁ {σ = ⟦ σ ⟧S}{t = ⟦ t ⟧t} i
⟦ I.▹η {σ = σ} i                            ⟧S = ▹η {σ = ⟦ σ ⟧S} i
⟦ I.π₁∘ {σ = σ}{δ = δ} i                    ⟧S = π₁∘ {σ = ⟦ σ ⟧S}{δ = ⟦ δ ⟧S} i
⟦ σ I.^ A                                   ⟧S = ⟦ σ ⟧S ^ ⟦ A ⟧T
⟦ (I.id^ A) i                               ⟧S = (id^ ⟦ A ⟧T) i
⟦ I.∘^ σ δ i                                ⟧S = ∘^ ⟦ σ ⟧S ⟦ δ ⟧S i
⟦ I.^=₁ i                                   ⟧S = ^=₁ i

⟦ I.TmSet t₀ t₁ te₀ te₁ i j                 ⟧t = TmSet ⟦ t₀ ⟧t ⟦ t₁ ⟧t (λ i → ⟦ te₀ i ⟧t) (λ i → ⟦ te₁ i ⟧t) i j
⟦ t I.[ σ ]t                                ⟧t = ⟦ t ⟧t [ ⟦ σ ⟧S ]t
⟦ (t I.[ σ ∣ δ ]t) i                        ⟧t = (⟦ t ⟧t [ ⟦ σ ⟧S ∣ ⟦ δ ⟧S ]t) i
⟦ (t I.[id]t) i                             ⟧t = (⟦ t ⟧t [id]t) i
⟦ I.π₂ {Γ}{Δ}{A} σ                          ⟧t = π₂ {⟦ Γ ⟧C}{⟦ Δ ⟧C}{⟦ A ⟧T} ⟦ σ ⟧S
⟦ I.▹β₂ {σ = σ}{t = t} i                    ⟧t = ▹β₂ {σ = ⟦ σ ⟧S}{t = ⟦ t ⟧t} i
⟦ I.π₂[] {σ = σ}{δ = δ} i                   ⟧t = π₂[] {σ = ⟦ σ ⟧S}{δ = ⟦ δ ⟧S} i
⟦ I.^=₂ i                                   ⟧t = ^=₂ i
⟦ I.lam t                                   ⟧t = lam ⟦ t ⟧t
⟦ I.app t                                   ⟧t = app ⟦ t ⟧t
⟦ I.Πβ {t = t} i                            ⟧t = Πβ {t = ⟦ t ⟧t} i
⟦ I.Πη {t = t} i                            ⟧t = Πη {t = ⟦ t ⟧t} i
⟦ I.lam[] t σ i                             ⟧t = lam[] ⟦ t ⟧t ⟦ σ ⟧S i
⟦ a I.[ σ ]U                                ⟧t = ⟦ a ⟧t [ ⟦ σ ⟧S ]U
⟦ (a I.[ σ ]U=) i                           ⟧t = (⟦ a ⟧t [ ⟦ σ ⟧S ]U=) i
⟦ (a I.[id]U) i                             ⟧t = (⟦ a ⟧t [id]U) i
⟦ (a I.[ σ ∣ δ ]U) i                        ⟧t = (⟦ a ⟧t [ ⟦ σ ⟧S ∣ ⟦ δ ⟧S ]U) i
