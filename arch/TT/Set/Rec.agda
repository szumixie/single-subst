{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.HLevels

import TT.Set as I
open import TT.Set.Model

module TT.Set.Rec {ℓ}{ℓ'}(M : Model {ℓ}{ℓ'}) where

open Model M

-- TODO: this seems to be and Agda bug

⟦_⟧UU : I.UU → UU
⟦_⟧EL : ∀{a} → I.EL a → EL ⟦ a ⟧UU

⟦ I.Con'                                    ⟧UU = Con'
⟦ I.Sub' Γ Δ                                ⟧UU = Sub' ⟦ Γ ⟧EL ⟦ Δ ⟧EL
⟦ I.Ty' Γ                                   ⟧UU = Ty' ⟦ Γ ⟧EL
⟦ I.Tm' Γ A                                 ⟧UU = Tm' ⟦ Γ ⟧EL ⟦ A ⟧EL
⟦ I.ConSet Γ₀ Γ₁ Γe₀ Γe₁ i j                ⟧EL = ConSet ⟦ Γ₀ ⟧EL ⟦ Γ₁ ⟧EL (λ i → ⟦ Γe₀ i ⟧EL) (λ i → ⟦ Γe₁ i ⟧EL) i j
⟦ I.SubSet σ₀ σ₁ σe₀ σe₁ i j                ⟧EL = SubSet ⟦ σ₀ ⟧EL ⟦ σ₁ ⟧EL (λ i → ⟦ σe₀ i ⟧EL) (λ i → ⟦ σe₁ i ⟧EL) i j
⟦ σ I.∘ δ                                   ⟧EL = ⟦ σ ⟧EL ∘ ⟦ δ ⟧EL
⟦ I.ass σ δ ν i                             ⟧EL = ass ⟦ σ ⟧EL ⟦ δ ⟧EL ⟦ ν ⟧EL i
⟦ I.id                                      ⟧EL = id
⟦ I.idl {σ = σ} i                           ⟧EL = idl {σ = ⟦ σ ⟧EL} i
⟦ I.idr {σ = σ} i                           ⟧EL = idr {σ = ⟦ σ ⟧EL} i
⟦ I.◆                                       ⟧EL = ◆
⟦ I.ε                                       ⟧EL = ε
⟦ I.◆η σ i                                  ⟧EL = ◆η ⟦ σ ⟧EL i
⟦ I.TySet A₀ A₁ Ae₀ Ae₁ i j                 ⟧EL = TySet ⟦ A₀ ⟧EL ⟦ A₁ ⟧EL (λ i → ⟦ Ae₀ i ⟧EL) (λ i → ⟦ Ae₁ i ⟧EL) i j
⟦ A I.[ σ ]T                                ⟧EL = ⟦ A ⟧EL [ ⟦ σ ⟧EL ]T
⟦ (A I.[ σ ∣ δ ]T) i                        ⟧EL = (⟦ A ⟧EL [ ⟦ σ ⟧EL ∣ ⟦ δ ⟧EL ]T) i
⟦ (A I.[id]T) i                             ⟧EL = (⟦ A ⟧EL [id]T) i
⟦ I.TmSet t₀ t₁ te₀ te₁ i j                 ⟧EL = TmSet ⟦ t₀ ⟧EL ⟦ t₁ ⟧EL (λ i → ⟦ te₀ i ⟧EL) (λ i → ⟦ te₁ i ⟧EL) i j
⟦ t I.[ σ ]t                                ⟧EL = ⟦ t ⟧EL [ ⟦ σ ⟧EL ]t
⟦ (t I.[ σ ∣ δ ]t) i                        ⟧EL = (⟦ t ⟧EL [ ⟦ σ ⟧EL ∣ ⟦ δ ⟧EL ]t) i
⟦ (t I.[id]t) i                             ⟧EL = (⟦ t ⟧EL [id]t) i
⟦ Γ I.▹ A                                   ⟧EL = ⟦ Γ ⟧EL ▹ ⟦ A ⟧EL
⟦ σ I.,s t                                  ⟧EL = ⟦ σ ⟧EL ,s ⟦ t ⟧EL
⟦ I.π₁ σ                                    ⟧EL = π₁ ⟦ σ ⟧EL
⟦ I.π₂ {Γ}{Δ}{A} σ                          ⟧EL = π₂ {⟦ Γ ⟧EL}{⟦ Δ ⟧EL}{⟦ A ⟧EL} ⟦ σ ⟧EL
⟦ I.▹β₁ {σ = σ}{t = t} i                    ⟧EL = ▹β₁ {σ = ⟦ σ ⟧EL}{t = ⟦ t ⟧EL} i
⟦ I.▹β₂ {σ = σ}{t = t} i                    ⟧EL = ▹β₂ {σ = ⟦ σ ⟧EL}{t = ⟦ t ⟧EL} i
⟦ I.▹η {σ = σ} i                            ⟧EL = ▹η {σ = ⟦ σ ⟧EL} i
⟦ I.π₁∘ {σ = σ}{δ = δ} i                    ⟧EL = π₁∘ {σ = ⟦ σ ⟧EL}{δ = ⟦ δ ⟧EL} i
⟦ (A I.[π₁ σ ∣ δ ]T) i                      ⟧EL = (⟦ A ⟧EL [π₁ ⟦ σ ⟧EL ∣ ⟦ δ ⟧EL ]T) i
⟦ I.π₂[] {σ = σ}{δ = δ} i                   ⟧EL = π₂[] {σ = ⟦ σ ⟧EL}{δ = ⟦ δ ⟧EL} i
⟦ σ I.^ A                                   ⟧EL = ⟦ σ ⟧EL ^ ⟦ A ⟧EL
⟦ (I.id^ A) i                               ⟧EL = (id^ ⟦ A ⟧EL) i
⟦ I.∘^ σ δ i                                ⟧EL = ∘^ ⟦ σ ⟧EL ⟦ δ ⟧EL i
⟦ (A I.[id^]T) i                            ⟧EL = (⟦ A ⟧EL [id^]T) i
⟦ (A I.[∘^]) i                              ⟧EL = (⟦ A ⟧EL [∘^]) i
⟦ I.^=₁ i                                   ⟧EL = ^=₁ i
⟦ (A I.[π₁^]) i                             ⟧EL = (⟦ A ⟧EL [π₁^]) i
⟦ I.^=₂ i                                   ⟧EL = ^=₂ i
⟦ I.Π A B                                   ⟧EL = Π ⟦ A ⟧EL ⟦ B ⟧EL
⟦ I.lam t                                   ⟧EL = lam ⟦ t ⟧EL
⟦ I.app t                                   ⟧EL = app ⟦ t ⟧EL
⟦ I.Πβ {t = t} i                            ⟧EL = Πβ {t = ⟦ t ⟧EL} i
⟦ I.Πη {t = t} i                            ⟧EL = Πη {t = ⟦ t ⟧EL} i
⟦ I.Π[] A B σ i                             ⟧EL = Π[] ⟦ A ⟧EL ⟦ B ⟧EL ⟦ σ ⟧EL i
⟦ I.lam[] t σ i                             ⟧EL = lam[] ⟦ t ⟧EL ⟦ σ ⟧EL i
⟦ I.U                                       ⟧EL = U
⟦ I.U[ σ ] i                                ⟧EL = U[ ⟦ σ ⟧EL ] i
⟦ a I.[ σ ]U                                ⟧EL = ⟦ a ⟧EL [ ⟦ σ ⟧EL ]U
⟦ (a I.[ σ ]U=) i                           ⟧EL = (⟦ a ⟧EL [ ⟦ σ ⟧EL ]U=) i
⟦ (a I.[id]U) i                             ⟧EL = (⟦ a ⟧EL [id]U) i
⟦ (a I.[ σ ∣ δ ]U) i                        ⟧EL = (⟦ a ⟧EL [ ⟦ σ ⟧EL ∣ ⟦ δ ⟧EL ]U) i
⟦ I.El a                                    ⟧EL = El ⟦ a ⟧EL
⟦ I.El a [ σ ] i                            ⟧EL = El ⟦ a ⟧EL [ ⟦ σ ⟧EL ] i

