{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Examples where

open import TT.Lib
open import TT.SSC.Syntax

_⇒_ : ∀{Γ i} → Ty Γ i → Ty Γ i → Ty Γ i
A ⇒ B = Π A (B [ p ]ᵀ)

El' : ∀{Γ Δ i}(γ : Sub Δ Γ) → Tm Δ (U i [ γ ]ᵀ) → Ty Δ i
El' γ t = El (coe (ap-Tm U-[]) t)

postulate
  Lift'   : ∀{i Γ} → Ty Γ i → Ty Γ (suc i)
  mk      : ∀{i Γ}{A : Ty Γ i} → Tm Γ A → Tm Γ (Lift' A)
  un      : ∀{i Γ}{A : Ty Γ i} → Tm Γ (Lift' A) → Tm Γ A
  Liftβ   : ∀{i Γ}{A : Ty Γ i}{a : Tm Γ A} → un (mk a) ≡ a
  Liftη   : ∀{i Γ}{A : Ty Γ i}{a : Tm Γ (Lift' A)} → mk (un a) ≡ a
  Lift-[] : ∀{i Γ}{A : Ty Γ i}{Δ}{γ : Sub Δ Γ} → Lift' A [ γ ]ᵀ ≡ Lift' (A [ γ ]ᵀ)

ap-Lift : ∀{i Γ}{A₀ A₁ : Ty Γ i} → A₀ ≡ A₁ → Lift' A₀ ≡ Lift' A₁
ap-Lift refl = refl

idFun : Tm ◇ (Π (U zero) (Lift' (El' p q ⇒ El' p q)))
idFun = lam (mk (lam q))

idFunβ : ∀{A : Ty ◇ zero}{a : Tm ◇ A} → app (un (coe (ap-Tm (Lift-[] ∙ ap-Lift Π-[])) (app (idFun) (c A)))) (coe (ap-Tm (sym U-β ∙ ap-El {!!} ∙ sym El-[])) a) ≡ {!!}
idFunβ = {!!}

-- difficulties working with single substitutions:
-- * cannot simply weaken things into arbitrary contexts
-- * 
