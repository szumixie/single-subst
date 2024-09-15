{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Examples where

-- basic examples using our single substitution syntax

open import TT.Lib
open import TT.SSC.Syntax

_⇒_ : ∀{Γ i} → Ty Γ i → Ty Γ i → Ty Γ i
A ⇒ B = Π A (B [ p ]ᵀ)

El' : ∀{Γ Δ i}(γ : Sub Δ Γ) → Tm Δ (U i [ γ ]ᵀ) → Ty Δ i
El' γ t = El (coe (ap-Tm U-[]) t)

idFun : Tm ◇ (Π (U zero) (Lift (El' p q) ⇒ Lift (El' p q)))
idFun = lam (lam q)

-- coe (ap ... e) q = q

-- idFunβ : ∀{A : Ty ◇ zero}{a : Tm ◇ A} → app (lower (coe (ap-Tm (Lift-[] ∙ ap-Lift Π-[])) (app (idFun) (c A)))) (coe (ap-Tm (sym U-β ∙ ap-El (undep (splitr {!!})) ∙ sym El-[])) a) ≡ {!!}
-- idFunβ = {!!}

-- difficulties working with single substitutions:
-- * cannot simply weaken closed things into arbitrary contexts
-- * 

-- TODO: dependent function composition, S, K, maybe dependent versions, with their substitution rules
-- Church encoding of Bool
