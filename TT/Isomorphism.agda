{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
#-}

module TT.Isomorphism where

open import TT.Lib
import TT.CwF.Syntax as CwF
import TT.SSC.Syntax as SSC
open import TT.SSC-CwF
open import TT.CwF-SSC
open import TT.SSC-CwF-SSC
open import TT.CwF-SSC-CwF
open Iso

private variable
  i : ℕ
  Γ : SSC.Con
  A : SSC.Ty Γ i

isoᶜ : Iso SSC.Con CwF.Con
isoᶜ .to = S→Cᶜ
isoᶜ .from = C→Sᶜ
isoᶜ .invl = S→C→Sᶜ
isoᶜ .invr = C→S→Cᶜ

isoᵀ : Iso (SSC.Ty Γ i) (CwF.Ty (S→Cᶜ Γ) i)
isoᵀ .to = S→Cᵀ
isoᵀ .from A = coe (SSC.ap-Ty S→C→Sᶜ) (C→Sᵀ A)
isoᵀ .invl = S→C→Sᵀ
isoᵀ .invr = C→S→Cᵀ

isoᵗ : Iso (SSC.Tm Γ A) (CwF.Tm (S→Cᶜ Γ) (S→Cᵀ A))
isoᵗ .to = S→Cᵗ
isoᵗ .from a = coe (SSC.ap-Tm₂ S→C→Sᶜ S→C→Sᵀ) (C→Sᵗ a)
isoᵗ .invl = S→C→Sᵗ
isoᵗ .invr = C→S→Cᵗ
