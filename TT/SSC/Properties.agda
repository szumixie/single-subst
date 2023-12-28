{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check #-}

module TT.SSC.Properties where

open import TT.Lib
open import TT.SSC
open import TT.SSC.AlphaNf

private variable
  i j : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A A₀ A₁ B : Ty Γ i
  x : Var Γ A

infixl 2 _++_ _▹_
infixl 9 _[_]ᵀˡ
infixl 10 _⁺^ _⁺^ʷ

data Tel (Γ : Con) : Set
_++_ : (Γ : Con) → Tel Γ → Con

data Tel Γ where
  ◇ : Tel Γ
  _▹_ : (Ω : Tel Γ) → Ty (Γ ++ Ω) i → Tel Γ

Γ ++ ◇ = Γ
Γ ++ (Ω ▹ A) = (Γ ++ Ω) ▹ A

private variable
  Ω Ω₀ Ω₁ : Tel Γ

_[_]ᵀˡ : Tel Γ → Sub Δ Γ → Tel Δ
_⁺^ : (γ : Sub Δ Γ) → Sub (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω)

◇ [ γ ]ᵀˡ = ◇
(Ω ▹ A) [ γ ]ᵀˡ = Ω [ γ ]ᵀˡ ▹ A [ γ ⁺^ ]ᵀ

_⁺^ {Ω = ◇} γ = γ
_⁺^ {Ω = Ω ▹ A} γ = γ ⁺^ ⁺

_⁺^ʷ : Wk Δ Γ γ → Wk (Δ ++ Ω [ γ ]ᵀˡ) (Γ ++ Ω) (γ ⁺^)
_⁺^ʷ {Ω = ◇} γʷ = γʷ
_⁺^ʷ {Ω = Ω ▹ A} γʷ = γʷ ⁺^ʷ ⁺

ap-++ : Ω₀ ≡ Ω₁ → (Γ ++ Ω₀) ≡ (Γ ++ Ω₁)
ap-++ refl = refl

module _
  (γʷ : Wk Δ Γ γ)
  (p-⁺ᵀˡʷ :
    ∀ {Ω} → Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ Ω [ γ ]ᵀˡ [ p ]ᵀˡ ∈ Tel (Δ ▹ A [ γ ]ᵀ))
  (p-⁺ᵀ-⁺^ʷ :
    ∀ {j Ω B} →
    B [ p ⁺^ ]ᵀ [ γ ⁺ ⁺^ ]ᵀ ≡[ ap-Ty (ap-++ p-⁺ᵀˡʷ) ]
    B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j)
  where
  var-p-⁺-⁺^ʷ₀ :
    {x : Var (Γ ++ Ω) B} →
    var x [ p ⁺^ ]ᵗ [ γ ⁺ ⁺^ ]ᵗ ≡[ ap-Tm (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ ]
    var x [ γ ⁺^ ]ᵗ [ p ⁺^ ]ᵗ
      ∈ Tm (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) (B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ)
  var-p-⁺-⁺^ʷ₀ {Ω = ◇} = dep (ap-[]ᵗ var-p) ∙ᵈ vs-⁺
  var-p-⁺-⁺^ʷ₀ {Ω = Ω ▹ B} {x = vz} =
    apᵈ-[]ᵗ refl refl (dep p-⁺ᵀ) vz-⁺ reflᵈ ∙ᵈ
    vz-⁺ ∙ᵈ
    apᵈ-var
      (ap-▹ (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ)
      (apᵈ-[]ᵀ
        (ap-++ p-⁺ᵀˡʷ)
        (ap-▹ (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ)
        p-⁺ᵀ-⁺^ʷ
        (apᵈ-p (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ))
      (apᵈ-vz (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ) ∙ᵈ
    symᵈ vz-⁺ ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym p-⁺ᵀ)) (symᵈ vz-⁺) reflᵈ
  var-p-⁺-⁺^ʷ₀ {Ω = Ω ▹ B} {x = vs x} =
    apᵈ-[]ᵗ refl refl (dep p-⁺ᵀ)
      (vs-⁺ ∙ᵈ dep (ap-[]ᵗ (var-[]ʷ (p ⁺^ʷ)) ∙ var-p))
      reflᵈ ∙ᵈ
    vs-⁺ ∙ᵈ
    apᵈ-[]ᵗ
      (ap-++ p-⁺ᵀˡʷ)
      (ap-▹ (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ)
      p-⁺ᵀ-⁺^ʷ
      ( dep (ap-[]ᵗ (sym (var-[]ʷ (p ⁺^ʷ)))) ∙ᵈ
        var-p-⁺-⁺^ʷ₀ ∙ᵈ
        dep (ap-[]ᵗ (var-[]ʷ (γʷ ⁺^ʷ))))
      (apᵈ-p (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ) ∙ᵈ
    symᵈ vs-⁺ ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym p-⁺ᵀ))
      (dep (sym var-p ∙ ap-[]ᵗ (sym (var-[]ʷ (γʷ ⁺^ʷ)))) ∙ᵈ symᵈ vs-⁺)
      reflᵈ

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
