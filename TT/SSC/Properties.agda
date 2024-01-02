{-# OPTIONS
  --with-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
  --hidden-argument-puns #-}

module TT.SSC.Properties where

open import TT.Lib
open import TT.SSC
open import TT.SSC.AlphaNf

private variable
  i j : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A A₀ A₁ B : Ty Γ i
  b : Tm Γ A
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

opaque
  unfolding coe
  ap-++ : Ω₀ ≡ Ω₁ → (Γ ++ Ω₀) ≡ (Γ ++ Ω₁)
  ap-++ refl = refl

  ap-▹ᵀˡ : (Ω₀₁ : Ω₀ ≡ Ω₁) → A₀ ≡[ ap-Ty (ap-++ Ω₀₁) ] A₁ → (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁)
  ap-▹ᵀˡ refl refl = refl

  ▹-inj₁ : (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁) → Ω₀ ≡ Ω₁
  ▹-inj₁ refl = refl

  ▹-inj₂ :
    {A₀ : Ty (Γ ++ Ω₀) i} {A₁ : Ty (Γ ++ Ω₁) i} →
    (ΩA₀₁ : (Ω₀ ▹ A₀) ≡ (Ω₁ ▹ A₁)) → A₀ ≡[ ap-Ty (ap-++ (▹-inj₁ ΩA₀₁)) ] A₁
  ▹-inj₂ refl = refl

module _ (γʷ : Wk Δ Γ γ) where
  var-p-⁺-⁺^ʷ₀ :
    {A : Ty Γ i}
    (Ω-p-⁺ᵀˡ : Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ Ω [ γ ]ᵀˡ [ p ]ᵀˡ ∈ Tel (Δ ▹ A [ γ ]ᵀ))
    (x : Var (Γ ++ Ω) B) →
    Σₚ[ B-p-⁺ᵀ-⁺^ ∈
      B [ p ⁺^ ]ᵀ [ γ ⁺ ⁺^ ]ᵀ ≡[ ap-Ty (ap-++ Ω-p-⁺ᵀˡ) ]
      B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j ]
    var x [ p ⁺^ ]ᵗ [ γ ⁺ ⁺^ ]ᵗ ≡[ ap-Tm (ap-++ Ω-p-⁺ᵀˡ) B-p-⁺ᵀ-⁺^ ]
    var x [ γ ⁺^ ]ᵗ [ p ⁺^ ]ᵗ
      ∈ Tm (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) (B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ)
  var-p-⁺-⁺^ʷ₀ {Ω = ◇} ◇-p-⁺ᵀˡ x .fst = dep p-⁺ᵀ
  var-p-⁺-⁺^ʷ₀ {Ω = ◇} ◇-p-⁺ᵀˡ x .snd = dep (ap-[]ᵗ var-p) ∙ᵈ vs-⁺

  var-p-⁺-⁺^ʷ₀ {Ω = Ω ▹ A} Ω▹A-p-⁺ᵀˡ vz .fst =
    dep (ap-[]ᵀ p-⁺ᵀ ∙ p-⁺ᵀ) ∙ᵈ
    apᵈ-[]ᵀ
      (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ))
      (ap-▹ (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ))
      (▹-inj₂ Ω▹A-p-⁺ᵀˡ)
      (apᵈ-p (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ)) ∙ᵈ
    dep (sym p-⁺ᵀ ∙ ap-[]ᵀ (sym p-⁺ᵀ))
  var-p-⁺-⁺^ʷ₀ {Ω = Ω ▹ A} Ω▹A-p-⁺ᵀˡ vz .snd =
    apᵈ-[]ᵗ refl refl (dep p-⁺ᵀ) vz-⁺ reflᵈ ∙ᵈ
    vz-⁺ ∙ᵈ
    apᵈ-var
      (ap-++ Ω▹A-p-⁺ᵀˡ)
      (apᵈ-[]ᵀ
        (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ))
        (ap-▹ (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ))
        (▹-inj₂ Ω▹A-p-⁺ᵀˡ)
        (apᵈ-p (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ)))
      (apᵈ-vz (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ)) ∙ᵈ
    symᵈ vz-⁺ ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym p-⁺ᵀ)) (symᵈ vz-⁺) reflᵈ

  var-p-⁺-⁺^ʷ₀ {Ω = Ω ▹ A} Ω▹A-p-⁺ᵀˡ (vs x) .fst =
    dep (ap-[]ᵀ p-⁺ᵀ ∙ p-⁺ᵀ) ∙ᵈ
    apᵈ-[]ᵀ
      (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ))
      (ap-▹ (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ))
      (var-p-⁺-⁺^ʷ₀ (▹-inj₁ Ω▹A-p-⁺ᵀˡ) x .fst)
      (apᵈ-p (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ)) ∙ᵈ
    dep (sym p-⁺ᵀ ∙ ap-[]ᵀ (sym p-⁺ᵀ))
  var-p-⁺-⁺^ʷ₀ {Ω = Ω ▹ A} Ω▹A-p-⁺ᵀˡ (vs x) .snd =
    apᵈ-[]ᵗ refl refl (dep p-⁺ᵀ)
      (vs-⁺ ∙ᵈ dep (ap-[]ᵗ (var-[]ʷ (p ⁺^ʷ)) ∙ var-p))
      reflᵈ ∙ᵈ
    vs-⁺ ∙ᵈ
    apᵈ-[]ᵗ
      (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ))
      (ap-▹ (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ))
      (var-p-⁺-⁺^ʷ₀ (▹-inj₁ Ω▹A-p-⁺ᵀˡ) x .fst)
      ( dep (ap-[]ᵗ (sym (var-[]ʷ (p ⁺^ʷ)))) ∙ᵈ
        var-p-⁺-⁺^ʷ₀ (▹-inj₁ Ω▹A-p-⁺ᵀˡ) x .snd ∙ᵈ
        dep (ap-[]ᵗ (var-[]ʷ (γʷ ⁺^ʷ))))
      (apᵈ-p (ap-++ (▹-inj₁ Ω▹A-p-⁺ᵀˡ)) (▹-inj₂ Ω▹A-p-⁺ᵀˡ)) ∙ᵈ
    symᵈ vs-⁺ ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym p-⁺ᵀ))
      (dep (sym var-p ∙ ap-[]ᵗ (sym (var-[]ʷ (γʷ ⁺^ʷ)))) ∙ᵈ symᵈ vs-⁺)
      reflᵈ

  p-⁺ᵀ-⁺^ʷ₀ :
    {A : Ty Γ i}
    (Ω-p-⁺ᵀˡ : Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ Ω [ γ ]ᵀˡ [ p ]ᵀˡ ∈ Tel (Δ ▹ A [ γ ]ᵀ)) →
    NTy (Γ ++ Ω) j B →
    B [ p ⁺^ ]ᵀ [ γ ⁺ ⁺^ ]ᵀ ≡[ ap-Ty (ap-++ Ω-p-⁺ᵀˡ) ]
    B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j
  p-⁺ᵗ-⁺^ʷ₀ :
    {A : Ty Γ i}
    (Ω-p-⁺ᵀˡ : Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ Ω [ γ ]ᵀˡ [ p ]ᵀˡ ∈ Tel (Δ ▹ A [ γ ]ᵀ)) →
    NTm (Γ ++ Ω) B b →
    Σₚ[ B-p-⁺ᵀ-⁺^ ∈
      B [ p ⁺^ ]ᵀ [ γ ⁺ ⁺^ ]ᵀ ≡[ ap-Ty (ap-++ Ω-p-⁺ᵀˡ) ]
      B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j ]
    b [ p ⁺^ ]ᵗ [ γ ⁺ ⁺^ ]ᵗ ≡[ ap-Tm (ap-++ Ω-p-⁺ᵀˡ) B-p-⁺ᵀ-⁺^ ]
    b [ γ ⁺^ ]ᵗ [ p ⁺^ ]ᵗ
      ∈ Tm (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) (B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ)

  p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (Uᴺ i) =
    dep (ap-[]ᵀ U-[] ∙ U-[]) ∙ᵈ
    apᵈ-U (ap-++ Ω-p-⁺ᵀˡ) ∙ᵈ
    dep (sym U-[] ∙ ap-[]ᵀ (sym U-[]))
  p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (Elᴺ αᴺ) =
    dep (ap-[]ᵀ El-[] ∙ El-[]) ∙ᵈ
    apᵈ-El (ap-++ Ω-p-⁺ᵀˡ)
      (splitlr
        (symᵈ (coe-[]ᵗ U-[]) ∙ᵈ p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ αᴺ .snd ∙ᵈ coe-[]ᵗ U-[])) ∙ᵈ
    dep (sym El-[] ∙ ap-[]ᵀ (sym El-[]))
  p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (Πᴺ Aᴺ Bᴺ) =
    dep (ap-[]ᵀ Π-[] ∙ Π-[]) ∙ᵈ
    apᵈ-Π
      (ap-++ Ω-p-⁺ᵀˡ)
      (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)
      (p-⁺ᵀ-⁺^ʷ₀ (ap-▹ᵀˡ Ω-p-⁺ᵀˡ (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)) Bᴺ) ∙ᵈ
    dep (sym Π-[] ∙ ap-[]ᵀ (sym Π-[]))

  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (varᴺ x) = var-p-⁺-⁺^ʷ₀ Ω-p-⁺ᵀˡ x
  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (cᴺ Aᴺ) .fst =
    dep (ap-[]ᵀ U-[] ∙ U-[]) ∙ᵈ
    apᵈ-U (ap-++ Ω-p-⁺ᵀˡ) ∙ᵈ
    dep (sym U-[] ∙ ap-[]ᵀ (sym U-[]))
  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (cᴺ Aᴺ) .snd =
    apᵈ-[]ᵗ refl refl (dep U-[]) c-[] reflᵈ ∙ᵈ
    c-[] ∙ᵈ
    apᵈ-c (ap-++ Ω-p-⁺ᵀˡ) (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ) ∙ᵈ
    symᵈ c-[] ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym U-[])) (symᵈ c-[]) reflᵈ

  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (appᴺ _ Bᴺ fᴺ aᴺ) .fst =
    dep (ap-[]ᵀ ⟨⟩-[]ᵀ ∙ ⟨⟩-[]ᵀ) ∙ᵈ
    apᵈ-[]ᵀ
      (ap-▹ (ap-++ Ω-p-⁺ᵀˡ) (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .fst))
      (ap-++ Ω-p-⁺ᵀˡ)
      (p-⁺ᵀ-⁺^ʷ₀ (ap-▹ᵀˡ Ω-p-⁺ᵀˡ (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .fst)) Bᴺ)
      (apᵈ-⟨⟩
        (ap-++ Ω-p-⁺ᵀˡ)
        (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .fst)
        (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .snd)) ∙ᵈ
    dep (sym ⟨⟩-[]ᵀ ∙ ap-[]ᵀ (sym ⟨⟩-[]ᵀ))
  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (appᴺ _ Bᴺ fᴺ aᴺ) .snd =
    apᵈ-[]ᵗ refl refl (dep ⟨⟩-[]ᵀ) app-[] reflᵈ ∙ᵈ
    app-[] ∙ᵈ
    apᵈ-app
      (ap-++ Ω-p-⁺ᵀˡ)
      (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .fst)
      (p-⁺ᵀ-⁺^ʷ₀ (ap-▹ᵀˡ Ω-p-⁺ᵀˡ (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .fst)) Bᴺ)
      (splitlr
        (symᵈ (coe-[]ᵗ Π-[]) ∙ᵈ p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ fᴺ .snd ∙ᵈ coe-[]ᵗ Π-[]))
      (p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ aᴺ .snd) ∙ᵈ
    symᵈ app-[] ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym ⟨⟩-[]ᵀ)) (symᵈ app-[]) reflᵈ

  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (lamᴺ Aᴺ _ bᴺ) .fst =
    dep (ap-[]ᵀ Π-[] ∙ Π-[]) ∙ᵈ
    apᵈ-Π
      (ap-++ Ω-p-⁺ᵀˡ)
      (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)
      (p-⁺ᵗ-⁺^ʷ₀ (ap-▹ᵀˡ Ω-p-⁺ᵀˡ (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)) bᴺ .fst) ∙ᵈ
    dep (sym Π-[] ∙ ap-[]ᵀ (sym Π-[]))
  p-⁺ᵗ-⁺^ʷ₀ Ω-p-⁺ᵀˡ (lamᴺ Aᴺ _ bᴺ) .snd =
    apᵈ-[]ᵗ refl refl (dep Π-[]) lam-[] reflᵈ ∙ᵈ
    lam-[] ∙ᵈ
    apᵈ-lam
      (ap-++ Ω-p-⁺ᵀˡ)
      (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)
      (p-⁺ᵗ-⁺^ʷ₀ (ap-▹ᵀˡ Ω-p-⁺ᵀˡ (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)) bᴺ .fst)
      (p-⁺ᵗ-⁺^ʷ₀ (ap-▹ᵀˡ Ω-p-⁺ᵀˡ (p-⁺ᵀ-⁺^ʷ₀ Ω-p-⁺ᵀˡ Aᴺ)) bᴺ .snd) ∙ᵈ
    symᵈ lam-[] ∙ᵈ
    apᵈ-[]ᵗ refl refl (dep (sym Π-[])) (symᵈ lam-[]) reflᵈ

  p-⁺ᵀˡʷ : Ω [ p ]ᵀˡ [ γ ⁺ ]ᵀˡ ≡ Ω [ γ ]ᵀˡ [ p ]ᵀˡ ∈ Tel (Δ ▹ A [ γ ]ᵀ)
  p-⁺ᵀˡʷ {Ω = ◇} = refl
  p-⁺ᵀˡʷ {Ω = Ω ▹ A} = ap-▹ᵀˡ p-⁺ᵀˡʷ (p-⁺ᵀ-⁺^ʷ₀ p-⁺ᵀˡʷ (normᵀ A))

  p-⁺ᵀ-⁺^ʷ :
    {A : Ty Γ i} {B : Ty (Γ ++ Ω) j} →
    B [ p ⁺^ ]ᵀ [ γ ⁺ ⁺^ ]ᵀ ≡[ ap-Ty (ap-++ p-⁺ᵀˡʷ) ]
    B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ ∈ Ty (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) j
  p-⁺ᵀ-⁺^ʷ {B} = p-⁺ᵀ-⁺^ʷ₀ p-⁺ᵀˡʷ (normᵀ B)

  p-⁺ᵗ-⁺^ʷ :
    {A : Ty Γ i} {b : Tm (Γ ++ Ω) B} →
    b [ p ⁺^ ]ᵗ [ γ ⁺ ⁺^ ]ᵗ ≡[ ap-Tm (ap-++ p-⁺ᵀˡʷ) p-⁺ᵀ-⁺^ʷ ]
    b [ γ ⁺^ ]ᵗ [ p ⁺^ ]ᵗ
      ∈ Tm (Δ ▹ A [ γ ]ᵀ ++ Ω [ γ ]ᵀˡ [ p ]ᵀˡ) (B [ γ ⁺^ ]ᵀ [ p ⁺^ ]ᵀ)
  p-⁺ᵗ-⁺^ʷ {b} = p-⁺ᵗ-⁺^ʷ₀ p-⁺ᵀˡʷ (normᵗ b) .snd

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
