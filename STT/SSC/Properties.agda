{-# OPTIONS
  --with-K --rewriting --postfix-projections --hidden-argument-puns #-}

module STT.SSC.Properties where

open import STT.Lib
open import STT.SSC
open import STT.SSC.SNf

private variable
  Γ Δ Θ : Con
  γ : Sub Δ Γ
  A B : Ty
  a b f : Tm Γ A
  x : Var Γ A

infixl 9 _∘_
data Sub* : Con → Con → Set where
  ⌜_⌝ : Sub Δ Γ → Sub* Δ Γ
  _∘_ : Sub* Δ Γ → Sub* Θ Δ → Sub* Θ Γ
  id : Sub* Γ Γ

_[_]* : Tm Γ A → Sub* Δ Γ → Tm Δ A
a [ ⌜ γ ⌝ ]* = a [ γ ]
a [ γ* ∘ δ* ]* = a [ γ* ]* [ δ* ]*
a [ id ]* = a

infixl 10 _⁺*
_⁺* : Sub* Δ Γ → Sub* (Δ ▹ A) (Γ ▹ A)
⌜ γ ⌝ ⁺* = ⌜ γ ⁺ ⌝
(γ* ∘ δ*) ⁺* = γ* ⁺* ∘ δ* ⁺*
id ⁺* = id

vz-⁺* : (γ* : Sub* Δ Γ) → var vz [ γ* ⁺* ]* ≡ (Tm (Δ ▹ A) A ∋ var vz)
vz-⁺* ⌜ γ ⌝ = vz-⁺
vz-⁺* (γ* ∘ δ*) = cong _[ δ* ⁺* ]* (vz-⁺* γ*) ∙ vz-⁺* δ*
vz-⁺* id = refl

app-[]* : (γ* : Sub* Δ Γ) → app f a [ γ* ]* ≡ app (f [ γ* ]*) (a [ γ* ]*)
app-[]* ⌜ γ ⌝ = app-[]
app-[]* (γ* ∘ δ*) = cong _[ δ* ]* (app-[]* γ*) ∙ app-[]* δ*
app-[]* id = refl

lam-[]* : (γ* : Sub* Δ Γ) → lam b [ γ* ]* ≡ lam (b [ γ* ⁺* ]*)
lam-[]* ⌜ γ ⌝ = lam-[]
lam-[]* (γ* ∘ δ*) = cong _[ δ* ]* (lam-[]* γ*) ∙ lam-[]* δ*
lam-[]* id = refl

Tel : Set
Tel = Con

private variable
  Ω : Tel

infixl 2 _++_
_++_ : Con → Tel → Con
Γ ++ ◇ = Γ
Γ ++ (Ω ▹ A) = (Γ ++ Ω) ▹ A

infixl 10 _⁺^
_⁺^ : Sub Δ Γ → Sub (Δ ++ Ω) (Γ ++ Ω)
_⁺^ {Ω = ◇} γ = γ
_⁺^ {Ω = Ω ▹ A} γ = γ ⁺^ ⁺

infixl 10 _⁺^*
_⁺^* : Sub* Δ Γ → Sub* (Δ ++ Ω) (Γ ++ Ω)
⌜ γ ⌝ ⁺^* = ⌜ γ ⁺^ ⌝
(γ* ∘ δ*) ⁺^* = γ* ⁺^* ∘ δ* ⁺^*
id ⁺^* = id

⁺^*-◇ : (γ* : Sub* Δ Γ) → γ* ⁺^* ≡ γ*
⁺^*-◇ ⌜ γ ⌝ = refl
⁺^*-◇ (γ* ∘ δ*) = cong₂ _∘_ (⁺^*-◇ γ*) (⁺^*-◇ δ*)
⁺^*-◇ id = refl

⁺^*-▹ : (γ* : Sub* Δ Γ) → γ* ⁺^* ≡ (Sub* (Δ ++ Ω ▹ A) (Γ ++ Ω ▹ A) ∋ γ* ⁺^* ⁺*)
⁺^*-▹ ⌜ γ ⌝ = refl
⁺^*-▹ (γ* ∘ δ*) = cong₂ _∘_ (⁺^*-▹ γ*) (⁺^*-▹ δ*)
⁺^*-▹ id = refl

module var-⁺^*→tm-⁺^*
  (γ*₀ γ*₁ : Sub* Δ Γ)
  (γ*₀₁ :
    ∀ {Ω A} {x : Var (Γ ++ Ω) A} → var x [ γ*₀ ⁺^* ]* ≡ var x [ γ*₁ ⁺^* ]*)
  where
  open NTmDModel

  M : NTmDModel _
  M .NTmᴰ Γ₀ A a _ =
    ∀ {Ω} (Γ₌ : Γ₀ ≡ (Γ ++ Ω)) →
    tm[ Γ₌ , refl ] a [ γ*₀ ⁺^* ]* ≡ tm[ Γ₌ , refl ] a [ γ*₁ ⁺^* ]*
  M .NTmᴰ-prop = funextᵢ (funext λ _ → uip _ _)
  M .varᴺᴰ x refl = γ*₀₁
  M .appᴺᴰ fᴺᴰ aᴺᴰ refl =
    app-[]* (γ*₀ ⁺^*) ∙
    cong₂ app (fᴺᴰ refl) (aᴺᴰ refl) ∙
    sym (app-[]* (γ*₁ ⁺^*))
  M .lamᴺᴰ {b} bᴺᴰ refl =
    lam-[]* (γ*₀ ⁺^*) ∙
    cong lam
      (cong (b [_]*) (sym (⁺^*-▹ γ*₀)) ∙ bᴺᴰ refl ∙ cong (b [_]*) (⁺^*-▹ γ*₁)) ∙
    sym (lam-[]* (γ*₁ ⁺^*))

  open NTmInd M public

var-⁺^*→tm-⁺^* :
  (γ*₀ γ*₁ : Sub* Δ Γ) →
  (∀ {Ω A} {x : Var (Γ ++ Ω) A} → var x [ γ*₀ ⁺^* ]* ≡ var x [ γ*₁ ⁺^* ]*) →
  ∀ {Ω A} {a : Tm (Γ ++ Ω) A} → a [ γ*₀ ⁺^* ]* ≡ a [ γ*₁ ⁺^* ]*
var-⁺^*→tm-⁺^* γ*₀ γ*₁ γ*₀₁ {a} = ⟦ norm a ⟧ refl
  where open var-⁺^*→tm-⁺^* γ*₀ γ*₁ γ*₀₁

infixl 10 _⁺^ʷ
_⁺^ʷ : Wk Δ Γ γ → Wk (Δ ++ Ω) (Γ ++ Ω) (γ ⁺^)
_⁺^ʷ {Ω = ◇} γʷ = γʷ
_⁺^ʷ {Ω = Ω ▹ A} γʷ = γʷ ⁺^ʷ ⁺

var-p-⁺-⁺^ʷ :
  {x : Var (Γ ++ Ω) B} → Wk Δ Γ γ →
  var x [ p ⁺^ ] [ γ ⁺ ⁺^ ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ var x [ γ ⁺^ ] [ p ⁺^ ])
var-p-⁺-⁺^ʷ {Ω = ◇} {γ} γʷ = cong _[ γ ⁺ ] var-p ∙ vs-⁺
var-p-⁺-⁺^ʷ {Ω = Ω ▹ B} {γ} {x = vz} γʷ =
  cong _[ γ ⁺ ⁺^ ⁺ ] vz-⁺ ∙ vz-⁺ ∙ sym vz-⁺ ∙ cong _[ p ⁺^ ⁺ ] (sym vz-⁺)
var-p-⁺-⁺^ʷ {Ω = Ω ▹ B} {γ} {x = vs x} γʷ =
  cong _[ γ ⁺ ⁺^ ⁺ ] (vs-⁺ ∙ cong _[ p ] (var-[]ʷ (p ⁺^ʷ)) ∙ var-p) ∙
  vs-⁺ ∙
  cong _[ p ]
    ( cong _[ γ ⁺ ⁺^ ] (sym (var-[]ʷ (p ⁺^ʷ))) ∙
      var-p-⁺-⁺^ʷ γʷ ∙
      cong _[ p ⁺^ ] (var-[]ʷ (γʷ ⁺^ʷ))) ∙
  sym vs-⁺ ∙
  cong _[ p ⁺^ ⁺ ]
    (sym var-p ∙ cong _[ p ] (sym (var-[]ʷ (γʷ ⁺^ʷ))) ∙ sym vs-⁺)

p-⁺-⁺^ʷ :
  {b : Tm (Γ ++ Ω) B} → Wk Δ Γ γ →
  b [ p ⁺^ ] [ γ ⁺ ⁺^ ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ b [ γ ⁺^ ] [ p ⁺^ ])
p-⁺-⁺^ʷ {γ} γʷ =
  var-⁺^*→tm-⁺^* (⌜ p ⌝ ∘ ⌜ γ ⁺ ⌝) (⌜ γ ⌝ ∘ ⌜ p ⌝) (var-p-⁺-⁺^ʷ γʷ)

var-p-⁺-⁺^ :
  {x : Var (Γ ++ Ω) B} {γ : Sub Δ Γ} →
  var x [ p ⁺^ ] [ γ ⁺ ⁺^ ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ var x [ γ ⁺^ ] [ p ⁺^ ])
var-p-⁺-⁺^ {Ω = ◇} {γ} = cong _[ γ ⁺ ] var-p ∙ vs-⁺
var-p-⁺-⁺^ {Ω = Ω ▹ B} {x = vz} {γ} =
  cong _[ γ ⁺ ⁺^ ⁺ ] vz-⁺ ∙ vz-⁺ ∙ sym vz-⁺ ∙ cong _[ p ⁺^ ⁺ ] (sym vz-⁺)
var-p-⁺-⁺^ {Ω = Ω ▹ B} {x = vs x} {γ} =
  cong _[ γ ⁺ ⁺^ ⁺ ] (vs-⁺ ∙ cong _[ p ] (var-[]ʷ (p ⁺^ʷ)) ∙ var-p) ∙
  vs-⁺ ∙
  cong _[ p ] (cong _[ γ ⁺ ⁺^ ] (sym (var-[]ʷ (p ⁺^ʷ))) ∙ var-p-⁺-⁺^) ∙
  sym (p-⁺-⁺^ʷ (p ⁺^ʷ)) ∙
  cong _[ p ⁺^ ⁺ ] (sym vs-⁺)

p-⁺-⁺^ :
  {b : Tm (Γ ++ Ω) B} {γ : Sub Δ Γ} →
  b [ p ⁺^ ] [ γ ⁺ ⁺^ ] ≡ (Tm (Δ ▹ A ++ Ω) B ∋ b [ γ ⁺^ ] [ p ⁺^ ])
p-⁺-⁺^ {γ} = var-⁺^*→tm-⁺^* (⌜ p ⌝ ∘ ⌜ γ ⁺ ⌝) (⌜ γ ⌝ ∘ ⌜ p ⌝) var-p-⁺-⁺^

p-⁺-⁺^* :
  {b : Tm (Γ ++ Ω) B} (γ* : Sub* Δ Γ) →
  b [ p ⁺^ ] [ γ* ⁺* ⁺^* ]* ≡ (Tm (Δ ▹ A ++ Ω) B ∋ b [ γ* ⁺^* ]* [ p ⁺^ ])
p-⁺-⁺^* ⌜ γ ⌝ = p-⁺-⁺^
p-⁺-⁺^* (γ* ∘ δ*) = cong _[ δ* ⁺* ⁺^* ]* (p-⁺-⁺^* γ*) ∙ p-⁺-⁺^* δ*
p-⁺-⁺^* id = refl

var-[]*→var-⁺^* :
  (γ*₀ γ*₁ : Sub* Δ Γ) →
  ({x : Var Γ A} → var x [ γ*₀ ]* ≡ var x [ γ*₁ ]*) →
  {x : Var (Γ ++ Ω) A} → var x [ γ*₀ ⁺^* ]* ≡ var x [ γ*₁ ⁺^* ]*
var-[]*→var-⁺^* {Ω = ◇} γ*₀ γ*₁ γ*₀₁ {x} =
  cong (var x [_]*) (⁺^*-◇ γ*₀) ∙ γ*₀₁ ∙ cong (var x [_]*) (sym (⁺^*-◇ γ*₁))
var-[]*→var-⁺^* {Ω = Ω ▹ A} γ*₀ γ*₁ γ*₀₁ {x = vz} =
  cong (var vz [_]*) (⁺^*-▹ γ*₀) ∙
  vz-⁺* (γ*₀ ⁺^*) ∙
  sym (vz-⁺* (γ*₁ ⁺^*)) ∙
  cong (var vz [_]*) (sym (⁺^*-▹ γ*₁))
var-[]*→var-⁺^* {Ω = Ω ▹ A} γ*₀ γ*₁ γ*₀₁ {x = vs x} =
  cong₂ _[_]* (sym var-p) (⁺^*-▹ γ*₀ ∙ sym (⁺^*-◇ (γ*₀ ⁺^* ⁺*))) ∙
  p-⁺-⁺^* (γ*₀ ⁺^*) ∙
  cong _[ p ]
    ( cong (var x [_]*) (⁺^*-◇ (γ*₀ ⁺^*)) ∙
      var-[]*→var-⁺^* γ*₀ γ*₁ γ*₀₁ ∙
      cong (var x [_]*) (sym (⁺^*-◇ (γ*₁ ⁺^*)))) ∙
  sym (p-⁺-⁺^* (γ*₁ ⁺^*)) ∙
  cong₂ _[_]* var-p (⁺^*-◇ (γ*₁ ⁺^* ⁺*) ∙ sym (⁺^*-▹ γ*₁))

var-[]*→tm-⁺^* :
  (γ*₀ γ*₁ : Sub* Δ Γ) →
  (∀ {A} {x : Var Γ A} → var x [ γ*₀ ]* ≡ var x [ γ*₁ ]*) →
  ∀ {A} {a : Tm (Γ ++ Ω) A} → a [ γ*₀ ⁺^* ]* ≡ a [ γ*₁ ⁺^* ]*
var-[]*→tm-⁺^* γ*₀ γ*₁ γ*₀₁ =
  var-⁺^*→tm-⁺^* γ*₀ γ*₁ (var-[]*→var-⁺^* γ*₀ γ*₁ γ*₀₁)

p-⟨⟩-⁺^ : {b : Tm (Γ ++ Ω) B} {a : Tm Γ A} → b [ p ⁺^ ] [ ⟨ a ⟩ ⁺^ ] ≡ b
p-⟨⟩-⁺^ {a} =
  var-[]*→tm-⁺^* (⌜ p ⌝ ∘ ⌜ ⟨ a ⟩ ⌝) id (cong _[ ⟨ a ⟩ ] var-p ∙ vs-⟨⟩)

var-⟨⟩-⁺ : var x [ ⟨ a ⟩ ] [ γ ] ≡ var x [ γ ⁺ ] [ ⟨ a [ γ ] ⟩ ]
var-⟨⟩-⁺ {x = vz} {a} {γ} =
  cong _[ γ ] vz-⟨⟩ ∙ sym vz-⟨⟩ ∙ cong _[ ⟨ a [ γ ] ⟩ ] (sym vz-⁺)
var-⟨⟩-⁺ {x = vs x} {a} {γ} =
  cong _[ γ ] vs-⟨⟩ ∙ sym p-⟨⟩-⁺^ ∙ cong _[ ⟨ a [ γ ] ⟩ ] (sym vs-⁺)

⟨⟩-⁺-⁺^ :
  {b : Tm (Γ ▹ A ++ Ω) B} {γ : Sub Δ Γ} →
  b [ ⟨ a ⟩ ⁺^ ] [ γ ⁺^ ] ≡ b [ γ ⁺ ⁺^ ] [ ⟨ a [ γ ] ⟩ ⁺^ ]
⟨⟩-⁺-⁺^ {a} {γ} =
  var-[]*→tm-⁺^* (⌜ ⟨ a ⟩ ⌝ ∘ ⌜ γ ⌝) (⌜ γ ⁺ ⌝ ∘ ⌜ ⟨ a [ γ ] ⟩ ⌝) var-⟨⟩-⁺

⟨⟩-⁺-⁺^* :
  {b : Tm (Γ ▹ A ++ Ω) B} (γ* : Sub* Δ Γ) →
  b [ ⟨ a ⟩ ⁺^ ] [ γ* ⁺^* ]* ≡ b [ γ* ⁺* ⁺^* ]* [ ⟨ a [ γ* ]* ⟩ ⁺^ ]
⟨⟩-⁺-⁺^* ⌜ γ ⌝ = ⟨⟩-⁺-⁺^
⟨⟩-⁺-⁺^* (γ* ∘ δ*) = cong _[ δ* ⁺^* ]* (⟨⟩-⁺-⁺^* γ*) ∙ ⟨⟩-⁺-⁺^* δ*
⟨⟩-⁺-⁺^* id = refl

var-▹-η : var x [ p ⁺ ] [ ⟨ var vz ⟩ ] ≡ var x
var-▹-η {x = vz} = cong _[ ⟨ var vz ⟩ ] vz-⁺ ∙ vz-⟨⟩
var-▹-η {x = vs x} = cong _[ ⟨ var vz ⟩ ] vs-⁺ ∙ p-⟨⟩-⁺^ ∙ var-p

▹-η-⁺^ : {b : Tm (Γ ▹ A ++ Ω) B} → b [ p ⁺ ⁺^ ] [ ⟨ var vz ⟩ ⁺^ ] ≡ b
▹-η-⁺^ = var-[]*→tm-⁺^* (⌜ p ⁺ ⌝ ∘ ⌜ ⟨ var vz ⟩ ⌝) id var-▹-η
