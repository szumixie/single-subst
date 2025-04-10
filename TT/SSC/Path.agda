{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Path where

open import TT.Lib
open import TT.SSC.Syntax

private variable
  i j : ℕ
  Γ Γ₀ Γ₁ Δ Δ₀ Δ₁ Θ : Con
  γ : Sub Δ Γ
  A A₀ A₁ B : Ty Γ i
  a a₀ a₁ b f α : Tm Γ A

infixl 9 _∘_
data Sub* : Con → Con → Set where
  ⌜_⌝ : Sub Δ Γ → Sub* Δ Γ
  _∘_ : Sub* Δ Γ → Sub* Θ Δ → Sub* Θ Γ
  id : Sub* Γ Γ

infixl 9 _[_]ᵀ*
_[_]ᵀ* : Ty Γ i → Sub* Δ Γ → Ty Δ i
A [ ⌜ γ ⌝ ]ᵀ* = A [ γ ]ᵀ
A [ γ* ∘ δ* ]ᵀ* = A [ γ* ]ᵀ* [ δ* ]ᵀ*
A [ id ]ᵀ* = A

infixl 9 _[_]ᵗ*
_[_]ᵗ* : Tm Γ A → (γ* : Sub* Δ Γ) → Tm Δ (A [ γ* ]ᵀ*)
a [ ⌜ γ ⌝ ]ᵗ* = a [ γ ]ᵗ
a [ γ* ∘ δ* ]ᵗ* = a [ γ* ]ᵗ* [ δ* ]ᵗ*
a [ id ]ᵗ* = a

private variable
  γ*₀ γ*₁ δ*₀ δ*₁ : Sub* Δ Γ

opaque
  unfolding coe

  ap-Sub* : Δ₀ ≡ Δ₁ → Γ₀ ≡ Γ₁ → Sub* Δ₀ Γ₀ ≡ Sub* Δ₁ Γ₁
  ap-Sub* refl refl = refl

  ap-[]ᵀ* : A₀ ≡ A₁ → (γ* : Sub* Δ Γ) → A₀ [ γ* ]ᵀ* ≡ A₁ [ γ* ]ᵀ*
  ap-[]ᵀ* refl γ* = refl

  apᵈ-[]ᵀ* :
    (Γ₀₁ : Γ₀ ≡ Γ₁) → A₀ ≡[ ap-Ty Γ₀₁ ] A₁ →
    (Δ₀₁ : Δ₀ ≡ Δ₁) → γ*₀ ≡[ ap-Sub* Δ₀₁ Γ₀₁ ] γ*₁ →
    A₀ [ γ*₀ ]ᵀ* ≡[ ap-Ty Δ₀₁ ] A₁ [ γ*₁ ]ᵀ*
  apᵈ-[]ᵀ* refl refl refl refl = refl

  ap-[]ᵗ* : a₀ ≡ a₁ → (γ* : Sub* Δ Γ) → a₀ [ γ* ]ᵗ* ≡ a₁ [ γ* ]ᵗ*
  ap-[]ᵗ* refl γ* = refl

  apᵈ-[]ᵗ* :
    (A₀₁ : A₀ ≡ A₁) → a₀ ≡[ ap-Tm A₀₁ ] a₁ → (γ* : Sub* Δ Γ) →
    a₀ [ γ* ]ᵗ* ≡[ ap-Tm (ap-[]ᵀ* A₀₁ γ*) ] a₁ [ γ* ]ᵗ*
  apᵈ-[]ᵗ* refl refl γ* = refl

ε* : Sub* Γ ◇
ε* {Γ = ◇} = id
ε* {Γ = Γ ▹ A} = ε* ∘ ⌜ p ⌝

ε*-[]ᵀ : A [ ε* ]ᵀ* [ γ ]ᵀ ≡ A [ ε* ]ᵀ*
ε*-[]ᵀ {γ = p} = refl
ε*-[]ᵀ {γ = γ ⁺} = p-⁺ᵀ ∙ ap-[]ᵀ ε*-[]ᵀ
ε*-[]ᵀ {γ = ⟨ a ⟩} = p-⟨⟩ᵀ

ε*-[]ᵗ :
  {A : Ty ◇ i} {a : Tm ◇ A} {γ : Sub Δ Γ} →
  a [ ε* ]ᵗ* [ γ ]ᵗ ≡[ ap-Tm ε*-[]ᵀ ] a [ ε* ]ᵗ*
ε*-[]ᵗ {γ = p} = reflᵈ
ε*-[]ᵗ {γ = γ ⁺} = p-⁺ᵗ ∙ᵈ apᵈ-[]ᵗ ε*-[]ᵀ ε*-[]ᵗ
ε*-[]ᵗ {γ = ⟨ a ⟩} = p-⟨⟩ᵗ

ε-[]ᵀ* : (γ* : Sub* Δ Γ) → A [ ε* ]ᵀ* [ γ* ]ᵀ* ≡ A [ ε* ]ᵀ*
ε-[]ᵀ* ⌜ γ ⌝ = ε*-[]ᵀ
ε-[]ᵀ* (γ* ∘ δ*) = ap-[]ᵀ* (ε-[]ᵀ* γ*) δ* ∙ ε-[]ᵀ* δ*
ε-[]ᵀ* id = refl

ε-[]ᵗ* :
  {A : Ty ◇ i} {a : Tm ◇ A} (γ* : Sub* Δ Γ) →
  a [ ε* ]ᵗ* [ γ* ]ᵗ* ≡[ ap-Tm (ε-[]ᵀ* γ*) ] a [ ε* ]ᵗ*
ε-[]ᵗ* ⌜ γ ⌝ = ε*-[]ᵗ
ε-[]ᵗ* (γ* ∘ δ*) = apᵈ-[]ᵗ* (ε-[]ᵀ* γ*) (ε-[]ᵗ* γ*) δ* ∙ᵈ ε-[]ᵗ* δ*
ε-[]ᵗ* id = reflᵈ

infixl 10 _⁺*
_⁺* : (γ* : Sub* Δ Γ) → Sub* (Δ ▹ A [ γ* ]ᵀ*) (Γ ▹ A)
⌜ γ ⌝ ⁺* = ⌜ γ ⁺ ⌝
(γ* ∘ δ*) ⁺* = γ* ⁺* ∘ δ* ⁺*
id ⁺* = id

p-⁺ᵀ* :
  (γ* : Sub* Δ Γ) →
  B [ p ]ᵀ [ γ* ⁺* ]ᵀ* ≡ B [ γ* ]ᵀ* [ p ]ᵀ ∈ Ty (Δ ▹ A [ γ* ]ᵀ*) j
p-⁺ᵀ* ⌜ γ ⌝ = p-⁺ᵀ
p-⁺ᵀ* (γ* ∘ δ*) = ap-[]ᵀ* (p-⁺ᵀ* γ*) (δ* ⁺*) ∙ p-⁺ᵀ* δ*
p-⁺ᵀ* id = refl

p-⁺ᵗ* :
  (γ* : Sub* Δ Γ) →
  b [ p ]ᵗ [ γ* ⁺* ]ᵗ* ≡[ ap-Tm (p-⁺ᵀ* γ*) ]
  b [ γ* ]ᵗ* [ p ]ᵗ ∈ Tm (Δ ▹ A [ γ* ]ᵀ*) (B [ γ* ]ᵀ* [ p ]ᵀ)
p-⁺ᵗ* ⌜ γ ⌝ = p-⁺ᵗ
p-⁺ᵗ* (γ* ∘ δ*) = apᵈ-[]ᵗ* (p-⁺ᵀ* γ*) (p-⁺ᵗ* γ*) (δ* ⁺*) ∙ᵈ p-⁺ᵗ* δ*
p-⁺ᵗ* id = reflᵈ

q-⁺* :
  (γ* : Sub* Δ Γ) →
  q [ γ* ⁺* ]ᵗ* ≡[ ap-Tm (p-⁺ᵀ* γ*) ]
  q ∈ Tm (Δ ▹ A [ γ* ]ᵀ*) (A [ γ* ]ᵀ* [ p ]ᵀ)
q-⁺* ⌜ γ ⌝ = q-⁺
q-⁺* (γ* ∘ δ*) = apᵈ-[]ᵗ* (p-⁺ᵀ* γ*) (q-⁺* γ*) (δ* ⁺*) ∙ᵈ q-⁺* δ*
q-⁺* id = reflᵈ

infixl 4 _,*_
_,*_ : (γ* : Sub* Δ Γ) → Tm Δ (A [ γ* ]ᵀ*) → Sub* Δ (Γ ▹ A)
γ* ,* a = γ* ⁺* ∘ ⌜ ⟨ a ⟩ ⌝

▹-β₁ᵀ* :
  (γ* : Sub* Δ Γ) {a : Tm Δ (A [ γ* ]ᵀ*)} →
  B [ p ]ᵀ [ γ* ,* a ]ᵀ* ≡ B [ γ* ]ᵀ*
▹-β₁ᵀ* γ* = ap-[]ᵀ (p-⁺ᵀ* γ*) ∙ p-⟨⟩ᵀ

▹-β₁ᵗ* :
  (γ* : Sub* Δ Γ) {a : Tm Δ (A [ γ* ]ᵀ*)} →
  b [ p ]ᵗ [ γ* ,* a ]ᵗ* ≡[ ap-Tm (▹-β₁ᵀ* γ*) ] b [ γ* ]ᵗ*
▹-β₁ᵗ* γ* = apᵈ-[]ᵗ (p-⁺ᵀ* γ*) (p-⁺ᵗ* γ*) ∙ᵈ p-⟨⟩ᵗ

▹-β₂* :
  (γ* : Sub* Δ Γ) {a : Tm Δ (A [ γ* ]ᵀ*)} →
  q [ γ* ,* a ]ᵗ* ≡[ ap-Tm (▹-β₁ᵀ* γ*) ] a
▹-β₂* γ* = apᵈ-[]ᵗ (p-⁺ᵀ* γ*) (q-⁺* γ*) ∙ᵈ q-⟨⟩

⟨⟩-[]ᵀ* :
  (γ* : Sub* Δ Γ) → B [ ⟨ a ⟩ ]ᵀ [ γ* ]ᵀ* ≡ B [ γ* ⁺* ]ᵀ* [ ⟨ a [ γ* ]ᵗ* ⟩ ]ᵀ
⟨⟩-[]ᵀ* ⌜ γ ⌝ = ⟨⟩-[]ᵀ
⟨⟩-[]ᵀ* (γ* ∘ δ*) = ap-[]ᵀ* (⟨⟩-[]ᵀ* γ*) δ* ∙ ⟨⟩-[]ᵀ* δ*
⟨⟩-[]ᵀ* id = refl

U-[]* : (γ* : Sub* Δ Γ) → U i [ γ* ]ᵀ* ≡ U i
U-[]* ⌜ γ ⌝ = U-[]
U-[]* (γ* ∘ δ*) = ap-[]ᵀ* (U-[]* γ*) δ* ∙ U-[]* δ*
U-[]* id = refl

El-[]* :
  (γ* : Sub* Δ Γ) → El α [ γ* ]ᵀ* ≡ El (coe (ap-Tm (U-[]* γ*)) (α [ γ* ]ᵗ*))
El-[]* ⌜ γ ⌝ = El-[]
El-[]* (γ* ∘ δ*) =
  ap-[]ᵀ* (El-[]* γ*) δ* ∙
  El-[]* δ* ∙
  ap-El (splitr (apᵈ-[]ᵗ* (sym (U-[]* γ*)) (splitl reflᵈ) δ*))
El-[]* id = ap-El (undep refl)

c-[]* : (γ* : Sub* Δ Γ) → c A [ γ* ]ᵗ* ≡[ ap-Tm (U-[]* γ*) ] c (A [ γ* ]ᵀ*)
c-[]* ⌜ γ ⌝ = c-[]
c-[]* (γ* ∘ δ*) = apᵈ-[]ᵗ* (U-[]* γ*) (c-[]* γ*) δ* ∙ᵈ c-[]* δ*
c-[]* id = reflᵈ

Lift-[]* : (γ* : Sub* Δ Γ) → Lift A [ γ* ]ᵀ* ≡ Lift (A [ γ* ]ᵀ*)
Lift-[]* ⌜ γ ⌝ = Lift-[]
Lift-[]* (γ* ∘ δ*) = ap-[]ᵀ* (Lift-[]* γ*) δ* ∙ Lift-[]* δ*
Lift-[]* id = refl

lower-[]* :
  (γ* : Sub* Δ Γ) →
  lower a [ γ* ]ᵗ* ≡ lower (coe (ap-Tm (Lift-[]* γ*)) (a [ γ* ]ᵗ*))
lower-[]* ⌜ γ ⌝ = lower-[]
lower-[]* (γ* ∘ δ*) =
  ap-[]ᵗ* (lower-[]* γ*) δ* ∙
  lower-[]* δ* ∙
  ap-lower (splitr (apᵈ-[]ᵗ* (sym (Lift-[]* γ*)) (splitl reflᵈ) δ*))
lower-[]* id = ap-lower (undep refl)

lift-[]* :
  (γ* : Sub* Δ Γ) → lift a [ γ* ]ᵗ* ≡[ ap-Tm (Lift-[]* γ*) ] lift (a [ γ* ]ᵗ*)
lift-[]* ⌜ γ ⌝ = lift-[]
lift-[]* (γ* ∘ δ*) = apᵈ-[]ᵗ* (Lift-[]* γ*) (lift-[]* γ*) δ* ∙ᵈ lift-[]* δ*
lift-[]* id = reflᵈ

Π-[]* : (γ* : Sub* Δ Γ) → Π A B [ γ* ]ᵀ* ≡ Π (A [ γ* ]ᵀ*) (B [ γ* ⁺* ]ᵀ*)
Π-[]* ⌜ γ ⌝ = Π-[]
Π-[]* (γ* ∘ δ*) = ap-[]ᵀ* (Π-[]* γ*) δ* ∙ Π-[]* δ*
Π-[]* id = refl

app-[]* :
  (γ* : Sub* Δ Γ) →
  app f a [ γ* ]ᵗ* ≡[ ap-Tm (⟨⟩-[]ᵀ* γ*) ]
  app (coe (ap-Tm (Π-[]* γ*)) (f [ γ* ]ᵗ*)) (a [ γ* ]ᵗ*)
app-[]* ⌜ γ ⌝ = app-[]
app-[]* (γ* ∘ δ*) =
  apᵈ-[]ᵗ* (⟨⟩-[]ᵀ* γ*) (app-[]* γ*) δ* ∙ᵈ
  app-[]* δ* ∙ᵈ
  dep (ap-app (splitr (apᵈ-[]ᵗ* (sym (Π-[]* γ*)) (splitl reflᵈ) δ*)))
app-[]* id = dep (ap-app (undep refl))

lam-[]* :
  (γ* : Sub* Δ Γ) → lam b [ γ* ]ᵗ* ≡[ ap-Tm (Π-[]* γ*) ] lam (b [ γ* ⁺* ]ᵗ*)
lam-[]* ⌜ γ ⌝ = lam-[]
lam-[]* (γ* ∘ δ*) = apᵈ-[]ᵗ* (Π-[]* γ*) (lam-[]* γ*) δ* ∙ᵈ lam-[]* δ*
lam-[]* id = reflᵈ
