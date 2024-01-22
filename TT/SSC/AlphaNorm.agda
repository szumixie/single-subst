{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections #-}

module TT.SSC.AlphaNorm where

open import TT.Lib
open import TT.SSC.Syntax
open import TT.SSC.Ind

private variable
  i : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A A₀ A₁ B : Ty Γ i
  a a₀ a₁ b f α : Tm Γ A

data Var : (Γ : Con) (A : Ty Γ i) → Tm Γ A → Set where
  vz : Var (Γ ▹ A) (A [ p ]ᵀ) q
  vs : Var Γ B b → Var (Γ ▹ A) (B [ p ]ᵀ) (b [ p ]ᵗ)

data NTy : (Γ : Con) (i : ℕ) → Ty Γ i → Prop
data NTm : (Γ : Con) (A : Ty Γ i) → Tm Γ A → Prop

data NTy where
  Uᴺ : (i : ℕ) → NTy Γ (suc i) (U i)
  Elᴺ : NTm Γ (U i) α → NTy Γ i (El α)
  Πᴺ : NTy Γ i A → NTy (Γ ▹ A) i B → NTy Γ i (Π A B)

data NTm where
  var : Var Γ A a → NTm Γ A a
  cᴺ : NTy Γ i A → NTm Γ (U i) (c A)

  appᴺ :
    NTy Γ i A → NTy (Γ ▹ A) i B →
    NTm Γ (Π A B) f → NTm Γ A a → NTm Γ (B [ ⟨ a ⟩ ]ᵀ) (app f a)
  lamᴺ : NTy Γ i A → NTy (Γ ▹ A) i B → NTm (Γ ▹ A) B b → NTm Γ (Π A B) (lam b)

opaque
  unfolding coe

  ap-NTy : A₀ ≡ A₁ → NTy Γ i A₀ ≡ NTy Γ i A₁
  ap-NTy refl = refl

  ap-NTm : (A₀₁ : A₀ ≡ A₁) → a₀ ≡[ ap-Tm A₀₁ ] a₁ → NTm Γ A₀ a₀ ≡ NTm Γ A₁ a₁
  ap-NTm refl refl = refl

  ap-Var : (A₀₁ : A₀ ≡ A₁) → a₀ ≡[ ap-Tm A₀₁ ] a₁ → Var Γ A₀ a₀ ≡ Var Γ A₁ a₁
  ap-Var refl refl = refl

module []ᴺᴾ
  (Subᴾ : (Δ Γ : Con) → Sub Δ Γ → Set)
  (_⁺ᴾ :
    ∀ {Γ Δ i} {A : Ty Γ i} {γ} → Subᴾ Δ Γ γ → Subᴾ (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺))
  (let infixl 10 _⁺ᴾ; _⁺ᴾ = _⁺ᴾ)
  (_[_]ᵛᴾ :
    ∀ {Γ Δ i} {A : Ty Γ i} {a γ} →
    Var Γ A a → Subᴾ Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ))
  (let infixl 9 _[_]ᵛᴾ; _[_]ᵛᴾ = _[_]ᵛᴾ)
  where
  infixl 9 _[_]ᵀᴺᴾ _[_]ᵗᴺᴾ
  _[_]ᵀᴺᴾ : NTy Γ i A → Subᴾ Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
  _[_]ᵗᴺᴾ : NTm Γ A a → Subᴾ Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)

  Uᴺ i [ γᴾ ]ᵀᴺᴾ = coeₚ (ap-NTy (sym U-[])) (Uᴺ i)
  Elᴺ αᴺ [ γᴾ ]ᵀᴺᴾ =
    coeₚ (ap-NTy (sym El-[])) (Elᴺ (coeₚ (ap-NTm U-[] refl) (αᴺ [ γᴾ ]ᵗᴺᴾ)))
  Πᴺ Aᴺ Bᴺ [ γᴾ ]ᵀᴺᴾ =
    coeₚ (ap-NTy (sym Π-[])) (Πᴺ (Aᴺ [ γᴾ ]ᵀᴺᴾ) (Bᴺ [ γᴾ ⁺ᴾ ]ᵀᴺᴾ))

  var aᵛ [ γᴾ ]ᵗᴺᴾ = aᵛ [ γᴾ ]ᵛᴾ
  cᴺ Aᴺ [ γᴾ ]ᵗᴺᴾ = coeₚ (ap-NTm (sym U-[]) (symᵈ c-[])) (cᴺ (Aᴺ [ γᴾ ]ᵀᴺᴾ))

  appᴺ Aᴺ Bᴺ fᴺ aᴺ [ γᴾ ]ᵗᴺᴾ =
    coeₚ (ap-NTm (sym ⟨⟩-[]ᵀ) (symᵈ app-[]))
      (appᴺ
        (Aᴺ [ γᴾ ]ᵀᴺᴾ)
        (Bᴺ [ γᴾ ⁺ᴾ ]ᵀᴺᴾ)
        (coeₚ (ap-NTm Π-[] refl) (fᴺ [ γᴾ ]ᵗᴺᴾ))
        (aᴺ [ γᴾ ]ᵗᴺᴾ))
  lamᴺ Aᴺ Bᴺ bᴺ [ γᴾ ]ᵗᴺᴾ =
    coeₚ (ap-NTm (sym Π-[]) (symᵈ lam-[]))
      (lamᴺ (Aᴺ [ γᴾ ]ᵀᴺᴾ) (Bᴺ [ γᴾ ⁺ᴾ ]ᵀᴺᴾ) (bᴺ [ γᴾ ⁺ᴾ ]ᵗᴺᴾ))

data Wk : (Δ Γ : Con) → Sub Δ Γ → Set where
  p : Wk (Γ ▹ A) Γ p
  _⁺ : Wk Δ Γ γ → Wk (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)

infixl 9 _[_]ᵛʷ
_[_]ᵛʷ : Var Γ A a → Wk Δ Γ γ → Var Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
aᵛ [ p ]ᵛʷ = vs aᵛ
vz [ γʷ ⁺ ]ᵛʷ = coe (ap-Var (sym p-⁺ᵀ) (symᵈ q-⁺)) vz
vs aᵛ [ γʷ ⁺ ]ᵛʷ = coe (ap-Var (sym p-⁺ᵀ) (symᵈ p-⁺ᵗ)) (vs (aᵛ [ γʷ ]ᵛʷ))

open []ᴺᴾ Wk _⁺ (λ aᵛ γʷ → var (aᵛ [ γʷ ]ᵛʷ))
  renaming (_[_]ᵀᴺᴾ to _[_]ᵀᴺʷ; _[_]ᵗᴺᴾ to _[_]ᵗᴺʷ)

data NSSub : (Δ Γ : Con) → Sub Δ Γ → Set where
  _⁺ : NSSub Δ Γ γ → NSSub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)
  ⟨_⟩ : NTm Γ A a → NSSub Γ (Γ ▹ A) ⟨ a ⟩

infixl 9 _[_]ᵛᴺˢ
_[_]ᵛᴺˢ : Var Γ A a → NSSub Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
vz [ γᴺˢ ⁺ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⁺ᵀ) (symᵈ q-⁺)) (var vz)
vs bᵛ [ γᴺˢ ⁺ ]ᵛᴺˢ =
  coeₚ (ap-NTm (sym p-⁺ᵀ) (symᵈ p-⁺ᵗ)) (bᵛ [ γᴺˢ ]ᵛᴺˢ [ p ]ᵗᴺʷ)
vz [ ⟨ aᴺ ⟩ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⟨⟩ᵀ) (symᵈ q-⟨⟩)) aᴺ
vs bᵛ [ ⟨ aᴺ ⟩ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⟨⟩ᵀ) (symᵈ p-⟨⟩ᵗ)) (var bᵛ)

open []ᴺᴾ NSSub _⁺ _[_]ᵛᴺˢ renaming (_[_]ᵀᴺᴾ to _[_]ᵀᴺˢ; _[_]ᵗᴺᴾ to _[_]ᵗᴺˢ)

data NSub (Δ Γ : Con) (γ : Sub Δ Γ) : Set where
  wk : Wk Δ Γ γ → NSub Δ Γ γ
  nssub : NSSub Δ Γ γ → NSub Δ Γ γ

infixl 9 _[_]ᵀᴺ
_[_]ᵀᴺ : NTy Γ i A → NSub Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
Aᴺ [ wk γʷ ]ᵀᴺ = Aᴺ [ γʷ ]ᵀᴺʷ
Aᴺ [ nssub γᴺˢ ]ᵀᴺ = Aᴺ [ γᴺˢ ]ᵀᴺˢ

infixl 9 _[_]ᵗᴺ
_[_]ᵗᴺ : NTm Γ A a → NSub Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
aᴺ [ wk γʷ ]ᵗᴺ = aᴺ [ γʷ ]ᵗᴺʷ
aᴺ [ nssub γᴺˢ ]ᵗᴺ = aᴺ [ γᴺˢ ]ᵗᴺˢ

infixl 10 _⁺ᴺ
_⁺ᴺ : NSub Δ Γ γ → NSub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)
wk γʷ ⁺ᴺ = wk (γʷ ⁺)
nssub γᴺˢ ⁺ᴺ = nssub (γᴺˢ ⁺)

module norm where
  open DM
  open DModel

  M : DModel
  M .sorts .Conᴹ _ = ⊤
  M .sorts .Subᴹ _ _ = NSub _ _
  M .sorts .Tyᴹ _ _ A = Lift (NTy _ _ A)
  M .sorts .Tmᴹ _ _ a = Lift (NTm _ _ a)

  M .core ._[_]ᵀᴹ (lift Aᴺ) γᴺ = lift (Aᴺ [ γᴺ ]ᵀᴺ)
  M .core ._[_]ᵗᴹ (lift aᴺ) γᴺ = lift (aᴺ [ γᴺ ]ᵗᴺ)

  M .core .◇ᴹ = ⋆
  M .core ._▹ᴹ_ _ _ = ⋆

  M .core .pᴹ = wk p
  M .core .qᴹ = lift (var vz)

  M .core ._⁺ᴹ = _⁺ᴺ
  M .core .p-⁺ᵀᴹ = refl

  M .core .p-⁺ᵗᴹ = refl
  M .core .q-⁺ᴹ = refl

  M .core .⟨_⟩ᴹ (lift aᴺ) = nssub ⟨ aᴺ ⟩
  M .core .p-⟨⟩ᵀᴹ = refl

  M .core .p-⟨⟩ᵗᴹ = refl
  M .core .q-⟨⟩ᴹ = refl

  M .core .⟨⟩-[]ᵀᴹ = refl
  M .core .▹-ηᵀᴹ = refl

  M .types .Uᴹ i = lift (Uᴺ i)
  M .types .U-[]ᴹ = refl

  M .types .Elᴹ (lift αᴺ) = lift (Elᴺ αᴺ)
  M .types .El-[]ᴹ = refl

  M .types .cᴹ (lift Aᴺ) = lift (cᴺ Aᴺ)
  M .types .c-[]ᴹ = refl

  M .types .U-βᴹ = refl
  M .types .U-ηᴹ = refl

  M .types .Πᴹ (lift Aᴺ) (lift Bᴺ) = lift (Πᴺ Aᴺ Bᴺ)
  M .types .Π-[]ᴹ = refl

  M .types .appᴹ {Aᴹ = lift Aᴺ} {Bᴹ = lift Bᴺ} (lift fᴺ) (lift aᴺ) =
    lift (appᴺ Aᴺ Bᴺ fᴺ aᴺ)
  M .types .app-[]ᴹ = refl

  M .types .lamᴹ {Aᴹ = lift Aᴺ} {Bᴹ = lift Bᴺ} (lift bᴺ) = lift (lamᴺ Aᴺ Bᴺ bᴺ)
  M .types .lam-[]ᴹ = refl

  M .types .Π-βᴹ = refl
  M .types .Π-ηᴹ = refl

  open Ind M public

normˢ : (γ : Sub Δ Γ) → NSub Δ Γ γ
normˢ γ = norm.⟦ γ ⟧ˢ

normᵀ : (A : Ty Γ i) → NTy Γ i A
normᵀ A = norm.⟦ A ⟧ᵀ .lower

normᵗ : (a : Tm Γ A) → NTm Γ A a
normᵗ a = norm.⟦ a ⟧ᵗ .lower
