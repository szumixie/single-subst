{-# OPTIONS --with-K --rewriting --postfix-projections #-}

module SSC.AlphaNf where

open import Lib
open import SSC

private variable
  ℓᵀ ℓᵗ : Level
  i : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A A₀ A₁ B : Ty Γ i
  a a₀ a₁ b f α : Tm Γ A
  x : Var Γ A

postulate
  NTy : (Γ : Con) (i : ℕ) → Ty Γ i → Set
  NTy-prop : {Aᴺ₀ Aᴺ₁ : NTy Γ i A} → Aᴺ₀ ≡ Aᴺ₁

  NTm : (Γ : Con) (A : Ty Γ i) → Tm Γ A → Set
  NTm-prop : {aᴺ₀ aᴺ₁ : NTm Γ A a} → aᴺ₀ ≡ aᴺ₁
  varᴺ : (x : Var Γ A) → NTm Γ A (var x)

  Uᴺ : (i : ℕ) → NTy Γ (suc i) (U i)
  Elᴺ : NTm Γ (U i) α → NTy Γ i (El α)
  cᴺ : NTy Γ i A → NTm Γ (U i) (c A)

  Πᴺ : NTy Γ i A → NTy (Γ ▹ A) i B → NTy Γ i (Π A B)
  appᴺ : NTm Γ (Π A B) f → NTm Γ A a → NTm Γ (B [ ⟨ a ⟩ ]ᵀ) (app f a)
  lamᴺ : NTm (Γ ▹ A) B b → NTm Γ (Π A B) (lam b)

private variable
  Aᴺ Bᴺ : NTy Γ i A
  aᴺ bᴺ fᴺ αᴺ : NTm Γ A a

nty[_] : A₀ ≡ A₁ → NTy Γ i A₀ → NTy Γ i A₁
nty[ refl ] Aᴺ = Aᴺ

ntm[_,_] :
  (A₀₁ : A₀ ≡ A₁) → transpTm refl A₀₁ a₀ ≡ a₁ → NTm Γ A₀ a₀ → NTm Γ A₁ a₁
ntm[ refl , refl ] aᴺ = aᴺ

record NfModel ℓᵀ ℓᵗ : Set (ℓ.suc (ℓᵀ ⊔ ℓᵗ)) where
  no-eta-equality
  field
    NTyᴹ : (Γ : Con) (i : ℕ) → Ty Γ i → Set ℓᵀ
    NTy-propᴹ : {Aᴺᴹ₀ Aᴺᴹ₁ : NTyᴹ Γ i A} → Aᴺᴹ₀ ≡ Aᴺᴹ₁

    NTmᴹ : (Γ : Con) (A : Ty Γ i) → Tm Γ A → Set ℓᵗ
    NTm-propᴹ : {aᴺᴹ₀ aᴺᴹ₁ : NTmᴹ Γ A a} → aᴺᴹ₀ ≡ aᴺᴹ₁
    varᴺᴹ : (x : Var Γ A) → NTmᴹ Γ A (var x)

    Uᴺᴹ : (i : ℕ) → NTyᴹ Γ (suc i) (U i)
    Elᴺᴹ : NTmᴹ Γ (U i) α → NTyᴹ Γ i (El α)
    cᴺᴹ : NTyᴹ Γ i A → NTmᴹ Γ (U i) (c A)

    Πᴺᴹ : NTyᴹ Γ i A → NTyᴹ (Γ ▹ A) i B → NTyᴹ Γ i (Π A B)
    appᴺᴹ : NTmᴹ Γ (Π A B) f → NTmᴹ Γ A a → NTmᴹ Γ (B [ ⟨ a ⟩ ]ᵀ) (app f a)
    lamᴺᴹ : NTmᴹ (Γ ▹ A) B b → NTmᴹ Γ (Π A B) (lam b)

module NfRec (D : NfModel ℓᵀ ℓᵗ) where
  open NfModel D

  postulate
    ⟦_⟧ᵀ : NTy Γ i A → NTyᴹ Γ i A
    ⟦_⟧ᵗ : NTm Γ A a → NTmᴹ Γ A a
    ⟦⟧-varᴺ : ⟦ varᴺ x ⟧ᵗ ≡ varᴺᴹ x
    {-# REWRITE ⟦⟧-varᴺ #-}

    ⟦⟧-Uᴺ : ⟦ Uᴺ i ⟧ᵀ ≡ (NTyᴹ Γ (suc i) (U i) ∋ Uᴺᴹ i)
    {-# REWRITE ⟦⟧-Uᴺ #-}
    ⟦⟧-Elᴺ : ⟦ Elᴺ αᴺ ⟧ᵀ ≡ Elᴺᴹ ⟦ αᴺ ⟧ᵗ
    {-# REWRITE ⟦⟧-Elᴺ #-}
    ⟦⟧-cᴺ : ⟦ cᴺ Aᴺ ⟧ᵗ ≡ cᴺᴹ ⟦ Aᴺ ⟧ᵀ
    {-# REWRITE ⟦⟧-cᴺ #-}

    ⟦⟧-Πᴺ : ⟦ Πᴺ Aᴺ Bᴺ ⟧ᵀ ≡ Πᴺᴹ ⟦ Aᴺ ⟧ᵀ ⟦ Bᴺ ⟧ᵀ
    {-# REWRITE ⟦⟧-Πᴺ #-}
    ⟦⟧-appᴺ : ⟦ appᴺ fᴺ aᴺ ⟧ᵗ ≡ appᴺᴹ ⟦ fᴺ ⟧ᵗ ⟦ aᴺ ⟧ᵗ
    {-# REWRITE ⟦⟧-appᴺ #-}
    ⟦⟧-lamᴺ : ⟦ lamᴺ bᴺ ⟧ᵗ ≡ lamᴺᴹ ⟦ bᴺ ⟧ᵗ
    {-# REWRITE ⟦⟧-lamᴺ #-}

module []ᴺᴾ
  (Subᴾ : (Δ Γ : Con) → Sub Δ Γ → Set)
  (_⁺ᴾ :
    ∀ {Γ Δ i} {A : Ty Γ i} {γ} → Subᴾ Δ Γ γ → Subᴾ (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺))
  (_[_]ᵛᴾ :
    ∀ {Γ Δ i} {A : Ty Γ i} {γ}
    (x : Var Γ A) → Subᴾ Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (var x [ γ ]ᵗ))
  where
  open NfModel

  M : NfModel _ _
  M .NTyᴹ Γ i A = ∀ {Δ γ} → Subᴾ Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
  M .NTy-propᴹ = funextᵢ (funextᵢ (funext λ _ → NTy-prop))

  M .NTmᴹ Γ A a = ∀ {Δ γ} → Subᴾ Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
  M .NTm-propᴹ = funextᵢ (funextᵢ (funext λ _ → NTm-prop))
  M .varᴺᴹ x = _[_]ᵛᴾ x

  M .Uᴺᴹ i γᴾ = nty[ sym U-[] ] (Uᴺ i)
  M .Elᴺᴹ αᴺᴹ γᴾ = nty[ sym El-[] ] (Elᴺ (ntm[ U-[] , refl ] (αᴺᴹ γᴾ)))
  M .cᴺᴹ Aᴺᴹ γᴾ = ntm[ sym U-[] , sym (transpTm-shiftr c-[]) ] (cᴺ (Aᴺᴹ γᴾ))

  M .Πᴺᴹ Aᴺᴹ Bᴺᴹ γᴾ = nty[ sym Π-[] ] (Πᴺ (Aᴺᴹ γᴾ) (Bᴺᴹ (γᴾ ⁺ᴾ)))
  M .appᴺᴹ fᴺᴹ aᴺᴹ γᴾ =
    ntm[ sym ⟨⟩-[]ᵀ , sym (transpTm-shiftr app-[]) ]
      (appᴺ (ntm[ Π-[] , refl ] (fᴺᴹ γᴾ)) (aᴺᴹ γᴾ))
  M .lamᴺᴹ bᴺᴹ γᴾ =
    ntm[ sym Π-[] , sym (transpTm-shiftr lam-[]) ] (lamᴺ (bᴺᴹ (γᴾ ⁺ᴾ)))

  open NfRec M public

infixl 10 _⁺
data Wk : (Δ Γ : Con) → Sub Δ Γ → Set where
  p : Wk (Γ ▹ A) Γ p
  _⁺ : Wk Δ Γ γ → Wk (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)

infixl 9 _[_]ᵛʷ
_[_]ᵛʷ : Var Γ A → Wk Δ Γ γ → Var Δ (A [ γ ]ᵀ)
x [ p ]ᵛʷ = vs x
vz [ γʷ ⁺ ]ᵛʷ = transpVar (sym p-⁺ᵀ) vz
vs x [ γʷ ⁺ ]ᵛʷ = transpVar (sym p-⁺ᵀ) (vs (x [ γʷ ]ᵛʷ))

var-[]ʷ : (γʷ : Wk Δ Γ γ) → var x [ γ ]ᵗ ≡ var (x [ γʷ ]ᵛʷ)
var-[]ʷ p = var-p
var-[]ʷ {x = vz} (γʷ ⁺) = transpTm-shiftr vz-⁺ ∙ transp-var
var-[]ʷ {x = vs x} (γʷ ⁺) =
  transpTm-shiftr vs-⁺ ∙
  cong (transpTm _ _) (cong _[ p ]ᵗ (var-[]ʷ γʷ) ∙ var-p) ∙
  transp-var

module []ᴺʷ =
  []ᴺᴾ Wk _⁺ (λ x γʷ → ntm[ refl , sym (var-[]ʷ γʷ) ] (varᴺ (x [ γʷ ]ᵛʷ)))

infixl 9 _[_]ᵀᴺʷ
_[_]ᵀᴺʷ : NTy Γ i A → Wk Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
_[_]ᵀᴺʷ Aᴺ = []ᴺʷ.⟦ Aᴺ ⟧ᵀ

infixl 9 _[_]ᵗᴺʷ
_[_]ᵗᴺʷ : NTm Γ A a → Wk Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
_[_]ᵗᴺʷ aᴺ = []ᴺʷ.⟦ aᴺ ⟧ᵗ

data NSSub : (Δ Γ : Con) → Sub Δ Γ → Set where
  _⁺ : NSSub Δ Γ γ → NSSub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)
  ⟨_⟩ : NTm Γ A a → NSSub Γ (Γ ▹ A) ⟨ a ⟩

infixl 9 _[_]ᵛᴺˢ
_[_]ᵛᴺˢ : (x : Var Γ A) → NSSub Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (var x [ γ ]ᵗ)
vz [ γᴺˢ ⁺ ]ᵛᴺˢ = ntm[ sym p-⁺ᵀ , sym (transpTm-shiftr vz-⁺) ] (varᴺ vz)
vs x [ γᴺˢ ⁺ ]ᵛᴺˢ =
  ntm[ sym p-⁺ᵀ , sym (transpTm-shiftr vs-⁺) ] (x [ γᴺˢ ]ᵛᴺˢ [ p ]ᵗᴺʷ)
vz [ ⟨ aᴺ ⟩ ]ᵛᴺˢ = ntm[ sym p-⟨⟩ᵀ , sym (transpTm-shiftr vz-⟨⟩) ] aᴺ
vs x [ ⟨ aᴺ ⟩ ]ᵛᴺˢ = ntm[ sym p-⟨⟩ᵀ , sym (transpTm-shiftr vs-⟨⟩) ] (varᴺ x)

module []ᴺˢ = []ᴺᴾ NSSub _⁺ (λ x → x [_]ᵛᴺˢ)

infixl 9 _[_]ᵀᴺˢ
_[_]ᵀᴺˢ : NTy Γ i A → NSSub Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
_[_]ᵀᴺˢ Aᴺ = []ᴺˢ.⟦ Aᴺ ⟧ᵀ

infixl 9 _[_]ᵗᴺˢ
_[_]ᵗᴺˢ : NTm Γ A a → NSSub Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
_[_]ᵗᴺˢ aᴺ = []ᴺˢ.⟦ aᴺ ⟧ᵗ

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

_⁺ᴺ : NSub Δ Γ γ → NSub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)
wk γʷ ⁺ᴺ = wk (γʷ ⁺)
nssub γᴺˢ ⁺ᴺ = nssub (γᴺˢ ⁺)

module norm where
  open DModel

  M : DModel _ _ _ _ _
  M .Conᴹ _ = ⊤
  M .Subᴹ _ _ = NSub _ _

  M .Tyᴹ _ = NTy _
  M ._[_]ᵀᴹ = _[_]ᵀᴺ

  M .Tmᴹ _ _ = NTm _ _
  M ._[_]ᵗᴹ = _[_]ᵗᴺ

  M .◇ᴹ = tt
  M ._▹ᴹ_ _ _ = tt
  M .pᴹ = wk p

  M .Varᴹ _ _ _ = ⊤
  M .varᴹ _ = varᴺ _

  M .vzᴹ = tt
  M .vsᴹ _ = tt
  M .var-pᴹ = NTm-prop

  M ._⁺ᴹ = _⁺ᴺ
  M .p-⁺ᵀᴹ = NTy-prop

  M .vz-⁺ᴹ = NTm-prop
  M .vs-⁺ᴹ = NTm-prop

  M .⟨_⟩ᴹ aᴺ = nssub ⟨ aᴺ ⟩
  M .p-⟨⟩ᵀᴹ = NTy-prop

  M .vz-⟨⟩ᴹ = NTm-prop
  M .vs-⟨⟩ᴹ = NTm-prop

  M .⟨⟩-[]ᵀᴹ = NTy-prop
  M .▹-ηᵀᴹ = NTy-prop

  M .Uᴹ = Uᴺ
  M .U-[]ᴹ = NTy-prop

  M .Elᴹ = Elᴺ
  M .El-[]ᴹ = NTy-prop

  M .cᴹ = cᴺ
  M .c-[]ᴹ = NTm-prop

  M .U-βᴹ = NTy-prop
  M .U-ηᴹ = NTm-prop

  M .Πᴹ = Πᴺ
  M .Π-[]ᴹ = NTy-prop

  M .appᴹ = appᴺ
  M .app-[]ᴹ = NTm-prop

  M .lamᴹ = lamᴺ
  M .lam-[]ᴹ = NTm-prop

  M .Π-βᴹ = NTm-prop
  M .Π-ηᴹ = NTm-prop

  open Ind M public

normˢ : (γ : Sub Δ Γ) → NSub Δ Γ γ
normˢ γ = norm.⟦ γ ⟧ˢ

normᵀ : (A : Ty Γ i) → NTy Γ i A
normᵀ A = norm.⟦ A ⟧ᵀ

normᵗ : (a : Tm Γ A) → NTm Γ A a
normᵗ a = norm.⟦ a ⟧ᵗ

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
