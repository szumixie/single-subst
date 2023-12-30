{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
  --postfix-projections
  --no-termination-check
#-}

module TT.SSC.AlphaNf where

open import TT.Lib
open import TT.SSC

infixl 9 _[_]ᵛʷ _[_]ᵛᴺˢ _[_]ᵀᴺ _[_]ᵗᴺ

private variable
  i : ℕ
  Γ Δ : Con
  γ : Sub Δ Γ
  A A₀ A₁ B : Ty Γ i
  a a₀ a₁ b f α : Tm Γ A

-- some derivable equalities

ap-El : a₀ ≡ a₁ → El a₀ ≡ El a₁
ap-El refl = refl

-- coe (ap-Tm )

p-⁺ᵀ : {A : Ty Γ i} → A [ p {A = B} ]ᵀ [ γ ⁺ ]ᵀ ≡ A [ γ ]ᵀ [ p ]ᵀ
p-⁺ᵀ {A = A} = {!!}
  -- ap-[]ᵀ (ap-[]ᵀ (sym U-β)) ∙ ap-[]ᵀ El-[] ∙ El-[] ∙ ap-El {!!} ∙ sym El-[] ∙ ap-[]ᵀ (sym El-[]) ∙ ap-[]ᵀ (ap-[]ᵀ U-β)


data NTy : (Γ : Con) (i : ℕ) → Ty Γ i → Prop
data Var : (Γ : Con) (A : Ty Γ i) → Tm Γ A → Prop
data NTm : (Γ : Con) (A : Ty Γ i) → Tm Γ A → Prop

data NTy where
  Uᴺ : (i : ℕ) → NTy Γ (suc i) (U i)
  Elᴺ : NTm Γ (U i) α → NTy Γ i (El α)
  Πᴺ : NTy Γ i A → NTy (Γ ▹ A) i B → NTy Γ i (Π A B)

data Var where
  vz : Var (Γ ▹ A) (A [ p ]ᵀ) q
  vs : Var Γ A a → Var (Γ ▹ B) (A [ p ]ᵀ) (a [ p ]ᵗ)

data NTm where
  varᴺ : Var Γ A a → NTm Γ A a
  cᴺ   : NTy Γ i A → NTm Γ (U i) (c A)

  appᴺ : NTy Γ i A → NTy (Γ ▹ A) i B → NTm Γ (Π A B) f → NTm Γ A a → NTm Γ (B [ ⟨ a ⟩ ]ᵀ) (app f a)
  lamᴺ : NTy Γ i A → NTy (Γ ▹ A) i B → NTm (Γ ▹ A) B b → NTm Γ (Π A B) (lam b)

opaque
  unfolding coe

  ap-NTy : A₀ ≡ A₁ → NTy Γ i A₀ ≡ NTy Γ i A₁
  ap-NTy refl = refl

  ap-Var :
     (A₀₁ : A₀ ≡ A₁) →
    a₀ ≡[ ap-Tm refl (dep A₀₁) ] a₁ →
    Var Γ A₀ a₀ ≡ Var Γ A₁ a₁
  ap-Var refl refl = refl

  ap-NTm :
    (A₀₁ : A₀ ≡ A₁) →
    a₀ ≡[ ap-Tm refl (dep A₀₁) ] a₁ →
    NTm Γ A₀ a₀ ≡ NTm Γ A₁ a₁
  ap-NTm refl refl = refl

data Wk : (Δ Γ : Con) → Sub Δ Γ → Prop where
  p : Wk (Γ ▹ A) Γ p
  _⁺ : Wk Δ Γ γ → Wk (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)

data NCon : Con → Prop where
  ◇ᴺ : NCon ◇
  _▹ᴺ_ : NCon Γ → NTy Γ i A → NCon (Γ ▹ A)

{-
-}

_[_]ᵀᴺʷ : NTy Γ i A → NCon Δ ×ₚ NCon Γ ×ₚ Wk Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
_[_]ⱽᴺʷ : Var Γ A a → NCon Δ ×ₚ NCon Γ ×ₚ Wk Δ Γ γ → Var Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
proj    : Var Γ A a → NCon Γ → NTy Γ i A
_[_]ᵗᴺʷ : NTm Γ A a → NCon Δ ×ₚ NCon Γ ×ₚ Wk Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)

Uᴺ i [ Δᴺ , Γᴺ , γᴺ ]ᵀᴺʷ = coeₚ (ap-NTy (sym U-[])) (Uᴺ i)
Elᴺ aᴺ [ Δᴺ , Γᴺ , γᴺ ]ᵀᴺʷ = coeₚ (ap-NTy (sym El-[])) (Elᴺ (coeₚ (ap-NTm U-[] refl) (aᴺ [ Δᴺ , Γᴺ , γᴺ ]ᵗᴺʷ)))
Πᴺ Aᴺ Bᴺ [ Δᴺ , Γᴺ , γᴺ ]ᵀᴺʷ = coeₚ (ap-NTy (sym Π-[])) (Πᴺ (Aᴺ [ Δᴺ , Γᴺ , γᴺ ]ᵀᴺʷ) (Bᴺ [ Δᴺ ▹ᴺ (Aᴺ [ Δᴺ , Γᴺ , γᴺ ]ᵀᴺʷ) , (Γᴺ ▹ᴺ Aᴺ) , γᴺ ⁺ ]ᵀᴺʷ))

x [ Γᴺ ▹ᴺ Aᴺ , Γᴺ , p ]ⱽᴺʷ = vs x
vz [ Δᴺ ▹ᴺ Aγᴺ , Γᴺ ▹ᴺ Aᴺ , (γᴺ ⁺) ]ⱽᴺʷ = coeₚ (ap-Var (sym p-⁺ᵀ) (symᵈ (q-⁺ p-⁺ᵀ))) vz
vs x [ Δᴺ ▹ᴺ Bγᴺ , Γᴺ ▹ᴺ Aᴺ , (γᴺ ⁺) ]ⱽᴺʷ = coeₚ (ap-Var (sym p-⁺ᵀ) (symᵈ (p-⁺ p-⁺ᵀ))) (x [ Δᴺ , Γᴺ , γᴺ ]ⱽᴺʷ [ Δᴺ ▹ᴺ Bγᴺ , Δᴺ , p ]ⱽᴺʷ)

proj vz     (Γᴺ ▹ᴺ Aᴺ) = Aᴺ [ (Γᴺ ▹ᴺ Aᴺ) , Γᴺ , p ]ᵀᴺʷ
proj (vs x) (Γᴺ ▹ᴺ Aᴺ) = proj x Γᴺ [ (Γᴺ ▹ᴺ Aᴺ) , Γᴺ , p ]ᵀᴺʷ

{-
x [ (? , ? , p) ]ⱽᴺʷ = vs x
vz {A = A} [ γᴺ ⁺ ]ⱽᴺʷ = coeₚ (ap-Var (sym (p-⁺ᵀ {!!})) (symᵈ (q-⁺ (p-⁺ᵀ {!!})))) vz
vs x [ γᴺ ⁺ ]ⱽᴺʷ = coeₚ {!!} (x [ γᴺ ]ⱽᴺʷ [ p ]ⱽᴺʷ)
-}

varᴺ x [ γᴺ ]ᵗᴺʷ = {!!}
cᴺ aᴺ [ γᴺ ]ᵗᴺʷ = {!!}
appᴺ Aᴺ Bᴺ fᴺ aᴺ [ γᴺ ]ᵗᴺʷ = {!!}
lamᴺ Aᴺ Bᴺ bᴺ [ γᴺ ]ᵗᴺʷ = {!!}

-- this is interesting: it seems that we also need NCon to show these, and we need to prove mutually the equation (A [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ A [ γ ]ᵀ [ p ]ᵀ) with defining substitution of normal forms




{-
module []ᴺᴾ
  (Subᴾ : (Δ Γ : Con) → Sub Δ Γ → Set)
  (_⁺ᴾ :
    ∀ {Γ Δ i} {A : Ty Γ i} {γ} → Subᴾ Δ Γ γ → Subᴾ (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺))
  (_[_]ᵛᴾ :
    ∀ {Γ Δ i} {A : Ty Γ i} {γ}
    (x : Var Γ A) → Subᴾ Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (var x [ γ ]ᵗ))
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

  varᴺ x [ γᴾ ]ᵗᴺᴾ = x [ γᴾ ]ᵛᴾ
  cᴺ Aᴺ [ γᴾ ]ᵗᴺᴾ = coeₚ (ap-NTm (sym U-[]) (symᵈ c-[])) (cᴺ (Aᴺ [ γᴾ ]ᵀᴺᴾ))

  appᴺ Aᴺ Bᴺ fᴺ aᴺ [ γᴾ ]ᵗᴺᴾ =
    coeₚ (ap-NTm {!Bᴺ!} {!app-[]!})
      (appᴺ (Aᴺ [ γᴾ ]ᵀᴺᴾ) (Bᴺ [ γᴾ ⁺ᴾ ]ᵀᴺᴾ) (coeₚ (ap-NTm Π-[] refl) (fᴺ [ γᴾ ]ᵗᴺᴾ)) (aᴺ [ γᴾ ]ᵗᴺᴾ))
  {-
    coeₚ (ap-NTm (sym ⟨⟩-[]ᵀ) (symᵈ app-[]))
      (appᴺ (coeₚ (ap-NTm Π-[] refl) (fᴺ [ γᴾ ]ᵗᴺᴾ)) (aᴺ [ γᴾ ]ᵗᴺᴾ))
  -}
  lamᴺ Aᴺ Bᴺ bᴺ [ γᴾ ]ᵗᴺᴾ =
    coeₚ (ap-NTm (sym Π-[]) (symᵈ lam-[])) (lamᴺ (Aᴺ [ γᴾ ]ᵀᴺᴾ) (Bᴺ [ γᴾ ⁺ᴾ ]ᵀᴺᴾ) (bᴺ [ γᴾ ⁺ᴾ ]ᵗᴺᴾ))
-}
{-

open []ᴺᴾ Wk _⁺
  (λ x γʷ → coeₚ (ap-NTm refl (dep (sym (var-[]ʷ γʷ)))) (varᴺ (x [ γʷ ]ᵛʷ)))
  renaming (_[_]ᵀᴺᴾ to _[_]ᵀᴺʷ; _[_]ᵗᴺᴾ to _[_]ᵗᴺʷ)

data NSSub : (Δ Γ : Con) → Sub Δ Γ → Set where
  _⁺ : NSSub Δ Γ γ → NSSub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)
  ⟨_⟩ : NTm Γ A a → NSSub Γ (Γ ▹ A) ⟨ a ⟩

_[_]ᵛᴺˢ : (x : Var Γ A) → NSSub Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (var x [ γ ]ᵗ)
vz [ γᴺˢ ⁺ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⁺ᵀ) (symᵈ vz-⁺)) (varᴺ vz)
vs x [ γᴺˢ ⁺ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⁺ᵀ) (symᵈ vs-⁺)) (x [ γᴺˢ ]ᵛᴺˢ [ p ]ᵗᴺʷ)
vz [ ⟨ aᴺ ⟩ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⟨⟩ᵀ) (symᵈ vz-⟨⟩)) aᴺ
vs x [ ⟨ aᴺ ⟩ ]ᵛᴺˢ = coeₚ (ap-NTm (sym p-⟨⟩ᵀ) (symᵈ vs-⟨⟩)) (varᴺ x)

open []ᴺᴾ NSSub _⁺ _[_]ᵛᴺˢ renaming (_[_]ᵀᴺᴾ to _[_]ᵀᴺˢ; _[_]ᵗᴺᴾ to _[_]ᵗᴺˢ)

data NSub (Δ Γ : Con) (γ : Sub Δ Γ) : Set where
  wk : Wk Δ Γ γ → NSub Δ Γ γ
  nssub : NSSub Δ Γ γ → NSub Δ Γ γ

_[_]ᵀᴺ : NTy Γ i A → NSub Δ Γ γ → NTy Δ i (A [ γ ]ᵀ)
Aᴺ [ wk γʷ ]ᵀᴺ = Aᴺ [ γʷ ]ᵀᴺʷ
Aᴺ [ nssub γᴺˢ ]ᵀᴺ = Aᴺ [ γᴺˢ ]ᵀᴺˢ

_[_]ᵗᴺ : NTm Γ A a → NSub Δ Γ γ → NTm Δ (A [ γ ]ᵀ) (a [ γ ]ᵗ)
aᴺ [ wk γʷ ]ᵗᴺ = aᴺ [ γʷ ]ᵗᴺʷ
aᴺ [ nssub γᴺˢ ]ᵗᴺ = aᴺ [ γᴺˢ ]ᵗᴺˢ

_⁺ᴺ : NSub Δ Γ γ → NSub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A) (γ ⁺)
wk γʷ ⁺ᴺ = wk (γʷ ⁺)
nssub γᴺˢ ⁺ᴺ = nssub (γᴺˢ ⁺)

module norm where
  open DModel

  M : DModel
  M .Conᴹ _ = ⊤
  M .Subᴹ _ _ = NSub _ _

  M .Tyᴹ _ _ A = Lift (NTy _ _ A)
  M ._[_]ᵀᴹ (lift Aᴺ) γᴺ = lift (Aᴺ [ γᴺ ]ᵀᴺ)

  M .Tmᴹ _ _ a = Lift (NTm _ _ a)
  M ._[_]ᵗᴹ (lift aᴺ) γᴺ = lift (aᴺ [ γᴺ ]ᵗᴺ)

  M .◇ᴹ = ⋆
  M ._▹ᴹ_ _ _ = ⋆
  M .pᴹ = wk p

  M .Varᴹ _ _ _ = ⊤
  M .varᴹ _ = lift (varᴺ _)

  M .vzᴹ = ⋆
  M .vsᴹ _ = ⋆
  M .var-pᴹ = refl

  M ._⁺ᴹ = _⁺ᴺ
  M .p-⁺ᵀᴹ = refl

  M .vz-⁺ᴹ = refl
  M .vs-⁺ᴹ = refl

  M .⟨_⟩ᴹ (lift aᴺ) = nssub ⟨ aᴺ ⟩
  M .p-⟨⟩ᵀᴹ = refl

  M .vz-⟨⟩ᴹ = refl
  M .vs-⟨⟩ᴹ = refl

  M .⟨⟩-[]ᵀᴹ = refl
  M .▹-ηᵀᴹ = refl

  M .Uᴹ i = lift (Uᴺ i)
  M .U-[]ᴹ = refl

  M .Elᴹ (lift αᴺ) = lift (Elᴺ αᴺ)
  M .El-[]ᴹ = refl

  M .cᴹ (lift Aᴺ) = lift (cᴺ Aᴺ)
  M .c-[]ᴹ = refl

  M .U-βᴹ = refl
  M .U-ηᴹ = refl

  M .Πᴹ (lift Aᴺ) (lift Bᴺ) = lift (Πᴺ Aᴺ Bᴺ)
  M .Π-[]ᴹ = refl

   M .appᴹ (lift fᴺ) (lift aᴺ) = lift (appᴺ fᴺ aᴺ)
  M .app-[]ᴹ = refl

  M .lamᴹ (lift bᴺ) = lift (lamᴺ bᴺ)
  M .lam-[]ᴹ = refl

  M .Π-βᴹ = refl
  M .Π-ηᴹ = refl

  open Ind M public

normˢ : (γ : Sub Δ Γ) → NSub Δ Γ γ
normˢ γ = norm.⟦ γ ⟧ˢ

normᵀ : (A : Ty Γ i) → NTy Γ i A
normᵀ A = norm.⟦ A ⟧ᵀ .lower

normᵗ : (a : Tm Γ A) → NTm Γ A a
normᵗ a = norm.⟦ a ⟧ᵗ .lower

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
