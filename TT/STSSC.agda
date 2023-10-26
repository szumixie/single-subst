{-# OPTIONS --safe --without-K --postfix-projections #-}

module STSSC where

open import Function using (_∋_; _↔_; mk↔′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

module _ (Ty : Set) where
  infixl 2 _▹_
  data Con-of : Set where
    ◆ : Con-of
    _▹_ : Con-of → Ty → Con-of

record CwF : Set₁ where
  no-eta-equality

  field Ty : Set
  Con : Set
  Con = Con-of Ty

  infixl 9 _∘_ _[_]
  infixl 4 _,_
  infixr 0 _⇒_
  field
    Sub : Con → Con → Set

    _∘_ : ∀ {Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    assoc :
      ∀ {Ξ Θ Δ Γ} (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) →
      γ ∘ (δ ∘ θ) ≡ γ ∘ δ ∘ θ

    id : ∀ {Γ} → Sub Γ Γ
    idr : ∀ {Δ Γ} (γ : Sub Δ Γ) → γ ∘ id ≡ γ
    idl : ∀ {Δ Γ} (γ : Sub Δ Γ) → id ∘ γ ≡ γ

    Tm : Con → Ty → Set
    _[_] : ∀ {Δ Γ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    []-∘ :
      ∀ {Θ Δ Γ A} (a : Tm Γ A) (γ : Sub Δ Γ) (δ : Sub Θ Δ) →
      a [ γ ∘ δ ] ≡ a [ γ ] [ δ ]
    []-id : ∀ {Γ A} (a : Tm Γ A) → a [ id ] ≡ a

    ε : ∀ {Γ} → Sub Γ ◆
    ε-∘ : ∀ {Δ Γ} (γ : Sub Δ Γ) → ε ∘ γ ≡ ε
    ◆-η : ε ≡ id

    p : ∀ {Γ A} → Sub (Γ ▹ A) Γ
    q : ∀ {Γ A} → Tm (Γ ▹ A) A

    _,_ : ∀ {Δ Γ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▹ A)
    ,-∘ :
      ∀ {Θ Δ Γ A} (γ : Sub Δ Γ) (a : Tm Δ A) (δ : Sub Θ Δ) →
      (γ , a) ∘ δ ≡ (γ ∘ δ , a [ δ ])

    ▹-β₁ : ∀ {Δ Γ A} (γ : Sub Δ Γ) (a : Tm Δ A) → p ∘ (γ , a) ≡ γ
    ▹-β₂ : ∀ {Δ Γ A} (γ : Sub Δ Γ) (a : Tm Δ A) → q [ γ , a ] ≡ a
    ▹-η : ∀ {Γ A} → (p , q) ≡ id {Γ ▹ A}

    ι : Ty
    _⇒_ : Ty → Ty → Ty

    app : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    app-[] :
      ∀ {Δ Γ A B} (f : Tm Γ (A ⇒ B)) a (γ : Sub Δ Γ) →
      app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

    lam : ∀ {Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    lam-[] :
      ∀ {Δ Γ A B} (b : Tm (Γ ▹ A) B) (γ : Sub Δ Γ) →
      lam b [ γ ] ≡ lam (b [ γ ∘ p , q ])

    ⇒-β : ∀ {Γ A B} (b : Tm (Γ ▹ A) B) a → app (lam b) a ≡ b [ id , a ]
    ⇒-η : ∀ {Γ A B} (f : Tm Γ (A ⇒ B)) → lam (app (f [ p ]) q) ≡ f

module _ (Ty : Set) (Tm : Con-of Ty → Ty → Set) where
  infixl 10 _⁺
  data SSub-of : Con-of Ty → Con-of Ty → Set where
    pₛ : ∀ {Γ A} → SSub-of (Γ ▹ A) Γ
    _⁺ : ∀ {Δ Γ A} → SSub-of Δ Γ → SSub-of (Δ ▹ A) (Γ ▹ A)
    ⟨_⟩ : ∀ {Γ A} → Tm Γ A → SSub-of Γ (Γ ▹ A)

record SSC : Set₁ where
  no-eta-equality

  field Ty : Set
  Con : Set
  Con = Con-of Ty

  field Tm : Con → Ty → Set
  SSub : Con → Con → Set
  SSub = SSub-of Ty Tm

  p : ∀ {Γ A} → SSub (Γ ▹ A) Γ
  p = pₛ

  infixl 9 _[_]
  infixr 0 _⇒_
  field
    _[_] : ∀ {Δ Γ A} → Tm Γ A → SSub Δ Γ → Tm Δ A
    q : ∀ {Γ A} → Tm (Γ ▹ A) A

    p-⁺ :
      ∀ {Δ Γ A B} (b : Tm Γ B) (γ : SSub Δ Γ) →
      (Tm (Δ ▹ A) B ∋ b [ p ] [ γ ⁺ ]) ≡ b [ γ ] [ p ]
    q-⁺ : ∀ {Δ Γ A} (γ : SSub Δ Γ) → (Tm (Δ ▹ A) A ∋ q [ γ ⁺ ]) ≡ q

    ⟨⟩-[] :
      ∀ {Δ Γ A B} (b : Tm (Γ ▹ A) B) (a : Tm Γ A) (γ : SSub Δ Γ) →
      b [ ⟨ a ⟩ ] [ γ ] ≡ b [ γ ⁺ ] [ ⟨ a [ γ ] ⟩ ]
    p-⟨⟩ : ∀ {Γ A B} (b : Tm Γ B) (a : Tm Γ A) → b [ p ] [ ⟨ a ⟩ ] ≡ b
    q-⟨⟩ : ∀ {Γ A} (a : Tm Γ A) → q [ ⟨ a ⟩ ] ≡ a
    ▹-η : ∀ {Γ A B} (b : Tm (Γ ▹ A) B) → b [ p ⁺ ] [ ⟨ q ⟩ ] ≡ b

    ι : Ty
    _⇒_ : Ty → Ty → Ty

    app : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    app-[] :
      ∀ {Δ Γ A B} (f : Tm Γ (A ⇒ B)) a (γ : SSub Δ Γ) →
      app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

    lam : ∀ {Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    lam-[] :
      ∀ {Δ Γ A B} (b : Tm (Γ ▹ A) B) (γ : SSub Δ Γ) →
      lam b [ γ ] ≡ lam (b [ γ ⁺ ])

    ⇒-β : ∀ {Γ A B} (b : Tm (Γ ▹ A) B) a → app (lam b) a ≡ b [ ⟨ a ⟩ ]
    ⇒-η : ∀ {Γ A B} (f : Tm Γ (A ⇒ B)) → lam (app (f [ p ]) q) ≡ f

module CwF→SSC (M : CwF) where
  open CwF M

  SSub : Con → Con → Set
  SSub = SSub-of Ty Tm

  SS→S : ∀ {Δ Γ} → SSub Δ Γ → Sub Δ Γ
  SS→S pₛ = p
  SS→S (γ ⁺) = SS→S γ ∘ p , q
  SS→S ⟨ a ⟩ = id , a

module _ (M : CwF) where
  open CwF M
  open CwF→SSC M

  CwF→SSC : SSC
  CwF→SSC .SSC.Ty = Ty
  CwF→SSC .SSC.Tm = Tm

  CwF→SSC .SSC._[_] a γ = a [ SS→S γ ]
  CwF→SSC .SSC.q = q

  CwF→SSC .SSC.p-⁺ b γ = begin
    b [ p ] [ SS→S γ ∘ p , q ] ≡˘⟨ []-∘ _ _ _ ⟩
    b [ p ∘ (SS→S γ ∘ p , q) ] ≡⟨ cong (λ x → b [ x ]) (▹-β₁ _ _) ⟩
    b [ SS→S γ ∘ p ]           ≡⟨ []-∘ _ _ _ ⟩
    b [ SS→S γ ] [ p ]         ∎
  CwF→SSC .SSC.q-⁺ γ = ▹-β₂ _ _

  CwF→SSC .SSC.⟨⟩-[] b a γ = begin
    b [ id , a ] [ SS→S γ ]                                          ≡˘⟨ []-∘ _ _ _ ⟩
    b [ (id , a) ∘ SS→S γ ]                                          ≡⟨ cong (λ x → b [ x ]) (,-∘ _ _ _) ⟩
    b [ id ∘ SS→S γ , a [ SS→S γ ] ]                                 ≡⟨ cong (λ x → b [ x , a [ SS→S γ ] ]) (idl _) ⟩
    b [ SS→S γ , a [ SS→S γ ] ]                                      ≡˘⟨ cong (λ x → b [ x , a [ SS→S γ ] ]) (idr _) ⟩
    b [ SS→S γ ∘ id , a [ SS→S γ ] ]                                 ≡˘⟨ cong (λ x → b [ SS→S γ ∘ x , a [ SS→S γ ] ]) (▹-β₁ _ _) ⟩
    b [ SS→S γ ∘ (p ∘ (id , a [ SS→S γ ])) , a [ SS→S γ ] ]          ≡⟨ cong (λ x → b [ x , a [ SS→S γ ] ]) (assoc _ _ _) ⟩
    b [ SS→S γ ∘ p ∘ (id , a [ SS→S γ ]) , a [ SS→S γ ] ]            ≡˘⟨ cong (λ x → b [ SS→S γ ∘ p ∘ (id , a [ SS→S γ ]) , x ]) (▹-β₂ _ _) ⟩
    b [ SS→S γ ∘ p ∘ (id , a [ SS→S γ ]) , q [ id , a [ SS→S γ ] ] ] ≡˘⟨ cong (λ x → b [ x ]) (,-∘ _ _ _) ⟩
    b [ (SS→S γ ∘ p , q) ∘ (id , a [ SS→S γ ]) ]                     ≡⟨ []-∘ _ _ _ ⟩
    b [ SS→S γ ∘ p , q ] [ id , a [ SS→S γ ] ]                       ∎
  CwF→SSC .SSC.p-⟨⟩ b a = begin
    b [ p ] [ id , a ] ≡˘⟨ []-∘ _ _ _ ⟩
    b [ p ∘ (id , a) ] ≡⟨ cong (λ x → b [ x ]) (▹-β₁ _ _) ⟩
    b [ id ]           ≡⟨ []-id _ ⟩
    b                  ∎
  CwF→SSC .SSC.q-⟨⟩ a = ▹-β₂ _ _
  CwF→SSC .SSC.▹-η b = begin
    b [ p ∘ p , q ] [ id , q ]              ≡˘⟨ []-∘ _ _ _ ⟩
    b [ (p ∘ p , q) ∘ (id , q) ]            ≡⟨ cong (λ x → b [ x ]) (,-∘ _ _ _) ⟩
    b [ p ∘ p ∘ (id , q) , q [ id , q ] ]   ≡˘⟨ cong (λ x → b [ x , q [ id , q ] ]) (assoc _ _ _) ⟩
    b [ p ∘ (p ∘ (id , q)) , q [ id , q ] ] ≡⟨ cong (λ x → b [ p ∘ x , q [ id , q ] ]) (▹-β₁ _ _) ⟩
    b [ p ∘ id , q [ id , q ] ]             ≡⟨ cong (λ x → b [ x , q [ id , q ] ]) (idr _) ⟩
    b [ p , q [ id , q ] ]                  ≡⟨ cong (λ x → b [ p , x ]) (▹-β₂ _ _) ⟩
    b [ p , q ]                             ≡⟨ cong (λ x → b [ x ]) ▹-η ⟩
    b [ id ]                                ≡⟨ []-id _ ⟩
    b                                       ∎

  CwF→SSC .SSC.ι = ι
  CwF→SSC .SSC._⇒_ = _⇒_

  CwF→SSC .SSC.app = app
  CwF→SSC .SSC.app-[] f a γ = app-[] _ _ _

  CwF→SSC .SSC.lam = lam
  CwF→SSC .SSC.lam-[] b γ = lam-[] _ _

  CwF→SSC .SSC.⇒-β = ⇒-β
  CwF→SSC .SSC.⇒-η = ⇒-η

module SSC→CwF (M : SSC) where
  open SSC M

  private variable
    Γ Δ Θ Ξ : Con
    A B : Ty

  infixl 9 _∘ₛ_
  data SSubs : Con → Con → Set where
    ⌜_⌝ : SSub Δ Γ → SSubs Δ Γ
    _∘ₛ_ : SSubs Δ Γ → SSubs Θ Δ → SSubs Θ Γ
    idₛ : SSubs Γ Γ

  infixl 9 _[_]ₛ
  _[_]ₛ : Tm Γ A → SSubs Δ Γ → Tm Δ A
  a [ ⌜ γ ⌝ ]ₛ = a [ γ ]
  a [ γ ∘ₛ δ ]ₛ = a [ γ ]ₛ [ δ ]ₛ
  a [ idₛ ]ₛ = a

  infixl 10 _⁺ₛ
  _⁺ₛ : SSubs Δ Γ → SSubs (Δ ▹ A) (Γ ▹ A)
  ⌜ γ ⌝ ⁺ₛ = ⌜ γ ⁺ ⌝
  (γ ∘ₛ δ) ⁺ₛ = γ ⁺ₛ ∘ₛ δ ⁺ₛ
  idₛ ⁺ₛ = idₛ

  p-⁺ₛ :
    (b : Tm Γ B) (γ : SSubs Δ Γ) →
    (Tm (Δ ▹ A) B ∋ b [ p ] [ γ ⁺ₛ ]ₛ) ≡ b [ γ ]ₛ [ p ]
  p-⁺ₛ b ⌜ γ ⌝ = p-⁺ _ _
  p-⁺ₛ b (γ ∘ₛ δ) = begin
    b [ p ] [ γ ⁺ₛ ]ₛ [ δ ⁺ₛ ]ₛ ≡⟨ cong (λ x → x [ δ ⁺ₛ ]ₛ) (p-⁺ₛ _ γ) ⟩
    b [ γ ]ₛ [ p ] [ δ ⁺ₛ ]ₛ    ≡⟨ p-⁺ₛ _ δ ⟩
    b [ γ ]ₛ [ δ ]ₛ [ p ]       ∎
  p-⁺ₛ b idₛ = refl

  q-⁺ₛ : (γ : SSubs Δ Γ) → (Tm (Δ ▹ A) A ∋ q [ γ ⁺ₛ ]ₛ) ≡ q
  q-⁺ₛ ⌜ γ ⌝ = q-⁺ _
  q-⁺ₛ (γ ∘ₛ δ) = begin
    q [ γ ⁺ₛ ]ₛ [ δ ⁺ₛ ]ₛ ≡⟨ cong (λ x → x [ δ ⁺ₛ ]ₛ) (q-⁺ₛ γ) ⟩
    q [ δ ⁺ₛ ]ₛ           ≡⟨ q-⁺ₛ δ ⟩
    q                     ∎
  q-⁺ₛ idₛ = refl

  ⟨⟩-[]ₛ :
    (b : Tm (Γ ▹ A) B) (a : Tm Γ A) (γ : SSubs Δ Γ) →
    b [ ⟨ a ⟩ ] [ γ ]ₛ ≡ b [ γ ⁺ₛ ]ₛ [ ⟨ a [ γ ]ₛ ⟩ ]
  ⟨⟩-[]ₛ b a ⌜ γ ⌝ = ⟨⟩-[] _ _ _
  ⟨⟩-[]ₛ b a (γ ∘ₛ δ) = begin
    b [ ⟨ a ⟩ ] [ γ ]ₛ [ δ ]ₛ                     ≡⟨ cong (λ x → x [ δ ]ₛ) (⟨⟩-[]ₛ _ _ γ) ⟩
    b [ γ ⁺ₛ ]ₛ [ ⟨ a [ γ ]ₛ ⟩ ] [ δ ]ₛ           ≡⟨ ⟨⟩-[]ₛ _ _ δ ⟩
    b [ γ ⁺ₛ ]ₛ [ δ ⁺ₛ ]ₛ [ ⟨ a [ γ ]ₛ [ δ ]ₛ ⟩ ] ∎
  ⟨⟩-[]ₛ b a idₛ = refl

  app-[]ₛ :
    ∀ (f : Tm Γ (A ⇒ B)) a (γ : SSubs Δ Γ) →
    app f a [ γ ]ₛ ≡ app (f [ γ ]ₛ) (a [ γ ]ₛ)
  app-[]ₛ f a ⌜ γ ⌝ = app-[] _ _ _
  app-[]ₛ f a (γ ∘ₛ δ) = begin
    app f a [ γ ]ₛ [ δ ]ₛ                   ≡⟨ cong (λ x → x [ δ ]ₛ) (app-[]ₛ _ _ γ) ⟩
    app (f [ γ ]ₛ) (a [ γ ]ₛ) [ δ ]ₛ        ≡⟨ app-[]ₛ _ _ δ ⟩
    app (f [ γ ]ₛ [ δ ]ₛ) (a [ γ ]ₛ [ δ ]ₛ) ∎
  app-[]ₛ f a idₛ = refl

  lam-[]ₛ :
    (b : Tm (Γ ▹ A) B) (γ : SSubs Δ Γ) → lam b [ γ ]ₛ ≡ lam (b [ γ ⁺ₛ ]ₛ)
  lam-[]ₛ b ⌜ γ ⌝ = lam-[] _ _
  lam-[]ₛ b (γ ∘ₛ δ) = begin
    lam b [ γ ]ₛ [ δ ]ₛ         ≡⟨ cong (λ x → x [ δ ]ₛ) (lam-[]ₛ _ γ) ⟩
    lam (b [ γ ⁺ₛ ]ₛ) [ δ ]ₛ    ≡⟨ lam-[]ₛ _ δ ⟩
    lam (b [ γ ⁺ₛ ]ₛ [ δ ⁺ₛ ]ₛ) ∎
  lam-[]ₛ b idₛ = refl

  []-⁺ₛ→lam :
    (b : Tm (Γ ▹ A) B) (γ : SSubs Δ Γ) →
    b [ γ ⁺ₛ ]ₛ ≡ app (lam b [ γ ]ₛ [ p ]) q
  []-⁺ₛ→lam b γ = begin
    b [ γ ⁺ₛ ]ₛ                       ≡˘⟨ ▹-η _ ⟩
    b [ γ ⁺ₛ ]ₛ [ p ⁺ ] [ ⟨ q ⟩ ]     ≡˘⟨ ⇒-β _ _ ⟩
    app (lam (b [ γ ⁺ₛ ]ₛ [ p ⁺ ])) q ≡˘⟨ cong (λ x → app x q) (lam-[]ₛ _ (γ ∘ₛ ⌜ p ⌝)) ⟩
    app (lam b [ γ ]ₛ [ p ]) q        ∎

  []-⁺ₛ :
    (b : Tm (Γ ▹ A) B) (γ₀ γ₁ : SSubs Δ Γ) →
    (∀ {B} (b : Tm Γ B) → b [ γ₀ ]ₛ ≡ b [ γ₁ ]ₛ) → b [ γ₀ ⁺ₛ ]ₛ ≡ b [ γ₁ ⁺ₛ ]ₛ
  []-⁺ₛ b γ₀ γ₁ γ₀₁ = begin
    b [ γ₀ ⁺ₛ ]ₛ                ≡⟨ []-⁺ₛ→lam _ γ₀ ⟩
    app (lam b [ γ₀ ]ₛ [ p ]) q ≡⟨ cong (λ x → app (x [ p ]) q) (γ₀₁ _) ⟩
    app (lam b [ γ₁ ]ₛ [ p ]) q ≡˘⟨ []-⁺ₛ→lam _ γ₁ ⟩
    b [ γ₁ ⁺ₛ ]ₛ                ∎

  εₛ : SSubs Γ ◆
  εₛ {Γ = ◆} = idₛ
  εₛ {Γ = Γ ▹ A} = εₛ ∘ₛ ⌜ p ⌝

  εₛ-[] : (a : Tm ◆ A) (γ : SSub Δ Γ) → a [ εₛ ]ₛ [ γ ] ≡ a [ εₛ ]ₛ
  εₛ-[] a pₛ = refl
  εₛ-[] a (γ ⁺) = begin
    a [ εₛ ]ₛ [ p ] [ γ ⁺ ] ≡⟨ p-⁺ _ _ ⟩
    a [ εₛ ]ₛ [ γ ] [ p ]   ≡⟨ cong (λ x → x [ p ]) (εₛ-[] _ _) ⟩
    a [ εₛ ]ₛ [ p ]         ∎
  εₛ-[] a ⟨ z ⟩ = p-⟨⟩ _ _

  ε-[]ₛ : (a : Tm ◆ A) (γ : SSubs Δ Γ) → a [ εₛ ]ₛ [ γ ]ₛ ≡ a [ εₛ ]ₛ
  ε-[]ₛ a ⌜ γ ⌝ = εₛ-[] _ _
  ε-[]ₛ a (γ ∘ₛ δ) = begin
    a [ εₛ ]ₛ [ γ ]ₛ [ δ ]ₛ ≡⟨ cong (λ x → x [ δ ]ₛ) (ε-[]ₛ _ γ) ⟩
    a [ εₛ ]ₛ [ δ ]ₛ        ≡⟨ ε-[]ₛ _ δ ⟩
    a [ εₛ ]ₛ               ∎
  ε-[]ₛ a idₛ = refl

  infixl 4 _,ₜ_
  data Tms : Con → Con → Set where
    εₜ : Tms Γ ◆
    _,ₜ_ : Tms Δ Γ → Tm Δ A → Tms Δ (Γ ▹ A)

  T→SS : Tms Δ Γ → SSubs Δ Γ
  T→SS εₜ = εₛ
  T→SS (γ ,ₜ a) = T→SS γ ⁺ₛ ∘ₛ ⌜ ⟨ a ⟩ ⌝

  infixl 9 _[_]ₜ
  _[_]ₜ : Tm Γ A → Tms Δ Γ → Tm Δ A
  a [ γ ]ₜ = a [ T→SS γ ]ₛ

  infixl 9 _∘ₜ_
  _∘ₜ_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  _∘ₜ_ εₜ δ = εₜ
  _∘ₜ_ (γ ,ₜ a) δ = γ ∘ₜ δ ,ₜ a [ δ ]ₜ

  []-∘ₜ :
    (a : Tm Γ A) (γ : Tms Δ Γ) (δ : Tms Θ Δ) → a [ γ ∘ₜ δ ]ₜ ≡ a [ γ ]ₜ [ δ ]ₜ
  []-∘ₜ a εₜ δ = sym (ε-[]ₛ _ (T→SS δ))
  []-∘ₜ a (γ ,ₜ z) δ = begin
    a [ T→SS (γ ∘ₜ δ) ⁺ₛ ]ₛ [ ⟨ z [ T→SS δ ]ₛ ⟩ ]         ≡⟨ cong (λ x → x [ ⟨ z [ T→SS δ ]ₛ ⟩ ]) ([]-⁺ₛ _ (T→SS (γ ∘ₜ δ)) (T→SS γ ∘ₛ T→SS δ) λ a → []-∘ₜ _ γ δ) ⟩
    a [ T→SS γ ⁺ₛ ]ₛ [ T→SS δ ⁺ₛ ]ₛ [ ⟨ z [ T→SS δ ]ₛ ⟩ ] ≡˘⟨ ⟨⟩-[]ₛ _ _ (T→SS δ) ⟩
    a [ T→SS γ ⁺ₛ ]ₛ [ ⟨ z ⟩ ] [ T→SS δ ]ₛ                ∎

  assocₜ :
    (γ : Tms Δ Γ) (δ : Tms Θ Δ) (θ : Tms Ξ Θ) → γ ∘ₜ (δ ∘ₜ θ) ≡ γ ∘ₜ δ ∘ₜ θ
  assocₜ εₜ δ θ = refl
  assocₜ (γ ,ₜ a) δ θ = begin
    γ ∘ₜ (δ ∘ₜ θ) ,ₜ a [ δ ∘ₜ θ ]ₜ ≡⟨ cong (λ x → x ,ₜ a [ δ ∘ₜ θ ]ₜ) (assocₜ _ _ _) ⟩
    γ ∘ₜ δ ∘ₜ θ ,ₜ a [ δ ∘ₜ θ ]ₜ   ≡⟨ cong (λ x → γ ∘ₜ δ ∘ₜ θ ,ₜ x) ([]-∘ₜ _ δ θ) ⟩
    γ ∘ₜ δ ∘ₜ θ ,ₜ a [ δ ]ₜ [ θ ]ₜ ∎

  infixl 9 _∘pₜ
  _∘pₜ : Tms Δ Γ → Tms (Δ ▹ A) Γ
  _∘pₜ εₜ = εₜ
  _∘pₜ (γ ,ₜ z) = γ ∘pₜ ,ₜ z [ p ]

  []-∘pₜ :
    (b : Tm Γ B) (γ : Tms Δ Γ) → (Tm (Δ ▹ A) B ∋ b [ γ ∘pₜ ]ₜ) ≡ b [ γ ]ₜ [ p ]
  []-∘pₜ b εₜ = sym (εₛ-[] _ _)
  []-∘pₜ b (γ ,ₜ z) = begin
    b [ T→SS (γ ∘pₜ) ⁺ₛ ]ₛ [ ⟨ z [ p ] ⟩ ]   ≡⟨ cong (λ x → x [ ⟨ z [ p ] ⟩ ]) ([]-⁺ₛ _ (T→SS (γ ∘pₜ)) (T→SS γ ∘ₛ ⌜ p ⌝) λ b → []-∘pₜ _ γ) ⟩
    b [ T→SS γ ⁺ₛ ]ₛ [ p ⁺ ] [ ⟨ z [ p ] ⟩ ] ≡˘⟨ ⟨⟩-[] _ _ _ ⟩
    b [ T→SS γ ⁺ₛ ]ₛ [ ⟨ z ⟩ ] [ p ]         ∎

  ∘p-,ₜ : (γ : Tms Δ Γ) (δ : Tms Θ Δ) (a : Tm Θ A) → γ ∘pₜ ∘ₜ (δ ,ₜ a) ≡ γ ∘ₜ δ
  ∘p-,ₜ εₜ δ a = refl
  ∘p-,ₜ (γ ,ₜ z) δ a = begin
    γ ∘pₜ ∘ₜ (δ ,ₜ a) ,ₜ z [ p ] [ T→SS δ ⁺ₛ ]ₛ [ ⟨ a ⟩ ] ≡⟨ cong (λ x → x ,ₜ z [ p ] [ T→SS δ ⁺ₛ ]ₛ [ ⟨ a ⟩ ]) (∘p-,ₜ _ _ _) ⟩
    γ ∘ₜ δ ,ₜ z [ p ] [ T→SS δ ⁺ₛ ]ₛ [ ⟨ a ⟩ ]            ≡⟨ cong (λ x → γ ∘ₜ δ ,ₜ x [ ⟨ a ⟩ ]) (p-⁺ₛ _ (T→SS δ)) ⟩
    γ ∘ₜ δ ,ₜ z [ T→SS δ ]ₛ [ p ] [ ⟨ a ⟩ ]               ≡⟨ cong (λ x → γ ∘ₜ δ ,ₜ x) (p-⟨⟩ _ _) ⟩
    γ ∘ₜ δ ,ₜ z [ T→SS δ ]ₛ                               ∎

  idₜ : Tms Γ Γ
  idₜ {Γ = ◆} = εₜ
  idₜ {Γ = Γ ▹ A} = idₜ ∘pₜ ,ₜ q

  []-idₜ : (a : Tm Γ A) → a [ idₜ ]ₜ ≡ a
  []-idₜ {Γ = ◆} a = refl
  []-idₜ {Γ = Γ ▹ Z} a = begin
    a [ T→SS (idₜ ∘pₜ) ⁺ₛ ]ₛ [ ⟨ q ⟩ ]   ≡⟨ cong (λ x → x [ ⟨ q ⟩ ]) ([]-⁺ₛ a (T→SS (idₜ ∘pₜ)) (T→SS idₜ ∘ₛ ⌜ p ⌝) λ a → []-∘pₜ _ idₜ) ⟩
    a [ T→SS idₜ ⁺ₛ ]ₛ [ p ⁺ ] [ ⟨ q ⟩ ] ≡⟨ cong (λ x → x [ p ⁺ ] [ ⟨ q ⟩ ]) ([]-⁺ₛ _ (T→SS idₜ) idₛ λ a → []-idₜ _) ⟩
    a [ p ⁺ ] [ ⟨ q ⟩ ]                  ≡⟨ ▹-η _ ⟩
    a                                    ∎

  idrₜ : (γ : Tms Δ Γ) → γ ∘ₜ idₜ ≡ γ
  idrₜ εₜ = refl
  idrₜ (γ ,ₜ a) = begin
    γ ∘ₜ idₜ ,ₜ a [ idₜ ]ₜ ≡⟨ cong (λ x → x ,ₜ a [ idₜ ]ₜ) (idrₜ _) ⟩
    γ ,ₜ a [ idₜ ]ₜ        ≡⟨ cong (λ x → γ ,ₜ x) ([]-idₜ _) ⟩
    γ ,ₜ a                 ∎

  idlₜ : (γ : Tms Δ Γ) → idₜ ∘ₜ γ ≡ γ
  idlₜ εₜ = refl
  idlₜ (γ ,ₜ a) = begin
    idₜ ∘pₜ ∘ₜ (γ ,ₜ a) ,ₜ q [ T→SS γ ⁺ₛ ]ₛ [ ⟨ a ⟩ ] ≡⟨ cong (λ x → x ,ₜ q [ T→SS γ ⁺ₛ ]ₛ [ ⟨ a ⟩ ]) (∘p-,ₜ _ _ _) ⟩
    idₜ ∘ₜ γ ,ₜ q [ T→SS γ ⁺ₛ ]ₛ [ ⟨ a ⟩ ]            ≡⟨ cong (λ x → x ,ₜ q [ T→SS γ ⁺ₛ ]ₛ [ ⟨ a ⟩ ]) (idlₜ _) ⟩
    γ ,ₜ q [ T→SS γ ⁺ₛ ]ₛ [ ⟨ a ⟩ ]                   ≡⟨ cong (λ x → γ ,ₜ x [ ⟨ a ⟩ ]) (q-⁺ₛ (T→SS γ)) ⟩
    γ ,ₜ q [ ⟨ a ⟩ ]                                  ≡⟨ cong (λ x → γ ,ₜ x) (q-⟨⟩ _) ⟩
    γ ,ₜ a                                            ∎

module _ (M : SSC) where
  open SSC M
  open SSC→CwF M

  SSC→CwF : CwF
  SSC→CwF .CwF.Ty = Ty
  SSC→CwF .CwF.Sub = Tms

  SSC→CwF .CwF._∘_ = _∘ₜ_
  SSC→CwF .CwF.assoc = assocₜ

  SSC→CwF .CwF.id = idₜ
  SSC→CwF .CwF.idr = idrₜ
  SSC→CwF .CwF.idl = idlₜ

  SSC→CwF .CwF.Tm = Tm
  SSC→CwF .CwF._[_] = _[_]ₜ
  SSC→CwF .CwF.[]-∘ = []-∘ₜ
  SSC→CwF .CwF.[]-id = []-idₜ

  SSC→CwF .CwF.ε = εₜ
  SSC→CwF .CwF.ε-∘ γ = refl
  SSC→CwF .CwF.◆-η = refl

  SSC→CwF .CwF.p = idₜ ∘pₜ
  SSC→CwF .CwF.q = q

  SSC→CwF .CwF._,_ = _,ₜ_
  SSC→CwF .CwF.,-∘ γ a δ = refl

  SSC→CwF .CwF.▹-β₁ γ a = begin
    idₜ ∘pₜ ∘ₜ (γ ,ₜ a) ≡⟨ ∘p-,ₜ _ _ _ ⟩
    idₜ ∘ₜ γ            ≡⟨ idlₜ _ ⟩
    γ                   ∎
  SSC→CwF .CwF.▹-β₂ γ a = begin
    q [ T→SS γ ⁺ₛ ]ₛ [ ⟨ a ⟩ ] ≡⟨ cong (λ x → x [ ⟨ a ⟩ ]) (q-⁺ₛ (T→SS γ)) ⟩
    q [ ⟨ a ⟩ ]                ≡⟨ q-⟨⟩ _ ⟩
    a                          ∎
  SSC→CwF .CwF.▹-η = refl

  SSC→CwF .CwF.ι = ι
  SSC→CwF .CwF._⇒_ = _⇒_

  SSC→CwF .CwF.app = app
  SSC→CwF .CwF.app-[] f a γ = app-[]ₛ _ _ (T→SS γ)

  SSC→CwF .CwF.lam = lam
  SSC→CwF .CwF.lam-[] b γ = begin
    lam b [ T→SS γ ]ₛ                                         ≡⟨ lam-[]ₛ _ (T→SS γ) ⟩
    lam (b [ T→SS γ ⁺ₛ ]ₛ)                                    ≡˘⟨ cong (λ x → lam x) ([]-⁺ₛ _ (T→SS idₜ) idₛ λ b → []-idₜ _) ⟩
    lam (b [ T→SS γ ⁺ₛ ]ₛ [ T→SS idₜ ⁺ₛ ]ₛ)                   ≡˘⟨ cong (λ x → lam x) (▹-η _) ⟩
    lam (b [ T→SS γ ⁺ₛ ]ₛ [ T→SS idₜ ⁺ₛ ]ₛ [ p ⁺ ] [ ⟨ q ⟩ ]) ≡˘⟨ cong (λ x → lam (x [ ⟨ q ⟩ ])) ([]-⁺ₛ (b [ T→SS γ ⁺ₛ ]ₛ) (T→SS (idₜ ∘pₜ)) (T→SS idₜ ∘ₛ ⌜ p ⌝) λ b → []-∘pₜ _ idₜ) ⟩
    lam (b [ T→SS γ ⁺ₛ ]ₛ [ T→SS (idₜ ∘pₜ) ⁺ₛ ]ₛ [ ⟨ q ⟩ ])   ≡˘⟨ cong (λ x → lam (x [ ⟨ q ⟩ ])) ([]-⁺ₛ _ (T→SS (γ ∘ₜ (idₜ ∘pₜ))) (T→SS γ ∘ₛ T→SS (idₜ ∘pₜ)) λ b → []-∘ₜ _ γ (idₜ ∘pₜ)) ⟩
    lam (b [ T→SS (γ ∘ₜ (idₜ ∘pₜ)) ⁺ₛ ]ₛ [ ⟨ q ⟩ ])           ∎

  SSC→CwF .CwF.⇒-β b a = begin
    app (lam b) a                ≡⟨ ⇒-β _ _ ⟩
    b [ ⟨ a ⟩ ]                  ≡˘⟨ cong (λ x → x [ ⟨ a ⟩ ]) ([]-⁺ₛ _ (T→SS idₜ) idₛ λ b → []-idₜ _) ⟩
    b [ T→SS idₜ ⁺ₛ ]ₛ [ ⟨ a ⟩ ] ∎
  SSC→CwF .CwF.⇒-η f = begin
    lam (app (f [ T→SS (idₜ ∘pₜ) ]ₛ) q) ≡⟨ cong (λ x → lam (app x q)) ([]-∘pₜ _ idₜ) ⟩
    lam (app (f [ T→SS idₜ ]ₛ [ p ]) q) ≡⟨ cong (λ x → lam (app (x [ p ]) q)) ([]-idₜ _) ⟩
    lam (app (f [ p ]) q)               ≡⟨ ⇒-η _ ⟩
    f                                   ∎

module SSC→CwF→SSC (M : SSC) where
  open SSC M
  open SSC→CwF M
  open CwF→SSC (SSC→CwF M) hiding (SSub)
  module SCS = SSC (CwF→SSC (SSC→CwF M))

  private variable
    Γ Δ : Con
    A B : Ty

  SCS-Ty : SCS.Ty ≡ Ty
  SCS-Ty = refl

  SCS-Tm : (Γ : Con) (A : Ty) → SCS.Tm Γ A ≡ Tm Γ A
  SCS-Tm Γ A = refl

  SCS-[] : (a : Tm Γ A) (γ : SSub Δ Γ) → a SCS.[ γ ] ≡ a [ γ ]
  SCS-[] a pₛ = begin
    a [ idₜ ∘pₜ ]ₜ   ≡⟨ []-∘pₜ _ idₜ ⟩
    a [ idₜ ]ₜ [ p ] ≡⟨ cong (λ x → x [ p ]) ([]-idₜ _) ⟩
    a [ p ]          ∎
  SCS-[] a (γ ⁺) = begin
    a [ T→SS (SS→S γ ∘ₜ (idₜ ∘pₜ)) ⁺ₛ ]ₛ [ ⟨ q ⟩ ]           ≡⟨ cong (λ x → x [ ⟨ q ⟩ ]) ([]-⁺ₛ _ (T→SS (SS→S γ ∘ₜ (idₜ ∘pₜ))) (T→SS (SS→S γ) ∘ₛ (T→SS (idₜ ∘pₜ))) λ a → []-∘ₜ _ (SS→S γ) (idₜ ∘pₜ)) ⟩
    a [ T→SS (SS→S γ) ⁺ₛ ]ₛ [ T→SS (idₜ ∘pₜ) ⁺ₛ ]ₛ [ ⟨ q ⟩ ] ≡⟨ cong (λ x → x [ T→SS (idₜ ∘pₜ) ⁺ₛ ]ₛ [ ⟨ q ⟩ ]) ([]-⁺ₛ _ (T→SS (SS→S γ)) ⌜ γ ⌝ λ a → SCS-[] _ _) ⟩
    a [ γ ⁺ ] [ T→SS (idₜ ∘pₜ) ⁺ₛ ]ₛ [ ⟨ q ⟩ ]               ≡⟨ cong (λ x → x [ ⟨ q ⟩ ]) ([]-⁺ₛ _ (T→SS (idₜ ∘pₜ)) (T→SS idₜ ∘ₛ ⌜ p ⌝) λ a → []-∘pₜ _ idₜ) ⟩
    a [ γ ⁺ ] [ T→SS idₜ ⁺ₛ ]ₛ [ p ⁺ ] [ ⟨ q ⟩ ]             ≡⟨ cong (λ x → x [ p ⁺ ] [ ⟨ q ⟩ ]) ([]-⁺ₛ _ (T→SS idₜ) idₛ λ a → []-idₜ _) ⟩
    a [ γ ⁺ ] [ p ⁺ ] [ ⟨ q ⟩ ]                              ≡⟨ ▹-η _ ⟩
    a [ γ ⁺ ]                                                ∎
  SCS-[] a ⟨ z ⟩ =
    cong (λ x → x [ ⟨ z ⟩ ]) ([]-⁺ₛ _ (T→SS idₜ) idₛ λ a → []-idₜ _)

  SCS-q : (Tm (Γ ▹ A) A ∋ SCS.q) ≡ q
  SCS-q = refl

  SCS-ι : SCS.ι ≡ ι
  SCS-ι = refl

  SCS-⇒ : (A B : Ty) → (A SCS.⇒ B) ≡ (A ⇒ B)
  SCS-⇒ A B = refl

  SCS-app : (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) → SCS.app f a ≡ app f a
  SCS-app f a = refl

  SCS-lam : (b : Tm (Γ ▹ A) B) → SCS.lam b ≡ lam b
  SCS-lam b = refl

module CwF→SSC→CwF (M : CwF) where
  open CwF M
  open CwF→SSC M
  open SSC→CwF (CwF→SSC M)
  module CSC = CwF (SSC→CwF (CwF→SSC M))

  private variable
    Γ Δ Θ : Con
    A B : Ty

  CSC-Ty : CSC.Ty ≡ Ty
  CSC-Ty = refl

  CSC-Tm : (Γ : Con) (A : Ty) → CSC.Tm Γ A ≡ Tm Γ A
  CSC-Tm Γ A = refl

  T→S : Tms Δ Γ → Sub Δ Γ
  T→S εₜ = ε
  T→S (γ ,ₜ a) = T→S γ , a

  S→T : Sub Δ Γ → Tms Δ Γ
  S→T {Γ = ◆} γ = εₜ
  S→T {Γ = Γ ▹ A} γ = S→T (p ∘ γ) ,ₜ q [ γ ]

  S→T→S : (γ : Sub Δ Γ) → T→S (S→T γ) ≡ γ
  S→T→S {Γ = ◆} γ = begin
    ε      ≡˘⟨ ε-∘ _ ⟩
    ε ∘ γ  ≡⟨ cong (λ x → x ∘ γ) ◆-η ⟩
    id ∘ γ ≡⟨ idl _ ⟩
    γ      ∎
  S→T→S {Γ = Γ ▹ A} γ = begin
    T→S (S→T (p ∘ γ)) , q [ γ ] ≡⟨ cong (λ x → x , q [ γ ]) (S→T→S _) ⟩
    p ∘ γ , q [ γ ]             ≡˘⟨ ,-∘ _ _ _ ⟩
    (p , q) ∘ γ                 ≡⟨ cong (λ x → x ∘ γ) ▹-η ⟩
    id ∘ γ                      ≡⟨ idl _ ⟩
    γ                           ∎

  T→S→T : (γ : Tms Δ Γ) → S→T (T→S γ) ≡ γ
  T→S→T εₜ = refl
  T→S→T (γ ,ₜ a) = begin
    S→T (p ∘ (T→S γ , a)) ,ₜ q [ T→S γ , a ] ≡⟨ cong (λ x → S→T x ,ₜ q [ T→S γ , a ]) (▹-β₁ _ _) ⟩
    S→T (T→S γ) ,ₜ q [ T→S γ , a ]           ≡⟨ cong (λ x → x ,ₜ q [ T→S γ , a ]) (T→S→T _) ⟩
    γ ,ₜ q [ T→S γ , a ]                     ≡⟨ cong (λ x → γ ,ₜ x) (▹-β₂ _ _) ⟩
    γ ,ₜ a                                   ∎

  CSC-Sub : (Δ Γ : Con) → CSC.Sub Δ Γ ↔ Sub Δ Γ
  CSC-Sub Δ Γ = mk↔′ T→S S→T S→T→S T→S→T

  []-εₛ : (a : Tm ◆ A) → (Tm Γ A ∋ a [ εₛ ]ₛ) ≡ a [ ε ]
  []-εₛ {Γ = ◆} a = begin
    a        ≡˘⟨ []-id _ ⟩
    a [ id ] ≡˘⟨ cong (λ x → a [ x ]) ◆-η ⟩
    a [ ε ]  ∎
  []-εₛ {Γ = Γ ▹ Z} a = begin
    a [ εₛ ]ₛ [ p ] ≡⟨ cong (λ x → x [ p ]) ([]-εₛ _) ⟩
    a [ ε ] [ p ]   ≡˘⟨ []-∘ _ _ _ ⟩
    a [ ε ∘ p ]     ≡⟨ cong (λ x → a [ x ]) (ε-∘ _) ⟩
    a [ ε ]         ∎

  CSC-[] : (a : Tm Γ A) (γ : Tms Δ Γ) → a CSC.[ γ ] ≡ a [ T→S γ ]
  CSC-[] a εₜ = []-εₛ _
  CSC-[] a (γ ,ₜ z) = begin
    a [ T→SS γ ⁺ₛ ]ₛ [ id , z ]                           ≡⟨ cong (λ x → x [ id , z ]) ([]-⁺ₛ→lam _ (T→SS γ)) ⟩
    app (lam a [ T→SS γ ]ₛ [ p ]) q [ id , z ]            ≡⟨ cong (λ x → app (x [ p ]) q [ id , z ]) (CSC-[] _ γ) ⟩
    app (lam a [ T→S γ ] [ p ]) q [ id , z ]              ≡⟨ app-[] _ _ _ ⟩
    app (lam a [ T→S γ ] [ p ] [ id , z ]) (q [ id , z ]) ≡˘⟨ cong (λ x → app x (q [ id , z ])) ([]-∘ _ _ _) ⟩
    app (lam a [ T→S γ ] [ p ∘ (id , z) ]) (q [ id , z ]) ≡⟨ cong (λ x → app (lam a [ T→S γ ] [ x ]) (q [ id , z ])) (▹-β₁ _ _) ⟩
    app (lam a [ T→S γ ] [ id ]) (q [ id , z ])           ≡⟨ cong (λ x → app x (q [ id , z ])) ([]-id _) ⟩
    app (lam a [ T→S γ ]) (q [ id , z ])                  ≡⟨ cong (λ x → app (lam a [ T→S γ ]) x) (▹-β₂ _ _) ⟩
    app (lam a [ T→S γ ]) z                               ≡⟨ cong (λ x → app x z) (lam-[] _ _) ⟩
    app (lam (a [ T→S γ ∘ p , q ])) z                     ≡⟨ ⇒-β _ _ ⟩
    a [ T→S γ ∘ p , q ] [ id , z ]                        ≡˘⟨ []-∘ _ _ _ ⟩
    a [ (T→S γ ∘ p , q) ∘ (id , z) ]                      ≡⟨ cong (λ x → a [ x ]) (,-∘ _ _ _) ⟩
    a [ T→S γ ∘ p ∘ (id , z) , q [ id , z ] ]             ≡˘⟨ cong (λ x → a [ x , q [ id , z ] ]) (assoc _ _ _) ⟩
    a [ T→S γ ∘ (p ∘ (id , z)) , q [ id , z ] ]           ≡⟨ cong (λ x → a [ T→S γ ∘ x , q [ id , z ] ]) (▹-β₁ _ _) ⟩
    a [ T→S γ ∘ id , q [ id , z ] ]                       ≡⟨ cong (λ x → a [ x , q [ id , z ] ]) (idr _) ⟩
    a [ T→S γ , q [ id , z ] ]                            ≡⟨ cong (λ x → a [ T→S γ , x ]) (▹-β₂ _ _) ⟩
    a [ T→S γ , z ]                                       ∎

  CSC-∘ : (γ : Tms Δ Γ) (δ : Tms Θ Δ) → T→S (γ CSC.∘ δ) ≡ T→S γ ∘ T→S δ
  CSC-∘ εₜ δ = sym (ε-∘ _)
  CSC-∘ (γ ,ₜ a) δ = begin
    T→S (γ ∘ₜ δ) , a [ δ ]ₜ     ≡⟨ cong (λ x → x , a [ δ ]ₜ) (CSC-∘ γ δ) ⟩
    T→S γ ∘ T→S δ , a [ δ ]ₜ    ≡⟨ cong (λ x → T→S γ ∘ T→S δ , x) (CSC-[] _ δ) ⟩
    T→S γ ∘ T→S δ , a [ T→S δ ] ≡˘⟨ ,-∘ _ _ _ ⟩
    (T→S γ , a) ∘ T→S δ         ∎

  CSC-∘p : (γ : Tms Δ Γ) → (Sub (Δ ▹ A) Γ ∋ T→S (γ ∘pₜ)) ≡ (T→S γ ∘ p)
  CSC-∘p εₜ = sym (ε-∘ _)
  CSC-∘p (γ ,ₜ z) = begin
    T→S (γ ∘pₜ) , z [ p ] ≡⟨ cong (λ x → x , z [ p ]) (CSC-∘p γ) ⟩
    T→S γ ∘ p , z [ p ]   ≡˘⟨ ,-∘ _ _ _ ⟩
    (T→S γ , z) ∘ p       ∎

  CSC-id : (Sub Γ Γ ∋ T→S CSC.id) ≡ id
  CSC-id {Γ = ◆} = ◆-η
  CSC-id {Γ = Γ ▹ A} = begin
    T→S (idₜ ∘pₜ) , q ≡⟨ cong (λ x → x , q) (CSC-∘p idₜ) ⟩
    T→S idₜ ∘ p , q   ≡⟨ cong (λ x → x ∘ p , q) CSC-id ⟩
    id ∘ p , q        ≡⟨ cong (λ x → x , q) (idl _) ⟩
    p , q             ≡⟨ ▹-η ⟩
    id                ∎

  CSC-ε : (Sub Γ ◆ ∋ T→S CSC.ε) ≡ ε
  CSC-ε = refl

  CSC-p : (Sub (Γ ▹ A) Γ ∋ T→S CSC.p) ≡ p
  CSC-p = begin
    T→S (idₜ ∘pₜ) ≡⟨ CSC-∘p idₜ ⟩
    T→S idₜ ∘ p   ≡⟨ cong (λ x → x ∘ p) CSC-id ⟩
    id ∘ p        ≡⟨ idl _ ⟩
    p             ∎

  CSC-q : (Tm (Γ ▹ A) A ∋ CSC.q) ≡ q
  CSC-q = refl

  CSC-, : (γ : Tms Δ Γ) (a : Tm Δ A) → T→S (γ CSC., a) ≡ (T→S γ , a)
  CSC-, γ a = refl

  CSC-ι : CSC.ι ≡ ι
  CSC-ι = refl

  CSC-⇒ : (A B : Ty) → (A CSC.⇒ B) ≡ (A ⇒ B)
  CSC-⇒ A B = refl

  CSC-app : (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) → CSC.app f a ≡ app f a
  CSC-app f a = refl

  CSC-lam : (b : Tm (Γ ▹ A) B) → CSC.lam b ≡ lam b
  CSC-lam b = refl
