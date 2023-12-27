{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.HLevels

-- the set-truncated syntax with forward declarations (as opposed to the Szumi method)

module TT.SetForward where

data Con : Type
data Sub : Con → Con → Type
data Ty  : Con → Type
data Tm  : (Γ : Con) → Ty Γ → Type

data Con where
  ConSet      : isSet Con
  ◆           : Con
  _▹_         : (Γ : Con) → Ty Γ → Con

_[_]T'        : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
π₁'           : ∀{Γ Δ A}(σ : Sub Γ (Δ ▹ A)) → Sub Γ Δ
π₂'           : ∀{Γ Δ A}(σ : Sub Γ (Δ ▹ A)) → Tm Γ (A [ π₁' σ ]T')
_∘'_          : ∀{Γ Θ Δ} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
id'           : ∀{Γ} → Sub Γ Γ
_[_∣_]T''     : ∀{Γ Θ Δ}(A : Ty Δ)(σ : Sub Θ Δ)(δ : Sub Γ Θ) → A [ σ ∘' δ ]T' ≡ A [ σ ]T' [ δ ]T'
_[id]T'       : ∀{Γ}(A : Ty Γ) → A [ id' ]T' ≡ A

data Sub where
  SubSet      : ∀{Γ Δ} → isSet (Sub Γ Δ)
  _∘_         : ∀{Γ Θ Δ} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
  ass         : ∀{Γ Θ Ξ Δ}(σ : Sub Ξ Δ)(δ : Sub Θ Ξ)(ν : Sub Γ Θ) →
                (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  id          : ∀{Γ} → Sub Γ Γ
  idl         : ∀{Γ Δ}{σ : Sub Γ Δ} → id ∘ σ ≡ σ
  idr         : ∀{Γ Δ}{σ : Sub Γ Δ} → σ ∘ id ≡ σ
  ε           : ∀{Γ} → Sub Γ ◆
  ◆η          : ∀{Γ}(σ : Sub Γ ◆) → σ ≡ ε
  _,s_        : ∀{Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T') → Sub Γ (Δ ▹ A)
  π₁          : ∀{Γ Δ A}(σ : Sub Γ (Δ ▹ A)) → Sub Γ Δ
  ▹β₁         : ∀{Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T')} → π₁ (σ ,s t) ≡ σ
  ▹η          : ∀{Γ Δ A}{σ : Sub Γ (Δ ▹ A)} → σ ≡ π₁' σ ,s π₂' σ
  π₁∘         : ∀{Γ Δ A}{σ : Sub Γ (Δ ▹ A)}{Θ}{δ : Sub Θ Γ} → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
  _^_         : ∀{Γ Δ}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▹ A [ σ ]T') (Δ ▹ A)
  id^_        : ∀{Γ}(A : Ty Γ) → PathP (λ i → Sub (Γ ▹ (A [id]T') i) (Γ ▹ A)) (id' ^ A) id
  ∘^          : ∀{Δ}{A : Ty Δ}{Θ}(σ : Sub Θ Δ){Γ}(δ : Sub Γ Θ) → PathP (λ i → Sub (Γ ▹ (A [ σ ∣ δ ]T'') i) (Δ ▹ A)) ((σ ∘' δ) ^ A) (σ ^ A ∘ δ ^ A [ σ ]T')
  ^=₁         : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ} → π₁ (σ ^ A) ≡ σ ∘ π₁ id

_∘'_ = _∘_
id' = id
π₁' = π₁
U'            : ∀{Γ} → Ty Γ
_[_]U'        : ∀{Γ} → Tm Γ U' → ∀{Θ} → Sub Θ Γ → Tm Θ U'

data Ty where
  TySet       : ∀{Γ} → isSet (Ty Γ)
  _[_]T       : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
  _[_∣_]T     : ∀{Γ Θ Δ}(A : Ty Δ)(σ : Sub Θ Δ)(δ : Sub Γ Θ) → A [ σ ∘ δ ]T' ≡ A [ σ ]T' [ δ ]T'
  _[id]T      : ∀{Γ}(A : Ty Γ) → A [ id ]T' ≡ A
  _[π₁_∣_]T   : ∀{Γ Δ} A (σ : Sub Γ (Δ ▹ A)){Θ}(δ : Sub Θ Γ) → A [ π₁ σ ]T [ δ ]T ≡ A [ π₁ (σ ∘ δ) ]T
  _[id^]T     : ∀{Γ}{A : Ty Γ} B → PathP (λ i → Ty (Γ ▹ (A [id]T) i)) (B [ id ^ A ]T) B
  _[∘^]       : ∀{Δ}{A : Ty Δ}{Θ}{σ : Sub Θ Δ}{Γ}{δ : Sub Γ Θ} B → PathP (λ i → Ty (Γ ▹ (A [ σ ∣ δ ]T) i)) (B [ (σ ∘ δ) ^ A ]T) ( B [ σ ^ A ]T [ δ ^ A [ σ ]T' ]T )
  _[π₁^]      : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ} B → B [ π₁ (σ ^ A) ]T ≡ B [ σ ]T [ π₁ id ]T
  Π           : ∀{Γ}(A : Ty Γ)(B : Ty (Γ ▹ A)) → Ty Γ
  Π[]         : ∀{Γ} A B {Θ}(σ : Sub Θ Γ) → Π A B [ σ ]T ≡ Π (A [ σ ]T') (B [ σ ^ A ]T)
  U           : ∀{Γ} → Ty Γ
  U[_]        : ∀{Γ Θ}(σ : Sub Θ Γ) → U [ σ ]T ≡ U
  El          : ∀{Γ} → Tm Γ U' → Ty Γ
  El_[_]      : ∀{Γ}(a : Tm Γ U'){Θ}(σ : Sub Θ Γ) → El a [ σ ]T ≡ El (a [ σ ]U')

_[_]T' = _[_]T
_[_∣_]T'' = _[_∣_]T
_[id]T' = _[id]T
U' = U

data Tm where
  TmSet       : ∀{Γ A} → isSet (Tm Γ A)
  _[_]t       : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  _[_∣_]t     : ∀{Γ Θ Δ}{A : Ty Δ}(t : Tm Δ A)(σ : Sub Θ Δ)(δ : Sub Γ Θ) →
                PathP (λ i → Tm Γ ((A [ σ ∣ δ ]T) i)) (t [ σ ∘ δ ]t) (t [ σ ]t [ δ ]t)
  _[id]t      : ∀{Γ A}(t : Tm Γ A) →
                PathP (λ i → Tm Γ ((A [id]T) i)) (t [ id ]t) t
  π₂          : ∀{Γ Δ A}(σ : Sub Γ (Δ ▹ A)) → Tm Γ (A [ π₁ σ ]T)
  ▹β₂         : ∀{Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → PathP (λ i → Tm Γ (A [ ▹β₁ {σ = σ}{t} i ]T)) (π₂ (σ ,s t)) t
  π₂[]        : ∀{Γ Δ A}{σ : Sub Γ (Δ ▹ A)}{Θ}{δ : Sub Θ Γ} → PathP (λ i → Tm Θ ((A [π₁ σ ∣ δ ]T) i)) (π₂ σ [ δ ]t) (π₂ (σ ∘ δ))
  ^=₂         : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ} → PathP (λ i → Tm (Γ ▹ A [ σ ]T) ((A [π₁^]) i)) (π₂ (σ ^ A)) (π₂ id)
  lam         : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (Π A B)
  app         : ∀{Γ A B} → Tm Γ (Π A B) → Tm (Γ ▹ A) B
  Πβ          : ∀{Γ A B}{t : Tm (Γ ▹ A) B} → app (lam t) ≡ t
  Πη          : ∀{Γ A B}{t : Tm Γ (Π A B)} → lam (app t) ≡ t
  lam[]       : ∀{Γ A B}(t : Tm (Γ ▹ A) B){Θ}(σ : Sub Θ Γ) → PathP (λ i → Tm Θ (Π[] A B σ i)) (lam t [ σ ]t) (lam (t [ σ ^ A ]t))
  _[_]U       : ∀{Γ} → Tm Γ U → ∀{Θ} → Sub Θ Γ → Tm Θ U
  _[_]U=      : ∀{Γ}(a : Tm Γ U){Θ}(σ : Sub Θ Γ) → PathP (λ i → Tm Θ (U[ σ ] (~ i))) (a [ σ ]U) (a [ σ ]t)
  _[id]U      : ∀{Γ}(a : Tm Γ U) → a [ id ]U ≡ a
  _[_∣_]U     : ∀{Γ}(a : Tm Γ U){Θ}(σ : Sub Θ Γ){Ω}(δ : Sub Ω Θ) → a [ σ ∘ δ ]U ≡ a [ σ ]U [ δ ]U

π₂' = π₂
_[_]U' = _[_]U

infixl 5 _▹_
infixl 40 _[_]T _[_]T'
infixl 40 _[_∣_]T _[_∣_]T''
infixl 40 _[id]T _[id]T'
infixl 5 _,s_
infixr 8 _∘_ _∘'_
infixl 40 _[_]t
infixl 40 _[_∣_]t
infixl 40 _[π₁_∣_]T
