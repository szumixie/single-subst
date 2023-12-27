{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.HLevels

module TT.Set.Model where

record Model {ℓ}{ℓ'} : Type₁ (lsuc (ℓ ⊔ ℓ')) where
  field
    UU          : Type ℓ
    EL          : UU → Type ℓ'
    Con'        : UU
    Sub'        : EL Con' → EL Con' → UU
    Ty'         : EL Con' → UU
    Tm'         : (Γ : EL Con') → EL (Ty' Γ) → UU
    ConSet      : isSet (EL Con')
    SubSet      : ∀{Γ Δ} → isSet (EL (Sub' Γ Δ))
    _∘_         : ∀{Γ Θ Δ} → EL (Sub' Θ Δ) → EL (Sub' Γ Θ) → EL (Sub' Γ Δ)
    ass         : ∀{Γ Θ Ξ Δ}(σ : EL (Sub' Ξ Δ))(δ : EL (Sub' Θ Ξ))(ν : EL (Sub' Γ Θ)) →
                  (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
    id          : ∀{Γ} → EL (Sub' Γ Γ)
    idl         : ∀{Γ Δ}{σ : EL (Sub' Γ Δ)} → id ∘ σ ≡ σ
    idr         : ∀{Γ Δ}{σ : EL (Sub' Γ Δ)} → σ ∘ id ≡ σ

    ◆           : EL Con'
    ε           : ∀{Γ} → EL (Sub' Γ ◆)
    ◆η          : ∀{Γ}(σ : EL (Sub' Γ ◆)) → σ ≡ ε

    TySet       : ∀{Γ} → isSet (EL (Ty' Γ))
    _[_]T       : ∀{Γ Δ} → EL (Ty' Δ) → EL (Sub' Γ Δ) → EL (Ty' Γ)
    _[_∣_]T     : ∀{Γ Θ Δ}(A : EL (Ty' Δ))(σ : EL (Sub' Θ Δ))(δ : EL (Sub' Γ Θ)) → A [ σ ∘ δ ]T ≡ A [ σ ]T [ δ ]T
    _[id]T      : ∀{Γ}(A : EL (Ty' Γ)) → A [ id ]T ≡ A
                  
    TmSet       : ∀{Γ A} → isSet (EL (Tm' Γ A))
    _[_]t       : ∀{Γ Δ}{A : EL (Ty' Δ)} → EL (Tm' Δ A) → (σ : EL (Sub' Γ Δ)) → EL (Tm' Γ (A [ σ ]T))
    _[_∣_]t     : ∀{Γ Θ Δ}{A : EL (Ty' Δ)}(t : EL (Tm' Δ A))(σ : EL (Sub' Θ Δ))(δ : EL (Sub' Γ Θ)) →
                  PathP (λ i → EL (Tm' Γ ((A [ σ ∣ δ ]T) i))) (t [ σ ∘ δ ]t) (t [ σ ]t [ δ ]t)
    _[id]t      : ∀{Γ A}(t : EL (Tm' Γ A)) →
                  PathP (λ i → EL (Tm' Γ ((A [id]T) i))) (t [ id ]t) t

    _▹_         : (Γ : EL Con') → EL (Ty' Γ) → EL Con'
    _,s_        : ∀{Γ Δ A}(σ : EL (Sub' Γ Δ)) → EL (Tm' Γ (A [ σ ]T)) → EL (Sub' Γ (Δ ▹ A))
    π₁          : ∀{Γ Δ A}(σ : EL (Sub' Γ (Δ ▹ A))) → EL (Sub' Γ Δ)
    π₂          : ∀{Γ Δ A}(σ : EL (Sub' Γ (Δ ▹ A))) → EL (Tm' Γ (A [ π₁ σ ]T))
    ▹β₁         : ∀{Γ Δ A}{σ : EL (Sub' Γ Δ)}{t : EL (Tm' Γ (A [ σ ]T))} → π₁ (σ ,s t) ≡ σ
    ▹β₂         : ∀{Γ Δ A}{σ : EL (Sub' Γ Δ)}{t : EL (Tm' Γ (A [ σ ]T))} → PathP (λ i → EL (Tm' Γ (A [ ▹β₁ {σ = σ}{t} i ]T))) (π₂ (σ ,s t)) t
    ▹η          : ∀{Γ Δ A}{σ : EL (Sub' Γ (Δ ▹ A))} → σ ≡ π₁ σ ,s π₂ σ
    π₁∘         : ∀{Γ Δ A}{σ : EL (Sub' Γ (Δ ▹ A))}{Θ}{δ : EL (Sub' Θ Γ)} → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
    _[π₁_∣_]T   : ∀{Γ Δ} A (σ : EL (Sub' Γ (Δ ▹ A))){Θ}(δ : EL (Sub' Θ Γ)) → A [ π₁ σ ]T [ δ ]T ≡ A [ π₁ (σ ∘ δ) ]T                        -- <- we want to refer to this later so we introduce it
    π₂[]        : ∀{Γ Δ A}{σ : EL (Sub' Γ (Δ ▹ A))}{Θ}{δ : EL (Sub' Θ Γ)} → PathP (λ i → EL (Tm' Θ ((A [π₁ σ ∣ δ ]T) i))) (π₂ σ [ δ ]t) (π₂ (σ ∘ δ))
    _^_         : ∀{Γ Δ}(σ : EL (Sub' Γ Δ))(A : EL (Ty' Δ)) → EL (Sub' (Γ ▹ A [ σ ]T) (Δ ▹ A))
    id^_        : ∀{Γ}(A : EL (Ty' Γ)) → PathP (λ i → EL (Sub' (Γ ▹ (A [id]T) i) (Γ ▹ A))) (id ^ A) id
    ∘^          : ∀{Δ}{A : EL (Ty' Δ)}{Θ}(σ : EL (Sub' Θ Δ)){Γ}(δ : EL (Sub' Γ Θ)) → PathP (λ i → EL (Sub' (Γ ▹ (A [ σ ∣ δ ]T) i) (Δ ▹ A))) ((σ ∘ δ) ^ A) (σ ^ A ∘ δ ^ A [ σ ]T)
    _[id^]T     : ∀{Γ}{A : EL (Ty' Γ)} B → PathP (λ i → EL (Ty' (Γ ▹ (A [id]T) i))) (B [ id ^ A ]T) B
    _[∘^]       : ∀{Δ}{A : EL (Ty' Δ)}{Θ}{σ : EL (Sub' Θ Δ)}{Γ}{δ : EL (Sub' Γ Θ)} B → PathP (λ i → EL (Ty' (Γ ▹ (A [ σ ∣ δ ]T) i))) (B [ (σ ∘ δ) ^ A ]T) ( B [ σ ^ A ]T [ δ ^ A [ σ ]T ]T )
    ^=₁         : ∀{Γ Δ}{σ : EL (Sub' Γ Δ)}{A : EL (Ty' Δ)} → π₁ (σ ^ A) ≡ σ ∘ π₁ id
    _[π₁^]      : ∀{Γ Δ}{σ : EL (Sub' Γ Δ)}{A : EL (Ty' Δ)} B → B [ π₁ (σ ^ A) ]T ≡ B [ σ ]T [ π₁ id ]T
    ^=₂         : ∀{Γ Δ}{σ : EL (Sub' Γ Δ)}{A : EL (Ty' Δ)} → PathP (λ i → EL (Tm' (Γ ▹ A [ σ ]T) ((A [π₁^]) i))) (π₂ (σ ^ A)) (π₂ id)

    Π           : ∀{Γ}(A : EL (Ty' Γ))(B : EL (Ty' (Γ ▹ A))) → EL (Ty' Γ)
    lam         : ∀{Γ A B} → EL (Tm' (Γ ▹ A) B) → EL (Tm' Γ (Π A B))
    app         : ∀{Γ A B} → EL (Tm' Γ (Π A B)) → EL (Tm' (Γ ▹ A) B)
    Πβ          : ∀{Γ A B}{t : EL (Tm' (Γ ▹ A) B)} → app (lam t) ≡ t
    Πη          : ∀{Γ A B}{t : EL (Tm' Γ (Π A B))} → lam (app t) ≡ t
    Π[]         : ∀{Γ} A B {Θ}(σ : EL (Sub' Θ Γ)) → Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)
    lam[]       : ∀{Γ A B}(t : EL (Tm' (Γ ▹ A) B)){Θ}(σ : EL (Sub' Θ Γ)) → PathP (λ i → EL (Tm' Θ (Π[] A B σ i))) (lam t [ σ ]t) (lam (t [ σ ^ A ]t))

    U           : ∀{Γ} → EL (Ty' Γ)
    U[_]        : ∀{Γ Θ}(σ : EL (Sub' Θ Γ)) → U [ σ ]T ≡ U
    _[_]U       : ∀{Γ} → EL (Tm' Γ U) → ∀{Θ} → EL (Sub' Θ Γ) → EL (Tm' Θ U)
    _[_]U=      : ∀{Γ}(a : EL (Tm' Γ U)){Θ}(σ : EL (Sub' Θ Γ)) → PathP (λ i → EL (Tm' Θ (U[ σ ] (~ i)))) (a [ σ ]U) (a [ σ ]t)
    _[id]U      : ∀{Γ}(a : EL (Tm' Γ U)) → a [ id ]U ≡ a                                                      -- no need to relate a [id]U and a [id]t because Tm is an hset
    _[_∣_]U     : ∀{Γ}(a : EL (Tm' Γ U)){Θ}(σ : EL (Sub' Θ Γ)){Ω}(δ : EL (Sub' Ω Θ)) → a [ σ ∘ δ ]U ≡ a [ σ ]U [ δ ]U
    El          : ∀{Γ} → EL (Tm' Γ U) → EL (Ty' Γ)
    El_[_]      : ∀{Γ}(a : EL (Tm' Γ U)){Θ}(σ : EL (Sub' Θ Γ)) → El a [ σ ]T ≡ El (a [ σ ]U)

  infixl 5 _▹_
  infixl 40 _[_]T
  infixl 40 _[_∣_]T
  infixl 40 _[id]T
  infixl 5 _,s_
  infixr 8 _∘_
  infixl 40 _[_]t
  infixl 40 _[_∣_]t
  infixl 40 _[π₁_∣_]T
