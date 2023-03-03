{-# OPTIONS --prop --rewriting #-}

module Syntax where

open import lib

-- syntax for the single substitution calculus as a postulated QIIT

infixl 6 _[_]T
infixl 6 _[_]t
infixl 5 _▹_
infixl 5 _$_

postulate
  Con     : Set
  Sub     : Con → Con → Set
  Ty      : (Γ : Con) → Set
  Tm      : (Γ : Con) → Ty Γ → Set

variable
  Γ Δ : Con
  σ ρ ν : Sub Δ Γ
  A B C : Ty Γ
  t u v : Tm Γ A

postulate
  _[_]T    : Ty Γ → Sub Δ Γ → Ty Δ                      -- instantiation
  
  -- contexts are normal forms
  ◇        : Con
  _▹_      : (Γ : Con) → Ty Γ → Con
  
  -- substitutions are normal forms (a Sub is either a single weakening p⁺⁺...⁺ or a single substitution ⟨t⟩⁺⁺...⁺)
  p        : Sub (Γ ▹ A) Γ                              -- weakening
  ⟨_⟩      : Tm Γ A → Sub Γ (Γ ▹ A)                     -- single substitution
  _⁺       : (σ : Sub Δ Γ) → Sub (Δ ▹ A [ σ ]T) (Γ ▹ A) -- lifting

  p⟨⟩T     : A [ p ]T [ ⟨ t ⟩ ]T ≡ A
  p⁺T      : A [ p {Γ}{B} ]T [ σ ⁺ ]T ≡ A [ σ ]T [ p ]T

  -- an intuition: q [ σ ]t computes the stack σ, and gives the top element of the stack
  -- _[ p ]t pops the last element from the stack
  -- _[ ⟨ t ⟩]t puts t on top of the stack
  -- _[ σ ⁺ ]t applies σ to the bottom of the stack while leaving the top unchanged

  _[_]t    : Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]T)

  ⁺⟨⟩T     : A [ ⟨ t ⟩ ]T [ σ ]T ≡ (A [ σ ⁺ ]T [ ⟨ t [ σ ]t ⟩ ]T) -- NEW
  
  p⟨⟩t     : (Tm Γ ~) p⟨⟩T (u [ p ]t [ ⟨ t ⟩ ]t)      u                       -- putting on top of the stack, then popping is the same as not doing anything
  p⁺t      : (Tm _ ~) p⁺T  (u [ p {Γ}{B} ]t [ σ ⁺ ]t) (u [ σ ]t [ p ]t)       -- doing σ⁺, then pop is the same as first pop, then σ

  q        : Tm (Γ ▹ A) (A [ p ]T)
  q[⟨⟩]    : (Tm Γ ~)              p⟨⟩T (q [ ⟨ t ⟩ ]t) t
  q[⁺]     : (Tm (Δ ▹ A [ σ ]T) ~) p⁺T  (q [ σ ⁺ ]t)   q

  p⁺⟨q⟩T   : A [ p ⁺ ]T [ ⟨ q ⟩ ]T ≡ A -- NEW

  Π        : (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
  Π[]      : Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ⁺ ]T)
  lam      : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  _$_      : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ ⟨ u ⟩ ]T)    
  $[]      : subst (Tm _) ⁺⟨⟩T ((t $ u) [ σ ]t) ≡ subst (Tm _) Π[] (t [ σ ]t) $ (u [ σ ]t)
  Πβ       : lam t $ u ≡ t [ ⟨ u ⟩ ]t
  Πη       : subst (Tm _) (cong (Π A) (p⁺⟨q⟩T ⁻¹)) t ≡ lam (subst (Tm _) Π[] (t [ p ]t) $ q)
  {-
  app      : Tm Γ (Π A B) → Tm (Γ ▹ A) B
  Πβ       : app (lam t) ≡ t
  Πη       : lam (app t) ≡ t
  -}
  lam[]    : (Tm _ ~) Π[] (lam t [ σ ]t) (lam (t [ σ ⁺ ]t))

  -- TODO: depmodel
  -- TODO: create the QIIRT syntax using this -- not that easy because we need α-normal (substitution-normal) types and terms in the new syntax

record DepModel {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _[_]T∙
  infixl 6 _[_]t∙
  infixl 5 _▹∙_
  infixl 5 _$∙_

  field
    Con∙       : Con → Set i
    Sub∙       : Con∙ Δ → Con∙ Γ → Sub Δ Γ → Set j
    Ty∙        : Con∙ Γ → Ty Γ → Set k
    Tm∙        : (Γ∙ : Con∙ Γ) → Ty∙ Γ∙ A → Tm Γ A → Set l
{-    
    ◇∙         : Con∙ ◇
    ε∙         : ∀{Γ}{Γ∙ : Con∙ Γ} → Sub∙ Γ∙ ◇∙ (ε {Γ})
    ◇η∙        : ∀{Γ}{Γ∙ : Con∙ Γ}{σ : Sub Γ ◇}{σ∙ : Sub∙ Γ∙ ◇∙ σ} → (Sub∙ Γ∙ ◇∙ ~) ◇η σ∙ ε∙

    _[_]∙      : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{t : Tm Γ A}{γ : Sub Δ Γ} → Tm∙ Γ∙ A∙ t → Sub∙ Δ∙ Γ∙ γ → Tm∙ Δ∙ A∙ (t [ γ ])
    [∘]∙       : ∀{Γ Δ Θ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A∙ : Ty∙ A}{t : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ}
                 {t∙ : Tm∙ Γ∙ A∙ t}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ} →
                (Tm∙ Θ∙ A∙ ~) [∘] (t∙ [ γ∙ ⊚∙ δ∙ ]∙) (t∙ [ γ∙ ]∙ [ δ∙ ]∙)
    [id]∙      : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : Tm Γ A}{t∙ : Tm∙ Γ∙ A∙ t} → (Tm∙ Γ∙ A∙ ~) [id] (t∙ [ id∙ ]∙) t∙
    _▹∙_       : ∀{Γ A} → Con∙ Γ → Ty∙ A → Con∙ (Γ ▹ A)
    _,o∙_      : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{t : Tm Δ A}{γ : Sub Δ Γ} → Sub∙ Δ∙ Γ∙ γ → Tm∙ Δ∙ A∙ t → Sub∙ Δ∙ (Γ∙ ▹∙ A∙) (γ ,o t)
    p∙         : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ (p {Γ}{A})
    q∙         : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Tm∙ (Γ∙ ▹∙ A∙) A∙ (q {Γ}{A})
    ▹β₁∙       : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γ : Sub Δ Γ}{t : Tm Δ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{t∙ : Tm∙ Δ∙ A∙ t} → 
                (Sub∙ Δ∙ Γ∙ ~) ▹β₁ (p∙ ⊚∙ (γ∙ ,o∙ t∙)) γ∙
    ▹β₂∙       : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γ : Sub Δ Γ}{t : Tm Δ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{t∙ : Tm∙ Δ∙ A∙ t} →
                (Tm∙ Δ∙ A∙ ~) ▹β₂ (q∙ [ γ∙ ,o∙ t∙ ]∙) t∙
    ▹η∙        : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γa : Sub Δ (Γ ▹ A)}{γa∙ : Sub∙ Δ∙ {Γ ▹ A} (Γ∙ ▹∙ A∙) γa} →
                (Sub∙ Δ∙ (Γ∙ ▹∙ A∙) ~) ▹η (p∙ ⊚∙ γa∙ ,o∙ q∙ [ γa∙ ]∙) γa∙

    Bool∙      : Ty∙ Bool
    true∙      : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ (true {Γ})
    false∙     : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ (false {Γ})
    ite∙       : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : Tm Γ Bool}{u v : Tm Γ A} → Tm∙ Γ∙ Bool∙ t → Tm∙ Γ∙ A∙ u → Tm∙ Γ∙ A∙ v → Tm∙ Γ∙ A∙ (ite t u v)
    iteβ₁∙     : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{u v : Tm Γ A}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v} → 
                (Tm∙ Γ∙ A∙ ~) iteβ₁ (ite∙ true∙ u∙ v∙) u∙
    iteβ₂∙     : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{u v : Tm Γ A}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v} →
                (Tm∙ Γ∙ A∙ ~) iteβ₂ (ite∙ false∙ u∙ v∙) v∙
    true[]∙    : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Tm∙ Δ∙ Bool∙ ~) true[] (true∙ [ γ∙ ]∙) true∙
    false[]∙   : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Tm∙ Δ∙ Bool∙ ~) false[] (false∙ [ γ∙ ]∙) false∙
    ite[]∙     : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : Tm Γ Bool}{u v : Tm Γ A}{t∙ : Tm∙ Γ∙ Bool∙ t}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v}
                {Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ A∙ ~) ite[] ((ite∙ t∙ u∙ v∙) [ γ∙ ]∙) (ite∙ (t∙ [ γ∙ ]∙) (u∙ [ γ∙ ]∙) (v∙ [ γ∙ ]∙))

    _⇒∙_       : ∀{A B} → Ty∙ A → Ty∙ B → Ty∙ (A ⇒ B)
    lam∙       : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : Tm (Γ ▹ A) B} →
                  Tm∙ {Γ ▹ A} (Γ∙ ▹∙ A∙) B∙ t → Tm∙ Γ∙ (A∙ ⇒∙ B∙) (lam t)
    _$∙_       : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A} →
                  Tm∙ {Γ} Γ∙ (A∙ ⇒∙ B∙) t → Tm∙ Γ∙ A∙ u → Tm∙ Γ∙ B∙ (t $ u)
    ⇒β∙        : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A}{t∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ t}{u∙ : Tm∙ Γ∙ A∙ u} →
                  (Tm∙ Γ∙ B∙ ~) ⇒β (lam∙ t∙ $∙ u∙) (t∙ [ id∙ ,o∙ u∙ ]∙)
    ⇒η∙        : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : Tm Γ (A ⇒ B)}{t∙ : Tm∙ Γ∙ (A∙ ⇒∙ B∙) t} →
                  (Tm∙ Γ∙ (A∙ ⇒∙ B∙) ~) ⇒η (lam∙ (t∙ [ p∙ ]∙ $∙ q∙)) t∙
    lam[]∙     : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : Tm (Γ ▹ A) B}{t∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ t}
                {Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ (A∙ ⇒∙ B∙) ~) lam[] ((lam∙ t∙) [ γ∙ ]∙) (lam∙ (t∙ [ γ∙ ⊚∙ p∙ ,o∙ q∙ ]∙))
    $[]∙       : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{t∙ : Tm∙ Γ∙ (A∙ ⇒∙ B∙) t}{u∙ : Tm∙ Γ∙ A∙ u}
                {Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ B∙ ~) $[] ((t∙ $∙ u∙) [ γ∙ ]∙) (t∙ [ γ∙ ]∙ $∙ u∙ [ γ∙ ]∙)

  ⟦_⟧T : (A : Ty) → Ty∙ A
  ⟦ Bool ⟧T = Bool∙
  ⟦ A ⇒ B ⟧T = ⟦ A ⟧T ⇒∙ ⟦ B ⟧T

  ⟦_⟧C : (Γ : Con) → Con∙ Γ
  ⟦ ◇ ⟧C = ◇∙
  ⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C ▹∙ ⟦ A ⟧T

  postulate
    ⟦_⟧S      : ∀{Γ Δ}(γ : Sub Δ Γ) → Sub∙ ⟦ Δ ⟧C  ⟦ Γ ⟧C  γ
    ⟦_⟧t      : ∀{Γ A}(t : Tm Γ A)  → Tm∙  ⟦ Γ ⟧C  ⟦ A ⟧T  t
    ⟦∘⟧       : ∀{Γ Δ Θ}{γ : Sub Δ Γ}{δ : Sub Θ Δ} → 
                         ⟦ γ ⊚ δ ⟧S     ≈ ⟦ γ ⟧S ⊚∙ ⟦ δ ⟧S
    ⟦id⟧      : ∀{Γ} →   ⟦ id {Γ} ⟧S    ≈ id∙
    ⟦ε⟧       : ∀{Γ} →   ⟦ ε {Γ} ⟧S     ≈ ε∙
    ⟦[]⟧      : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Γ A} →
                         ⟦ t [ γ ] ⟧t   ≈ ⟦ t ⟧t [ ⟦ γ ⟧S ]∙
    ⟦,⟧       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} →
                         ⟦ γ ,o t ⟧S    ≈ ⟦ γ ⟧S ,o∙ ⟦ t ⟧t
    ⟦p⟧       : ∀{Γ A} → ⟦ p {Γ}{A} ⟧S  ≈ p∙
    ⟦q⟧       : ∀{Γ A} → ⟦ q {Γ}{A} ⟧t  ≈ q∙
    {-# REWRITE ⟦∘⟧ ⟦id⟧ ⟦ε⟧ ⟦[]⟧ ⟦,⟧ ⟦p⟧ ⟦q⟧ #-}

    ⟦true⟧    : ∀{Γ} →   ⟦ true {Γ} ⟧t  ≈ true∙
    ⟦false⟧   : ∀{Γ} →   ⟦ false {Γ} ⟧t ≈ false∙
    ⟦ite⟧     : ∀{Γ A}{t : Tm Γ Bool}{u v : Tm Γ A} →
                         ⟦ ite t u v ⟧t ≈ ite∙ ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦ite⟧ #-}

    ⟦lam⟧     : ∀{Γ A B}{t : Tm (Γ ▹ A) B} →
                         ⟦ lam t ⟧t     ≈ lam∙ ⟦ t ⟧t
    ⟦$⟧       : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A} →
                         ⟦ t $ u ⟧t     ≈ ⟦ t ⟧t $∙ ⟦ u ⟧t
    {-# REWRITE ⟦lam⟧ ⟦$⟧ #-}

open I
-}
