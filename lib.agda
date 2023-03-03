{-# OPTIONS --prop --rewriting #-}

module lib where

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.Bool public renaming (Bool to 𝟚; true to tt; false to ff)
open import Agda.Builtin.Sigma public renaming (fst to π₁; snd to π₂)

infix  4 _≡_ _≈_
infixr 2 _≡≡_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infixr 7 _⊃_
infixl 8 _∨_
infixl 9 _∧_
infixr 1 _⊎_
infixr 2 _×_
infixr 4 _,=_ _,×=_
infixl 6 _∘_
infixl 2 _◾_
infix 5 _⁻¹


-- rewriting

postulate _≈_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Set ℓ
{-# BUILTIN REWRITE _≈_ #-}


-- exercise

postulate
  exercise  : ∀{ℓ}{A : Set  ℓ} → A
  exercisep : ∀{ℓ}{A : Prop ℓ} → A

-- Bottom

data ⊥ : Prop where

exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()

exfalsop : ∀{ℓ}{A : Prop ℓ} → ⊥ → A
exfalsop ()

¬_ : ∀{ℓ}(A : Prop ℓ) → Prop ℓ
¬ A = A → ⊥


-- Top

record ⊤ : Prop where
  constructor triv

-- Functions

_∘_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : A → Set ℓ'}{C : ∀ {x} → B x → Set ℓ''}
  (f : ∀ {x} (y : B x) → C y)(g : (x : A) → B x)
  (x : A) → C (g x)
(f ∘ g) x = f (g x)


-- Lift

record Lift {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor mk
  field un : A
open Lift public


-- Raise

record Raise {ℓ ℓ'}(A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor mk
  field un : A
open Raise public


-- Equality

data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≢_

_≢_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Prop ℓ
x ≢ y = ¬ (x ≡ y)

_◾_ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → ∀{a''} → a' ≡ a'' → a ≡ a''
refl ◾ refl = refl

postulate subst       : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' : A} → a ≡ a' → P a → P a'
postulate substrefl   : ∀{ℓ}{A : Set ℓ}{ℓ'}{P : A → Set ℓ'}{a : A}{e : a ≡ a}{p : P a} → subst P e p ≈ p
{-# REWRITE substrefl   #-}

_⁻¹ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → a' ≡ a
refl ⁻¹ = refl

cong : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong₂ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}
        {a c : A}{b d : B}(f : A → B → C)(p : a ≡ c)(q : b ≡ d) →
        f a b ≡ f c d
cong₂ f refl refl = refl

cong₃ : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
        {a d : A}{b e : B}{c f : C}(g : A → B → C → D)(p : a ≡ d)(q : b ≡ e)(r : c ≡ f) →
        g a b c ≡ g d e f
cong₃ g refl refl refl = refl

congd : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}(f : (a : A) → B a){a a' : A}(e : a ≡ a') → subst B e (f a) ≡ f a'
congd f refl = refl

substconst  : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}{e : a ≡ a'}{b : B} → subst (λ _ → B) e b ≡ b
substconst {e = refl} = refl

substsubst : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' a'' : A}(e : a ≡ a'){e' : a' ≡ a''}{p : P a} → subst P e' (subst P e p) ≡ subst P (e ◾ e') p
substsubst P refl {refl} = refl

subst→' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : B → C a} → 
  subst (λ a → B → C a) e f ≡ λ b → subst C e (f b)
subst→' C refl = refl

subst→i' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : {b : B} → C a} → 
  (λ {b} → subst (λ a → {B} → C a) e (λ {b} → f {b}) {b}) ≡ (λ {b} → subst C e (f {b}))
subst→i' C refl = refl

substΠ' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ''){a a' : A}(e : a ≡ a'){f : (b : B) → C a b} → 
  subst (λ a → (b : B) → C a b) e f ≡ λ b → subst (λ a → C a b) e (f b)
substΠ' C refl = refl

substΠi' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ''){a a' : A}(e : a ≡ a'){f : {b : B} → C a b} → 
  (λ {b} → subst (λ a → {b : B} → C a b) e f {b}) ≡ λ {b} → subst (λ a → C a b) e (f {b})
substΠi' C refl = refl

subst→ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : B a → C a} → 
  subst (λ a → B a → C a) e f ≡ λ b' → subst C e (f (subst B (e ⁻¹) b'))
subst→ C refl = refl

substcong : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : B → Set ℓ'')(f : A → B){a a' : A}(e : a ≡ a'){c : C (f a)} →
  subst {A = B} C (cong f e) c ≡ subst {A = A} (λ a → C (f a)) e c
substcong C f refl = refl

subst$ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}(f : ∀ a → B a → C a){a a' : A}(e : a ≡ a'){b : B a} → f a' (subst B e b) ≡ subst C e (f a b) 
subst$ f refl = refl

subst$i : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}(f : ∀{a} → B a → C a){a a' : A}(e : a ≡ a'){b : B a} → f (subst B e b) ≡ subst C e (f b) 
subst$i f refl = refl

-- if this doesn't normalise (C-c C-n PROBLEM), then your Agda is too old
PROBLEM : {A : Set}(B : A → Prop){a a' : A}(e : a ≡ a') → B a → Lift (B a')
PROBLEM B e b = subst (λ a → Lift (B a)) e (mk b)

_~ : ∀{ℓ ℓ'}{A : Set ℓ}(B : A → Set ℓ'){a₀ a₁ : A}(a₀₁ : a₀ ≡ a₁) → B a₀ → B a₁ → Prop ℓ'
(B ~) a₀₁ b₀ b₁ = subst B a₀₁ b₀ ≡ b₁

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

_≡≡_ : ∀{ℓ}{A : Set ℓ}(x : A){y} → x ≡ y → x ≡ y
x ≡≡ x≡y = x≡y

_∎ : ∀{ℓ}{A : Set ℓ}(a : A) → a ≡ a
a ∎ = refl

substP : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Prop ℓ'){a a' : A} → a ≡ a' → P a → P a'
substP P refl p = p

UIP : ∀{ℓ}{A : Set ℓ}{a a' : A}{e e' : a ≡ a'} → _≡_ {A = Lift (a ≡ a')} (mk e) (mk e')
UIP = refl


-- Function space

postulate funext  : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
postulate funexti : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g


-- Maybe

data Maybe {ℓ}(A : Set ℓ) : Set ℓ where
  Nothing  : Maybe A
  Just     : A → Maybe A

caseMaybe : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (A → B) → Maybe A → B
caseMaybe n j Nothing = n
caseMaybe n j (Just a) = j a


-- Product

_×_ : ∀{ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

_,=_ : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{a a' : A}(e : a ≡ a') → {b : B a}{b' : B a'} → (B ~) e b b' → (a , b) ≡ (a' , b')
_,=_ refl refl = refl

_,×=_ : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}(e : a ≡ a') → {b b' : B} → b  ≡ b' → (a , b) ≡ (a' , b')
_,×=_ refl refl = refl

record Σsp {ℓ ℓ'} (A : Set ℓ)(B : A → Prop ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σsp public
infixr 4 _,_

_,=- : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Prop ℓ'}{a a' : A}(e : a ≡ a') → {b : B a}{b' : B a'} → _≡_ {A = Σsp A B} (a , b) (a' , b')
_,=- refl = refl

subst× : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}(B : A → Set ℓ')(C : A → Set ℓ''){a : A}{w : B a × C a}{a' : A}(e : a ≡ a') →
  subst (λ a → B a × C a) e w ≡ (subst B e (π₁ w) , subst C e (π₂ w))
subst× B C refl = refl

substΣ' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ''){a a' : A}(e : a ≡ a'){w : Σ B (C a)} →
  subst (λ a → Σ B (C a)) e w ≡ (π₁ w , subst (λ a → C a (π₁ w)) e (π₂ w))
substΣ' C refl = refl


-- ℕ

max : ℕ → ℕ → ℕ
max zero    b       = b
max (suc a) zero    = suc a
max (suc a) (suc b) = suc (max a b)

iteℕ : ∀{ℓ}{A : Set ℓ}(u : A)(v : A → A)(t : ℕ) → A
iteℕ u v zero = u
iteℕ u v (suc t) = v (iteℕ u v t)

indℕ : ∀{ℓ}(A : ℕ → Set ℓ)(z : A zero)(s : ∀ n → A n → A (suc n))(n : ℕ) → A n
indℕ A z s zero = z
indℕ A z s (suc n) = s n (indℕ A z s n)

zero≠suc : {n : ℕ} → ¬ (zero ≡ suc n)
zero≠suc e = substP P e triv
  where
    P : ℕ → Prop
    P zero = ⊤
    P (suc _) = ⊥

ass+ : ∀{m n o} → (m + n) + o ≡ m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})

idr+ : ∀{n} → n + 0 ≡ n
idr+ {zero} = refl
idr+ {suc n} = cong suc (idr+ {n})

+suc : ∀{m n} → m + suc n ≡ suc (m + n)
+suc {zero} = refl
+suc {suc m} = cong suc (+suc {m})

+comm : ∀{m n} → m + n ≡ n + m
+comm {zero} = idr+ ⁻¹
+comm {suc m}{n} = cong suc (+comm {m}{n}) ◾ +suc {n}{m} ⁻¹

-- 𝟚

if_then_else_ : ∀{ℓ}{A : Set ℓ}(t : 𝟚)(u v : A) → A
if tt then u else v = u
if ff then u else v = v

_∨_ : 𝟚 → 𝟚 → 𝟚
a ∨ b = if a then tt else b

_∧_ : 𝟚 → 𝟚 → 𝟚
a ∧ b = if a then b else ff

_⊃_ : 𝟚 → 𝟚 → 𝟚
a ⊃ b = if a then b else tt

tt≠ff : ¬ (tt ≡ ff)
tt≠ff e = substP P e triv
  where
    P : 𝟚 → Prop
    P tt = ⊤
    P ff = ⊥


-- Sum type

data _⊎_ {ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B

case : ∀ {ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}
       (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (ι₁ t) u v = u t
case (ι₂ t) u v = v t

ind⊎ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(P : A ⊎ B → Set ℓ'') →
       ((a : A) → P (ι₁ a)) → ((b : B) → P (ι₂ b)) → (t : A ⊎ B) → P t
ind⊎ P u v (ι₁ t) = u t
ind⊎ P u v (ι₂ t) = v t

subst⊎ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}(B : A → Set ℓ')(C : A → Set ℓ''){a : A}{w : B a ⊎ C a}{a' : A}(e : a ≡ a') →
  subst (λ a → B a ⊎ C a) e w ≡ case w (λ b → ι₁ (subst B e b)) (λ c → ι₂ (subst C e c))
subst⊎ B C {w = ι₁ a} refl = refl
subst⊎ B C {w = ι₂ b} refl = refl

casesubst : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}(B : A → Set ℓ')(C : A → Set ℓ''){D : Set ℓ'''}{a a' : A}(e : a ≡ a')(w : B a ⊎ C a){u : B a' → D}{v : C a' → D} →
  case (subst (λ a → B a ⊎ C a) e w) u v ≡ case w (λ b → u (subst B e b)) (λ c → v (subst C e c))
casesubst B C refl w = refl

substcase : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}(D : A → Set ℓ'''){a a' : A}(e : a ≡ a')(w : B ⊎ C){u : B → D a}{v : C → D a} →
  subst D e (case w u v) ≡ case w (λ a → subst D e (u a)) (λ b → subst D e (v b))
substcase D refl w = refl


-- finite types

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

{-# INJECTIVE Fin #-}

-- more subst rules

substΠ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}(C : (a : A) → B a → Set ℓ''){a a' : A}(e : a ≡ a'){f : (b : B a) → C a b} → 
  subst (λ a → (b : B a) → C a b) e f ≡ λ b' → subst (λ ab → C (π₁ ab) (π₂ ab)) (e ,= substsubst B (e ⁻¹)) (f (subst B (e ⁻¹) b'))
substΠ C refl = refl

substΠi : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}(C : (a : A) → B a → Set ℓ''){a a' : A}(e : a ≡ a'){f : {b : B a} → C a b} → 
  (λ {b'} → subst (λ a → {b : B a} → C a b) e f {b'}) ≡ λ {b'} → subst (λ ab → C (π₁ ab) (π₂ ab)) (e ,= substsubst B (e ⁻¹)) (f {subst B (e ⁻¹) b'})
substΠi C refl = refl

subst2left : ∀{ℓ ℓ'}{A : Set ℓ}(B : A → Set ℓ'){a a' : A}(e : a ≡ a'){b : B a}{b' : B a'} →
  subst B e b ≡ b' → b ≡ subst B (e ⁻¹) b'
subst2left B refl e = e
