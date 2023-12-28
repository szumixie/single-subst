\section{Single substitution calculus}
\label{sec:SSC}

In this section we define the syntax of a type theory with dependent
function space and an infinite hierarchy of Coquand-universes
\cite{coquandUniverse}. The syntax is given by a quotient inductive-inductive type (QIIT),
we list its sorts and constructors, and we briefly discuss its induction principle.

\begin{code}[hide]
{-# OPTIONS --with-K --rewriting #-}

module SSC where

open import Lib

private variable
  ℓᶜ ℓˢ ℓᵀ ℓᵗ ℓᵛ : Level
  i j : ℕ
\end{code}

We start by declaring the sorts of our language: first of all,
contexts and types.
\begin{code}
data       Con  : Set 
postulate  Ty   : Con → ℕ → Set
\end{code}
Contexts are forward declared as an inductive set, and types are postulated because
they will include equality constructors. Types are indexed by their context and
a universe level. Contexts have two constructors: a context is either empty, or is another context extended by a type:
\begin{code}[hide]
infixl 2 _▹_
\end{code}
\begin{code}
data Con where
  ◇    : Con
  _▹_  : (Γ : Con) → Ty Γ i → Con
\end{code}
\begin{code}[hide]
private variable
  Γ Γ₀ Γ₁ Δ : Con
  A A₀ A₁ B B₀ B₁ B₂ C : Ty Γ i
\end{code}
Just as the sort of types, the sort of terms is postulated:
\begin{code}
postulate Tm : (Γ : Con) → Ty Γ i → Set
\end{code}
Terms are indexed by their context and type. For example, a term that
can refer to two different free variables of types \AgdaGeneralizable{A₀} and \AgdaGeneralizable{A₁} which itself has
type \AgdaGeneralizable{B}, is in the set \AD{Tm}\AgdaSpace{}\AgdaSymbol{(}\AC{◇}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A₀}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A₁}\AgdaSymbol{)}\AgdaSpace{}\AgdaGeneralizable{B}. Note that later types depend
on more information than previous ones: \AgdaGeneralizable{A₀} is a type in the
empty context (\AgdaGeneralizable{A₀}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AD{Ty}\AgdaSpace{}\AC{◇}\AgdaSpace{}\AgdaGeneralizable{i}), but
\AgdaGeneralizable{A₁}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AD{Ty}\AgdaSpace{}\AgdaSymbol{(}\AC{◇}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A₀}\AgdaSymbol{)}\AgdaSpace{}\AgdaGeneralizable{j}
and
\AgdaGeneralizable{B}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AD{Ty}\AgdaSpace{}\AgdaSymbol{(}\AC{◇}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A₀}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A₁}\AgdaSymbol{)}\AgdaSpace{}\AgdaGeneralizable{k}.

The first term constructors that we will introduce are variables. For example, we would
like to have a term \AD{Tm}\AgdaSpace{}\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A}\AgdaSymbol{)}\AgdaSpace{}\AgdaGeneralizable{A} for any context
\AgdaGeneralizable{Γ} and type
\AgdaGeneralizable{A}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AD{Ty}\AgdaSpace{}\AgdaGeneralizable{Γ}\AgdaSpace{}\AgdaGeneralizable{i}. This should be the variable given by De Bruijn \cite{debruijn} index $0$, that is, the
last variable in the context. However this set of terms does not make sense: the type of the term has to be in the same context as the term, but our type is in \AgdaGeneralizable{Γ}, our term is however in \AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A}.
This is why we need to weaken the type of the term \AgdaGeneralizable{A} to be usable in the same context, and De Bruijn index $0$ will be in
\AD{Tm}\AgdaSpace{}\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A}\AgdaSymbol{)}\AgdaSpace{}\AgdaSymbol{(}\AgdaGeneralizable{A}\AgdaSpace{}\AD{[}\AgdaSpace{}\AC{p}\AgdaSpace{}\AD{]ᵀ}\AgdaSymbol{)}.
We have an inductive sort \AD{Sub} of substitutions, and an operation \AD{\_[\_]ᵀ} called instantiation. They are declared as follows.
\begin{code}
data Sub : Con → Con → Set
postulate
  _[_]ᵀ : Ty Γ i → Sub Δ Γ → Ty Δ i
\end{code}
\begin{code}[hide]
infixl 9 _[_]ᵀ
\end{code}
Instantiation takes a type that has free variables in \AgdaGeneralizable{Γ},
and a substitution from \AgdaGeneralizable{Δ} to \AgdaGeneralizable{Γ} and returns a type in context
\AgdaGeneralizable{Δ}. Note that instantiation is a constructor of our QIIT, thus we define
an explicit substitution calculus. The substitution laws are given by equality constructors
rather than definitional equalities.
\begin{code}[hide]
infixl 10 _⁺
\end{code}
We have three different ways to construct substitutions: the above used \emph{weakening} \AC{p}, a single term turned into a substitution via \AC{⟨\_⟩}, and \emph{lifting} of a pre-existing substitution.
Lifting leaves the last variable untouched.
\begin{code}
data Sub where
  p    : Sub (Γ ▹ A) Γ
  ⟨_⟩  : Tm Γ A → Sub Γ (Γ ▹ A)
  _⁺   : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A)
\end{code}
Hence, a substitution is either a single weakening lifted a finite number of times
\[\text{
\AC{p}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AD{Sub}\AgdaSpace{}
\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{B₀}\AgdaSpace{}\AD{[}\AgdaSpace{}\AC{p}\AgdaSpace{}\AD{]ᵀ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{Bₙ}\AgdaSpace{}\AD{[}\AgdaSpace{}\AC{p}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AD{]ᵀ}\AgdaSymbol{)}\AgdaSpace{}
\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{B₀}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{Bₙ}\AgdaSymbol{)},
}\]
or a single term weakened a finite number of times
\[\text{
\AC{⟨}\AgdaSpace{}\AgdaGeneralizable{t}\AgdaSpace{}\AC{⟩}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AD{Sub}\AgdaSpace{}
\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{B₀}\AgdaSpace{}\AD{[}\AgdaSpace{}\AC{⟨}\AgdaSpace{}\AgdaGeneralizable{t}\AgdaSpace{}\AC{⟩}\AgdaSpace{}\AD{]ᵀ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{Bₙ}\AgdaSpace{}\AD{[}\AgdaSpace{}\AC{⟨}\AgdaSpace{}\AgdaGeneralizable{t}\AgdaSpace{}\AC{⟩}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{⁺}\AgdaSpace{}\AD{]ᵀ}\AgdaSymbol{)}\AgdaSpace{}
\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{B₀}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaSymbol{⋯}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{Bₙ}\AgdaSymbol{)}.
}\]
\begin{code}[hide]
p⁺    : Sub (Γ ▹ A ▹ B₀ [ p ]ᵀ) (Γ ▹ B₀)
p⁺    = p ⁺
p⁺⁺   : Sub (Γ ▹ A ▹ B₀ [ p ]ᵀ ▹ B₁ [ p ⁺ ]ᵀ) (Γ ▹ B₀ ▹ B₁)
p⁺⁺   = p ⁺ ⁺
p⁺⁺⁺  : Sub (Γ ▹ A ▹ B₀ [ p ]ᵀ ▹ B₁ [ p ⁺ ]ᵀ ▹ B₂ [ p ⁺ ⁺ ]ᵀ) (Γ ▹ B₀ ▹ B₁ ▹ B₂)
p⁺⁺⁺  = p ⁺ ⁺ ⁺

⟨_⟩⁺     : (t : Tm Γ A) → Sub (Γ ▹ B₀ [ ⟨ t ⟩ ]ᵀ) (Γ ▹ A ▹ B₀)
⟨ t ⟩⁺   = ⟨ t ⟩ ⁺
⟨_⟩⁺⁺ :  (t : Tm Γ A) → Sub (Γ ▹ B₀ [ ⟨ t ⟩ ]ᵀ ▹ B₁ [ ⟨ t ⟩ ⁺ ]ᵀ) (Γ ▹ A ▹ B₀ ▹ B₁)
⟨ t ⟩⁺⁺  = ⟨ t ⟩ ⁺ ⁺
\end{code}
Weakening is introduced to express the variable rule. The other two
constructors will be explained later. For now, we just say that single
substitution is needed to express the computation
rule for function space, and lifting is needed for the
substitution rules of binders.

Now we introduce variables as well-typed De Bruijn indices.
\begin{code}
data Var : (Γ : Con) → Ty Γ i → Set where
  vz : Var (Γ ▹ A) (A [ p ]ᵀ)
  vs : Var Γ B → Var (Γ ▹ A) (B [ p ]ᵀ)
postulate
  var : Var Γ A → Tm Γ A
\end{code}
To illustrate their usage, we define the first three De Bruijn indices as the
following abbreviations.
\begin{code}
v0 : Tm (Γ ▹ A) (A [ p ]ᵀ)
v0 = var vz
v1 : Tm (Γ ▹ A ▹ B) (A [ p ]ᵀ [ p ]ᵀ)
v1 = var (vs vz)
v2 : Tm (Γ ▹ A ▹ B ▹ C) (A [ p ]ᵀ [ p ]ᵀ [ p ]ᵀ)
v2 = var (vs (vs vz))
\end{code}
Just as we can instantiate types using a substitution, we can do the same for terms.
\begin{code}[hide]
infixl 9 _[_]ᵗ
\end{code}
\begin{code}
postulate
  _[_]ᵗ : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ)
\end{code}
Note that it refers to type instantiation \AD{\_[\_]ᵀ} in the type of the result.
\begin{code}[hide]
private variable
  γ : Sub Δ Γ
  a b f α : Tm Γ A
  x : Var Γ A

transpTy : Γ₀ ≡ Γ₁ → Ty Γ₀ i → Ty Γ₁ i
transpTy refl A = A

transpTm : (Γ₀₁ : Γ₀ ≡ Γ₁) → transpTy Γ₀₁ A₀ ≡ A₁ → Tm Γ₀ A₀ → Tm Γ₁ A₁
transpTm refl refl a = a
\end{code}
The following equations govern how we instantiate variables by the three different
kinds of substitutions.
\begin{itemize}
\item Weakening of a variable increases its index by one.
\begin{code}
postulate
  var-p : var x [ p ]ᵗ ≡ (Tm (Γ ▹ A) (B [ p ]ᵀ) ∋ var (vs x))
\end{code}
\item Instantiating a variable by a single term substitution depends on whether
  the variable is zero or successor. In the former case, we simply return the term (\AD{vz-⟨⟩}).
  In the latter case, we decrease the De Bruijn index (\AD{vs-⟨⟩}). The terms on the two sides of these
  equations have different types, the equality of which is stated by \AD{p-⟨⟩ᵀ}.
\begin{code}
postulate
  p-⟨⟩ᵀ  : B [ p ]ᵀ [ ⟨ a ⟩ ]ᵀ ≡ B
  vz-⟨⟩  : transpTm refl p-⟨⟩ᵀ (var vz      [ ⟨ a ⟩ ]ᵗ) ≡ a
  vs-⟨⟩  : transpTm refl p-⟨⟩ᵀ (var (vs x)  [ ⟨ a ⟩ ]ᵗ) ≡ var x
\end{code}
\item When instantiating a variable by a lifted substitution, we again 
  do case distinction on the variable. In short, a lifted substitution does not
  affect the last variable in the context, hence it stays zero (\AD{vz-⁺}).
  If the variable is a successor, then we read the variable out of the
  original substitution, and we weaken the result. Again, to typecheck the equations,
  we require an equation on types (\AD{p-⁺ᵀ}).
\begin{code}
postulate
  p-⁺ᵀ  : B [ p ]ᵀ [ γ ⁺ ]ᵀ ≡ (Ty (Δ ▹ A [ γ ]ᵀ) i ∋ B [ γ ]ᵀ [ p ]ᵀ)
  vz-⁺  : transpTm refl p-⁺ᵀ (var vz      [ γ ⁺ ]ᵗ) ≡ (Tm (Δ ▹ A [ γ ]ᵀ) (A [ γ ]ᵀ [ p ]ᵀ) ∋ var vz)
  vs-⁺  : transpTm refl p-⁺ᵀ (var (vs x)  [ γ ⁺ ]ᵗ) ≡ (Tm (Δ ▹ A [ γ ]ᵀ) (B [ γ ]ᵀ [ p ]ᵀ) ∋ var x [ γ ]ᵗ [ p ]ᵗ)
\end{code}
\end{itemize}
Finally we state two more equations on types that will be required to write down
the substitution rule for the application constructor, and the $\eta$ law for function space, respectively.
\begin{code}
postulate
  ⟨⟩-[]ᵀ : B [ ⟨ a ⟩ ]ᵀ [ γ ]ᵀ ≡ B [ γ ⁺ ]ᵀ [ ⟨ a [ γ ]ᵗ ⟩ ]ᵀ
  ▹-ηᵀ   : B ≡ B [ p ⁺ ]ᵀ [ ⟨ var vz ⟩ ]ᵀ
\end{code}
This concludes the definition of the substitution calculus, that is, the part of
the syntax of type theory which does not refer to concrete type formers.

Now we list the rules for our type formers, first for the universe,
and then for the function space. As usual, the rules come in groups:
type formation rules, introduction rules, elimination rules, computation ($\beta$) and
uniqueness ($\eta$) rules. In addition, we have substitution rules
explaining how to instantiate each constructor.

The universe is given by a natural isomorphism
\text{\AD{Tm}\AgdaSpace{}\AgdaGeneralizable{Γ}\AgdaSpace{}\AgdaSymbol{(}\AD{U}\AgdaSpace{}\AgdaGeneralizable{i}\AgdaSymbol{)}}
$\cong$
\text{\AD{Ty}\AgdaSpace{}\AgdaGeneralizable{Γ}\AgdaSpace{}\AgdaGeneralizable{i}}.
The introduction rule is \AD{c} is called ``code'', the elimination \AD{El} gives the type of ``elements'' of the universe.
Naturality is expressed by the substitution laws. The substitution laws for \AD{c} and \AD{El} depend on that of \AD{U}.
\begin{code}
postulate
  U      : (i : ℕ) → Ty Γ (suc i)
  El     : Tm Γ (U i) → Ty Γ i
  c      : Ty Γ i → Tm Γ (U i)
  U-β    : El (c A) ≡ A
  U-η    : α ≡ c (El α)
  U-[]   : U i [ γ ]ᵀ ≡ U i
  El-[]  : El α [ γ ]ᵀ ≡ El (transpTm refl U-[] (α [ γ ]ᵗ))
  c-[]   : transpTm refl U-[] (c A [ γ ]ᵗ) ≡ c (A [ γ ]ᵀ)
\end{code}
The dependent function type former \AD{Π} is a binder, there is an extra free variable
in its second argument. The introduction, elimination, $\beta$ and $\eta$ rules are given by a natural isomorphism
\AD{Tm}\AgdaSpace{}\AgdaSymbol{(}\AgdaGeneralizable{Γ}\AgdaSpace{}\AC{▹}\AgdaSpace{}\AgdaGeneralizable{A}\AgdaSymbol{)}\AgdaSpace{}B
$\cong$
\AD{Tm}\AgdaSpace{}\AgdaGeneralizable{Γ}\AgdaSpace{}\AgdaSymbol{(}\AD{Π}\AgdaSpace{}\AgdaGeneralizable{A}\AgdaSpace{}\AgdaGeneralizable{B}\AgdaSymbol{)}.
The left to right direction of the isomorphism is given by \AD{lam}. Instead of directly
assuming the right to left direction, we define the more traditional two-argument
application operator.
\begin{code}
  Π       : (A : Ty Γ i) → Ty (Γ ▹ A) i → Ty Γ i
  lam     : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  app     : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]ᵀ)
  Π-β     : app (lam b) a ≡ b [ ⟨ a ⟩ ]ᵗ
  Π-[]    : Π A B [ γ ]ᵀ ≡ Π (A [ γ ]ᵀ) (B [ γ ⁺ ]ᵀ)
  Π-η     : f ≡ lam (transpTm refl (sym ▹-ηᵀ) (app (transpTm refl Π-[] (f [ p ]ᵗ)) (var vz)))
  app-[]  : transpTm refl ⟨⟩-[]ᵀ (app f a [ γ ]ᵗ) ≡ app (transpTm refl Π-[] (f [ γ ]ᵗ)) (a [ γ ]ᵗ)
  lam-[]  : transpTm refl Π-[] (lam b [ γ ]ᵗ) ≡ lam (b [ γ ⁺ ]ᵗ)
\end{code}
The substitution rule for \AD{Π} illustrates the need for lifting of substitutions: the last variable
has to be left untouched by the substitution. The $\beta$ law illustrates the need for single term substitutions:
we substitute the last free variable in \AgdaGeneralizable{b} by \AgdaGeneralizable{a}.

With this we conclude the definition of the constructors for our syntax.

Just as for natural numbers in Subsection \ref{sec:metatheory}, we
define a notion of dependent model of type theory, and postulate the
induction principle. This part is automatic, there is no creativity
involved, there are generic algorithms which compute the notion of
dependent model and the types of the induction principle from the
types of the constructors \cite{DBLP:journals/pacmpl/KaposiKA19}.
Here we list some of the fields of a dependent model, and
the types of the induction principle. Consult the formalisation for all details.
\begin{code}[hide]
private variable
  Γ₀₁ : Γ₀ ≡ Γ₁
  A₀₁ : A₀ ≡ A₁
  a₀ a₁ : Tm Γ A

transpTy-shiftr : transpTy Γ₀₁ A₀ ≡ A₁ → A₀ ≡ transpTy (sym Γ₀₁) A₁
transpTy-shiftr {Γ₀₁ = refl} A₀₁ = A₀₁

transpTm-shiftr :
  transpTm Γ₀₁ A₀₁ a₀ ≡ a₁ → a₀ ≡
  transpTm (sym Γ₀₁) (sym (transpTy-shiftr {Γ₀₁ = Γ₀₁} A₀₁)) a₁
transpTm-shiftr {Γ₀₁ = refl} {A₀₁ = refl} a₀₁ = a₀₁

transpVar : A₀ ≡ A₁ → Var Γ A₀ → Var Γ A₁
transpVar refl x = x

transp-var : transpTm refl A₀₁ (var x) ≡ var (transpVar A₀₁ x)
transp-var {A₀₁ = refl} = refl

private
  module Util
    (Conᴹ : Con → Set ℓᶜ) (Tyᴹ : ∀ {Γ} → Conᴹ Γ → (i : ℕ) → Ty Γ i → Set ℓᵀ)
    where
    transpTyᴹ : {Γᴹ : Conᴹ Γ} → A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ → Tyᴹ Γᴹ i A₁
    transpTyᴹ refl Aᴹ₀ = Aᴹ₀

    tyᴹ[]-shiftr :
      {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁} →
      transpTyᴹ A₀₁ Aᴹ₀ ≡ Aᴹ₁ → Aᴹ₀ ≡ transpTyᴹ (sym A₀₁) Aᴹ₁
    tyᴹ[]-shiftr {A₀₁ = refl} A₀₁ = A₀₁

    module _ (Tmᴹ : ∀ {Γ A} (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set ℓᵗ) where
      tmᴹ[_,_,_] :
        {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁}
        (A₀₁ : A₀ ≡ A₁) → transpTyᴹ A₀₁ Aᴹ₀ ≡ Aᴹ₁ → transpTm refl A₀₁ a₀ ≡ a₁ →
        Tmᴹ Γᴹ Aᴹ₀ a₀ → Tmᴹ Γᴹ Aᴹ₁ a₁
      tmᴹ[ refl ,  refl , refl ] aᴹ₀ = aᴹ₀
\end{code}
\begin{AgdaAlign}
\begin{code}
record DModel ℓᶜ ℓˢ ℓᵀ ℓᵗ ℓᵛ : Set (ℓ.suc (ℓᶜ ⊔ ℓˢ ⊔ ℓᵀ ⊔ ℓᵗ ⊔ ℓᵛ)) where
\end{code}
\begin{code}[hide]
  no-eta-equality
  infixl 9 _[_]ᵀᴹ _[_]ᵗᴹ
\end{code}
\begin{code}
  field
    Conᴹ    : Con → Set ℓᶜ
    Subᴹ    : Conᴹ Δ → Conᴹ Γ → Sub Δ Γ → Set ℓˢ
    Tyᴹ     : Conᴹ Γ → (i : ℕ) → Ty Γ i → Set ℓᵀ
    _[_]ᵀᴹ  : {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} → Tyᴹ Γᴹ i A → Subᴹ Δᴹ Γᴹ γ → Tyᴹ Δᴹ i (A [ γ ]ᵀ)
\end{code}
\begin{code}[hide]
    Tmᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Tm Γ A → Set ℓᵗ
    _[_]ᵗᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} →
      Tmᴹ Γᴹ Aᴹ a → (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Tmᴹ Δᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (a [ γ ]ᵗ)
      
  transpTyᴹ : {Γᴹ : Conᴹ Γ} → A₀ ≡ A₁ → Tyᴹ Γᴹ i A₀ → Tyᴹ Γᴹ i A₁
  transpTyᴹ = Util.transpTyᴹ Conᴹ Tyᴹ

  tyᴹ[]-shiftr :
    {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁} →
    transpTyᴹ A₀₁ Aᴹ₀ ≡ Aᴹ₁ → Aᴹ₀ ≡ transpTyᴹ (sym A₀₁) Aᴹ₁
  tyᴹ[]-shiftr = Util.tyᴹ[]-shiftr Conᴹ Tyᴹ

  tmᴹ[_,_,_] :
    {Γᴹ : Conᴹ Γ} {Aᴹ₀ : Tyᴹ Γᴹ i A₀} {Aᴹ₁ : Tyᴹ Γᴹ i A₁}
    (A₀₁ : A₀ ≡ A₁) → transpTyᴹ A₀₁ Aᴹ₀ ≡ Aᴹ₁ → transpTm refl A₀₁ a₀ ≡ a₁ →
    Tmᴹ Γᴹ Aᴹ₀ a₀ → Tmᴹ Γᴹ Aᴹ₁ a₁
  tmᴹ[_,_,_] = Util.tmᴹ[_,_,_] Conᴹ Tyᴹ Tmᴹ

  infixl 2 _▹ᴹ_
  field
\end{code}
\begin{code}
    ◇ᴹ      : Conᴹ ◇
    _▹ᴹ_    : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Conᴹ (Γ ▹ A)
    pᴹ      : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Subᴹ (Γᴹ ▹ᴹ Aᴹ) Γᴹ p
\end{code}
\begin{code}[hide]
  field
    Varᴹ : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ i A → Var Γ A → Set ℓᵛ
    varᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Varᴹ Γᴹ Aᴹ x → Tmᴹ Γᴹ Aᴹ (var x)

    vzᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Varᴹ (Γᴹ ▹ᴹ Aᴹ) (Aᴹ [ pᴹ ]ᵀᴹ) vz
    vsᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} →
      Varᴹ Γᴹ Bᴹ x → Varᴹ (Γᴹ ▹ᴹ Aᴹ) (Bᴹ [ pᴹ ]ᵀᴹ) (vs x)
    var-pᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} {xᴹ : Varᴹ Γᴹ Bᴹ x} →
      tmᴹ[ refl , refl , var-p ] (varᴹ xᴹ [ pᴹ ]ᵗᴹ) ≡
      (Tmᴹ (Γᴹ ▹ᴹ Aᴹ) (Bᴹ [ pᴹ ]ᵀᴹ) (var (vs x)) ∋ varᴹ (vsᴹ xᴹ))

  infixl 10 _⁺ᴹ
  field
\end{code}
\begin{code}
    _⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A}
      (γᴹ : Subᴹ Δᴹ Γᴹ γ) → Subᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Γᴹ ▹ᴹ Aᴹ) (γ ⁺)
    p-⁺ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      transpTyᴹ p-⁺ᵀ (Bᴹ [ pᴹ ]ᵀᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ) ≡
      (Tyᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) j (B [ γ ]ᵀ [ p ]ᵀ) ∋ Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ)
\end{code}
\end{AgdaAlign}
\begin{code}[hide]
    vz-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ p-⁺ᵀ , p-⁺ᵀᴹ , vz-⁺ ] (varᴹ vzᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ) ≡
      (Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Aᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (var vz) ∋ varᴹ vzᴹ)
    vs-⁺ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {xᴹ : Varᴹ Γᴹ Bᴹ x} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ p-⁺ᵀ , p-⁺ᵀᴹ , vs-⁺ ] (varᴹ (vsᴹ xᴹ) [ γᴹ ⁺ᴹ ]ᵗᴹ) ≡
      (Tmᴹ (Δᴹ ▹ᴹ Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ]ᵀᴹ [ pᴹ ]ᵀᴹ) (var x [ γ ]ᵗ [ p ]ᵗ)
        ∋ varᴹ xᴹ [ γᴹ ]ᵗᴹ [ pᴹ ]ᵗᴹ)

    ⟨_⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → Tmᴹ Γᴹ Aᴹ a → Subᴹ Γᴹ (Γᴹ ▹ᴹ Aᴹ) ⟨ a ⟩
    p-⟨⟩ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      transpTyᴹ p-⟨⟩ᵀ (Bᴹ [ pᴹ ]ᵀᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ) ≡ Bᴹ

    vz-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tmᴹ[ p-⟨⟩ᵀ , p-⟨⟩ᵀᴹ , vz-⟨⟩ ] (varᴹ vzᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ) ≡ aᴹ
    vs-⟨⟩ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ Γᴹ j B}
      {xᴹ : Varᴹ Γᴹ Bᴹ x} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tmᴹ[ p-⟨⟩ᵀ , p-⟨⟩ᵀᴹ , vs-⟨⟩ ] (varᴹ (vsᴹ xᴹ) [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ) ≡ varᴹ xᴹ

    ⟨⟩-[]ᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) j B}
      {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      transpTyᴹ ⟨⟩-[]ᵀ (Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ [ γᴹ ]ᵀᴹ) ≡
      Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ aᴹ [ γᴹ ]ᵗᴹ ⟩ᴹ ]ᵀᴹ
    ▹-ηᵀᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) j B} →
      transpTyᴹ ▹-ηᵀ Bᴹ ≡ Bᴹ [ pᴹ ⁺ᴹ ]ᵀᴹ [ ⟨ varᴹ vzᴹ ⟩ᴹ ]ᵀᴹ

  field
    Uᴹ : {Γᴹ : Conᴹ Γ} (i : ℕ) → Tyᴹ Γᴹ (suc i) (U i)
    U-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      transpTyᴹ U-[] (Uᴹ i [ γᴹ ]ᵀᴹ) ≡ Uᴹ i

    Elᴹ : {Γᴹ : Conᴹ Γ} → Tmᴹ Γᴹ (Uᴹ i) α → Tyᴹ Γᴹ i (El α)
    El-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {αᴹ : Tmᴹ Γᴹ (Uᴹ i) α} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      transpTyᴹ El-[] (Elᴹ αᴹ [ γᴹ ]ᵀᴹ) ≡
      Elᴹ (tmᴹ[ U-[] , U-[]ᴹ , refl ] (αᴹ [ γᴹ ]ᵗᴹ))

    cᴹ : {Γᴹ : Conᴹ Γ} → Tyᴹ Γᴹ i A → Tmᴹ Γᴹ (Uᴹ i) (c A)
    c-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ U-[] , U-[]ᴹ , c-[] ] (cᴹ Aᴹ [ γᴹ ]ᵗᴹ) ≡ cᴹ (Aᴹ [ γᴹ ]ᵀᴹ)

    U-βᴹ : {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} → transpTyᴹ U-β (Elᴹ (cᴹ Aᴹ)) ≡ Aᴹ
    U-ηᴹ :
      {Γᴹ : Conᴹ Γ} {αᴹ : Tmᴹ Γᴹ (Uᴹ i) α} →
      tmᴹ[ refl , refl , U-η ] αᴹ ≡ cᴹ (Elᴹ αᴹ)

    Πᴹ : {Γᴹ : Conᴹ Γ} (Aᴹ : Tyᴹ Γᴹ i A) → Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B → Tyᴹ Γᴹ i (Π A B)
    Π-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      transpTyᴹ Π-[] (Πᴹ Aᴹ Bᴹ [ γᴹ ]ᵀᴹ) ≡ Πᴹ (Aᴹ [ γᴹ ]ᵀᴹ) (Bᴹ [ γᴹ ⁺ᴹ ]ᵀᴹ)

    appᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B} →
      Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f →
      (aᴹ : Tmᴹ Γᴹ Aᴹ a) → Tmᴹ Γᴹ (Bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵀᴹ) (app f a)
    app-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} {aᴹ : Tmᴹ Γᴹ Aᴹ a} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ ⟨⟩-[]ᵀ , ⟨⟩-[]ᵀᴹ , app-[] ] (appᴹ fᴹ aᴹ [ γᴹ ]ᵗᴹ) ≡
      appᴹ (tmᴹ[ Π-[] , Π-[]ᴹ , refl ] (fᴹ [ γᴹ ]ᵗᴹ)) (aᴹ [ γᴹ ]ᵗᴹ)

    lamᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B} →
      Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (lam b)
    lam-[]ᴹ :
      {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {bᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b} {γᴹ : Subᴹ Δᴹ Γᴹ γ} →
      tmᴹ[ Π-[] , Π-[]ᴹ , lam-[] ] (lamᴹ bᴹ [ γᴹ ]ᵗᴹ) ≡ lamᴹ (bᴹ [ γᴹ ⁺ᴹ ]ᵗᴹ)

    Π-βᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {bᴹ : Tmᴹ (Γᴹ ▹ᴹ Aᴹ) Bᴹ b} {aᴹ : Tmᴹ Γᴹ Aᴹ a} →
      tmᴹ[ refl , refl , Π-β ] (appᴹ (lamᴹ bᴹ) aᴹ) ≡ bᴹ [ ⟨ aᴹ ⟩ᴹ ]ᵗᴹ
    Π-ηᴹ :
      {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ i A} {Bᴹ : Tyᴹ (Γᴹ ▹ᴹ Aᴹ) i B}
      {fᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f} →
      tmᴹ[ refl , refl , Π-η ] fᴹ ≡
      lamᴹ
        (tmᴹ[ sym ▹-ηᵀ , sym (tyᴹ[]-shiftr ▹-ηᵀᴹ) , refl ]
          (appᴹ (tmᴹ[ Π-[] , Π-[]ᴹ , refl ] (fᴹ [ pᴹ ]ᵗᴹ)) (varᴹ vzᴹ)))

module Ind (D : DModel ℓᶜ ℓˢ ℓᵀ ℓᵗ ℓᵛ) where
  open DModel D

\end{code}
Assuming a dependent model, the induction principle consists of five functions, one for
each sort. The ones for \AD{Con}, \AD{Sub}, \AD{Var} are defined by pattern matching, the ones for \AD{Ty} and \AD{Tm}
are postulated. We just list their types here, and provide the pattern matching definition for the induction principle for \AD{Con}.
\begin{AgdaAlign}
\begin{code}
  ⟦_⟧ᶜ       : (Γ : Con) → Conᴹ Γ
  postulate
    ⟦_⟧ᵀ     : (A : Ty Γ i) → Tyᴹ ⟦ Γ ⟧ᶜ i A
  ⟦ ◇      ⟧ᶜ = ◇ᴹ
  ⟦ Γ ▹ A  ⟧ᶜ = ⟦ Γ ⟧ᶜ ▹ᴹ ⟦ A ⟧ᵀ
  postulate
    ⟦_⟧ᵗ     : (a : Tm Γ A) → Tmᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ a
  ⟦_⟧ˢ       : (γ : Sub Δ Γ) → Subᴹ ⟦ Δ ⟧ᶜ ⟦ Γ ⟧ᶜ γ
\end{code}
\begin{code}[hide]
  postulate
    ⟦⟧-[]ᵀ : ⟦ A [ γ ]ᵀ ⟧ᵀ ≡ ⟦ A ⟧ᵀ [ ⟦ γ ⟧ˢ ]ᵀᴹ
    {-# REWRITE ⟦⟧-[]ᵀ #-}

  ⟦ p ⟧ˢ = pᴹ
  ⟦ γ ⁺ ⟧ˢ = ⟦ γ ⟧ˢ ⁺ᴹ
  ⟦ ⟨ a ⟩ ⟧ˢ = ⟨ ⟦ a ⟧ᵗ ⟩ᴹ

  postulate
    ⟦⟧-[]ᵗ : ⟦ a [ γ ]ᵗ ⟧ᵗ ≡ ⟦ a ⟧ᵗ [ ⟦ γ ⟧ˢ ]ᵗᴹ
    {-# REWRITE ⟦⟧-[]ᵗ #-}
\end{code}
\begin{code}
  ⟦_⟧ᵛ       : (x : Var Γ A) → Varᴹ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ x
\end{code}
\end{AgdaAlign}
\begin{code}[hide]
  ⟦ vz ⟧ᵛ = vzᴹ
  ⟦ vs x ⟧ᵛ = vsᴹ ⟦ x ⟧ᵛ

  postulate
    ⟦⟧-var : ⟦ var x ⟧ᵗ ≡ varᴹ ⟦ x ⟧ᵛ
    {-# REWRITE ⟦⟧-var #-}

    ⟦⟧-U : ⟦ U i ⟧ᵀ ≡ (Tyᴹ ⟦ Γ ⟧ᶜ (suc i) (U i) ∋ Uᴹ i)
    {-# REWRITE ⟦⟧-U #-}
    ⟦⟧-El : ⟦ El α ⟧ᵀ ≡ Elᴹ ⟦ α ⟧ᵗ
    {-# REWRITE ⟦⟧-El #-}
    ⟦⟧-c : ⟦ c A ⟧ᵗ ≡ cᴹ ⟦ A ⟧ᵀ
    {-# REWRITE ⟦⟧-c #-}

    ⟦⟧-Π : ⟦ Π A B ⟧ᵀ ≡ Πᴹ ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
    {-# REWRITE ⟦⟧-Π #-}
    ⟦⟧-app : ⟦ app f a ⟧ᵗ ≡ appᴹ ⟦ f ⟧ᵗ ⟦ a ⟧ᵗ
    {-# REWRITE ⟦⟧-app #-}
    ⟦⟧-lam : ⟦ lam b ⟧ᵗ ≡ lamᴹ ⟦ b ⟧ᵗ
    {-# REWRITE ⟦⟧-lam #-}

-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
\end{code}

TODO: add examples, and show what we cannot do and need alpha-norm for.
