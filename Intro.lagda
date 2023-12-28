\begin{code}[hide]
{-# OPTIONS --with-K --rewriting #-}

module Intro where

open import Lib hiding (ℕ; zero; suc)

private variable
  ℓ : Level
\end{code}

\section{Introduction}

What is type theory? This term can refer to formal systems (languages,
type systems, type theories) or to the field of study of type
theories. In this paper, we will give an answer to this question in
the form of a concrete formal system. We aim for simplicity and ease
of understanding: we only require a working knowledge of Agda, a
functional programming language which is an implementation of type
theory. Our metatheory in which this paper is written is thus type
theory, and everything is formalised in Agda.

The traditional way of defining a programming language formally
\cite{DBLP:books/daglib/0005958,DBLP:books/cu/Ha2016,Pierce:SF1,plfa22.08}
is comprised of three steps: (i) definition of the presyntax
(abstract syntax trees, ASTs) as a formal grammar; (ii) specification of
well-formedness/well-typedness relations saying which ASTs are
well-behaved; (iii) specification of rewriting/conversion relations
explaining how programs are executed. Instead of following this route,
we use the intrinsic approach
\cite{DBLP:conf/csl/AltenkirchR99,DBLP:conf/popl/AltenkirchK16}: (i)
we define ASTs as an inductive type instead of production rules of a
grammar; (ii) terms are indexed by (object theoretic) types, thus only
allowing ASTs to be plugged together in well-typed ways; (iii) terms
are quotiented by conversion rules, making convertible terms
equal. Inductive types which allow such mutual indexing and
quotienting are called quotient inductive-inductive types (QIITs
\cite{DBLP:journals/pacmpl/KaposiKA19}). As Agda does not support them
directly, we postulate their constructors and induction principle and add the
computation rules using rewrite rules \cite{DBLP:conf/types/Cockx19}.

A QIIT is also the initial algebra/model of a generalised algebraic
theory (GAT \cite{DBLP:journals/apal/Cartmell86}). The induction principle of
the QIIT is equivalent to having a unique morphism into any model
\cite{DBLP:journals/pacmpl/KaposiKA19}. There are several ways to
define type theory as a GAT: categories with families (CwFs
\cite{DBLP:journals/corr/abs-1904-00827}), contextual categories
\cite{DBLP:journals/apal/Cartmell86}, natural models
\cite{DBLP:journals/mscs/Awodey18}, C-systems and B-systems
\cite{ahrens_emmenegger_north_rijke_2023}. When extracting a QIIT from
a GAT, with the exception of B-systems, we obtain parallel
substitution calculi. Like B-systems, in this paper we define type
theory using \emph{single substitutions}. Our definition is simpler
than B-systems, but it is closely related to it. It is a minimalistic
presentation where every operation and equation is well-motivated (see
Section \ref{sec:SSC}). However, when we want to use our syntax (for
example, if we want to prove canonicity or normalisation for our
theory), it is much more convenient to use parallel substitution
calculi such as CwFs. We first show how to get rid of explicit
substitutions from the syntax using the technique of
$\alpha$-normalisation (Section \ref{sec:alpha}). Then we show how to
derive the rules of a CwF from our syntax (Section
\ref{sec:cwf}). Finally, we show that our syntax is isomorphic to the
CwF-style syntax (Section \ref{sec:iso}). We list related work and
conclude in Section \ref{sec:conclusion}.

Our main contribution is the novel definition of a minimalistic single
substitution calculus, justified by showing its equivalence to CwFs.

\subsection{Metatheory and formalisation}
\label{sec:metatheory}

The source code of this
paper comprises of several literate Agda files, everything is
formalised. We use Agda with QIITs postulated using rewrite rules
\cite{DBLP:conf/types/Cockx19}. We illustrate this technique by defining natural
numbers in two different ways. The first way is the usual one: we declare
natural numbers as an inductive datatype:
\begin{code}[hide]
module NatExample where
\end{code}
\begin{code}
  data ℕ  : Set where
    zero  : ℕ
    suc   : ℕ → ℕ
\end{code}
Now we can define functions such as addition by pattern matching:
\begin{code}
  add : ℕ → ℕ → ℕ
  add zero     n = n
  add (suc m)  n = suc (add m n)
\end{code}
The alternative is to postulate the type and its constructors:
\begin{code}[hide]
module NatExamplePostulated where
\end{code}
\begin{code}
  postulate
    ℕ     : Set
    zero  : ℕ
    suc   : ℕ → ℕ
\end{code}
\begin{code}[hide]
  private variable
    n : ℕ
\end{code}
Then we define dependent (displayed) natural models, which collect the
motive \AR{ℕᴹ} and methods \AR{zeroᴹ}, \AR{sucᴹ} of the induction principle (dependent eliminator), one for each constructor.
\begin{code}
  record DModel ℓ : Set (ℓ.suc ℓ) where
    field
      ℕᴹ     : ℕ → Set ℓ
      zeroᴹ  : ℕᴹ zero
      sucᴹ   : ℕᴹ n → ℕᴹ (suc n)
\end{code}
Finally, we say that we can eliminate into any dependent model, adding the computation rules for the induction principle \AD{⟦\_⟧} as rewrite rules.
\begin{code}
  module Ind (D : DModel ℓ) where
    open DModel D
    postulate
      ⟦_⟧      : (n : ℕ) → ℕᴹ n
      ⟦⟧-zero  : ⟦ zero   ⟧ ≡ zeroᴹ
      ⟦⟧-suc   : ⟦ suc n  ⟧ ≡ sucᴹ ⟦ n ⟧
      {-# REWRITE ⟦⟧-zero ⟦⟧-suc #-}
\end{code}
We define addition via elimination into a dependent model:
\begin{code}
  add : ℕ → ℕ → ℕ
  add m n = ⟦ m ⟧
    where
      D : DModel ℓ.zero
      D = record { ℕᴹ = λ _ → ℕ ; zeroᴹ = n ; sucᴹ = suc }
      open Ind D
\end{code}
Actually, this model is not dependent, as \AD{ℕᴹ} is defined as the constant
\AD{ℕ} family. The method \AF{zeroᴹ} expresses that when addition is called on \AD{m = zero}, it returns \AD{n}. The method \AF{sucᴹ} expresses that addition on \AD{m = suc m'} makes a recursive call and then puts a \AD{suc} on top.

The two versions of \AD{ℕ} allow us to define the same functions, up to translating pattern matching definitions to eliminators \cite{DBLP:phd/basesearch/Cockx17}. We prefer the datatype definition because pattern matching is easier to write and read. However, Agda does not allow equality constructors for inductive types, so when defining quotient inductive types, we use the latter method.

We use uniqueness of identity proofs, and the universe of strict propositions \AD{Prop} \cite{DBLP:journals/pacmpl/GilbertCST19}.

We use the ``variable'' feature of Agda for readability.

Sometimes we use the phrase ``set'' to refer to metatheoretic types, which aligns well with Agda's notation \AD{Set} for the universe of types.

We write element notation for equalities. We define separate transport
operations for families.
