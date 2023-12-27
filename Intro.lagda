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
directly, we postulate their constructors and eliminators and add the
computation rules using rewrite rules \cite{DBLP:conf/types/Cockx19}.

A QIIT is also the initial algebra/model of a generalised algebraic
theory (GAT \cite{DBLP:journals/apal/Cartmell86}). The eliminator of
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
substitution calculus. We justify it by showing its equivalence with
CwFs.

\subparagraph*{Metatheory and formalisation.} The source code of this
paper comprises of several literate Agda files, everything is
formalised. We use Agda with postulated QIITs using rewrite rules
\cite{DBLP:conf/types/Cockx19}.
