\section{Related work and conclusion}
\label{sec:conclusion}

In this paper we introduced a new single substitution calculus which
can be seen as a minimalistic variant of B-systems. We illustrate its
usage through the definition of a type theory with dependent function
space and a hierarchy of universes. We aim for accessibility: this
paper can be seen as a tutorial introduction to the syntax of type
theory inside type theory. All the operations and equations are
well-motivated and provide a minimalistic description of the syntax of
type theory. It is minimalistic in the sense that the syntax is
isomorphic to the CwF-syntax, but there are more models. 

The relationship of our single substitution calculus and the CwF-based
theory is similar to that of combinatory logic and lambda calculus
\cite{DBLP:conf/fscd/AltenkirchKSV23}. Combinatory logic has more
models than lambda calculus, but the syntaxes are
isomorphic. Similarly, the single substitution calculus has more
models, but the syntaxes are isomorphic.

SSC was used in the 90s for simple type theories, ask Hugo for references.

A more abstract, higher level description of a language is simply
stating that a language is an algebraic theory: the terms of the
language are given by a sort of the theory, the different term formers
are operations, and the conversion relation is specified by the
equations. Such a description contains less information than the
traditional one, for example, conversion is not oriented, so it is not
clear how to turn it into a rewriting relation; we cannot choose how
much annotations we add to terms, they are always fully
annotated. this is similar to how asts contain less information than
strings, for example, the bracket-removal strategy is not encoded in
asts. the algebraic description automatically induces a notion of
model and the existence of an initial model
\cite{DBLP:journals/pacmpl/KaposiKA19} which we call the syntax. The
algebraic approach is especially natural for languages with dependent
types where typing and conversion have to be specified mutually
\cite{DBLP:conf/popl/AltenkirchK16}.

QIIT is nice because syntax and semantics are given together. The
notion of model/semantics is traditionally given separately, and work
has to be done to show that the above specified syntax generates a
model. For example, this was the goal of the initiality project for
homotopy type theory \cite{brunerie}. Maybe list work on type theory
using QIITs, see TYPES mailing list.

We can abstract over these strategies and define our language as a
second-order generalised algebraic theory
\cite{DBLP:journals/corr/abs-1904-04097}, but to state initiality of
our syntax, at some point we need to turn it into a first-order
algebraic theory \cite{DBLP:conf/fscd/BocquetKS23}.

We conjecture that any SOGAT can be turned into an SSC.
