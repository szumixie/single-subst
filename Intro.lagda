\section{Introduction}

The traditional way of defining
\cite{DBLP:books/daglib/0005958,DBLP:books/cu/Ha2016,Pierce:SF1,plfa22.08}
a programming language is comprised of three steps: (i) definition of
the presyntax (abstract syntax trees, ASTs) by a formal grammar; (ii)
specification of well-formedness/well-typedness relations saying which
ASTs are well-behaved; (iii) specification of rewriting/conversion
relations explaining how programs are executed. The notion of
model/semantics is then given separately, and work has to be done to
show that the above specified syntax generates a model. For example,
this was the goal of the initiality project for homotopy type theory
\cite{brunerie}.

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

When defining languages as algebraic theories, we still have to make
some choices about representing \emph{binders}: for this, several
strategies have been developed. For example, for the binding structure
of dependent types, we have categories with families (CwFs
\cite{DBLP:journals/corr/abs-1904-00827}), contextual categories
\cite{DBLP:journals/apal/Cartmell86}, natural models
\cite{DBLP:journals/mscs/Awodey18}, C-systems and B-systems
\cite{ahrens_emmenegger_north_rijke_2023}. We can abstract over these
strategies and define our language as a second-order generalised
algebraic theory \cite{DBLP:journals/corr/abs-1904-04097}, but to
state initiality of our syntax, at some point we need to turn it into
a first-order algebraic theory \cite{DBLP:conf/fscd/BocquetKS23}. With
the exception of B-systems, the above descriptions are based on
parallel substitutions. 

In this paper we introduce a new single substitution calculus which
can be seen as a minimalistic variant of B-systems. We illustrate its
usage through the definition of a type theory with dependent function
space and a hierarchy of universes. We aim for accessibility: this
paper can be seen as a tutorial introduction to the syntax of type
theory inside type theory. All the operations and equations are
well-motivated and provide a minimalistic description of the syntax of
type theory. It is minimalistic in the sense that the syntax is
isomorphic to the CwF-syntax, but there are more models. This is
analogous to the relationship of combinatory logic and lambda
calculus: the syntaxes are isomorphic, but the former has more models
\cite{DBLP:conf/fscd/AltenkirchKSV23}.

\subparagraph*{Structure of the paper.}  Formalisation, Syntax,
$\alpha$-normalisation (a method to prove stuff about the syntax),
isomorphism to CwFs.

\subparagraph*{Metatheory and formalisation.} The source code of this
paper comprises of several literate Agda files, everything is
formalised.  We use Agda with postulated QIITs using rewrite rules
\cite{DBLP:conf/types/Cockx19}.
