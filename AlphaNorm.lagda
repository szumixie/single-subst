\section{$\alpha$-normalisation}
\label{sec:alpha}

Intrinsic syntax for type theory has explicit substitutions, which
makes it hard to prove properties of the syntax by structural
induction, as there is an extra case for substituted terms. In
contrast, in extrinsic syntax substitution is defined recursively, and
structural induction does not need to mention substitution. To
alleviate this disadvantage, we use $\alpha$-normalisation which
compute substitutions, and provides a nice induction principle. In
this section we state such an induction principle, and use it to
prove some equations about our minimalistic syntax.

% Nf : ∀ Γ A → Tm Γ A → Set
% all constructors (indexed over Tm), but no _[_]
% an equation: (u v : Nf Γ A t) → u = v  (prop.truncation)

% we prove normalisation into this by defining _[_]* : NTm → NSub →
% NTm, and use this to define a model of normal forms

% the induction principle:
% P : Tm Γ A → Set
% we define P' : Σ Tm Nf → Set by P ∘ π₁, and prove P' by induction on Nf.

