## Contents of this repository

* TYPES [abstract](types_2024/abstract.tex) titled "Type theory in type theory using single substitutions" by Ambrus Kaposi and Szumi Xie.
* Agda formalisation of single substitution calculi (SSC)
    * Simple type theory: [Syntax](STT/SSC.agda), [Admissible operations](STT/SSC), [Equivalence of SSC and simply typed CwF contextual models](STT/Contextual.agda) (this relies on having function space)
    * Type theory: [Syntax](TT/SSC/Syntax.agda), [Induction principle](TT/SSC/Ind.agda), [Alpha-normalisation](TT/SSC/AlphaNorm.agda), [Reflexive-transitive closure of single substitutions](TT/SSC/Path.agda), [Telescopes](TT/SSC/Tel.agda), [Lifting the equations for variables to terms and types](TT/SSC/Lift.agda), [Rules of the parallel substitution calculus](TT/SSC/Parallel.agda)
