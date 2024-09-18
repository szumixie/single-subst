## Contents of this repository

* CPP [submission](https://bitbucket.org/akaposi/single/raw/no-var/cpp/p.pdf) titled "Type theory in type theory with single substitutions" by Ambrus Kaposi and Szumi Xie.
* TYPES [abstract](types_2024/abstract.tex) titled "Type theory in type theory using single substitutions" by Ambrus Kaposi and Szumi Xie.
* Agda formalisation:
    * Simple type theory:
        * [Syntax](STT/SSC.agda)
        * [Admissible operations](STT/SSC)
        * [Equivalence of SSC and simply typed CwF contextual models](STT/Contextual.agda) (this relies on having function space)
    * Type theory using parallel substitutions (CwF):
        * [TT.CwF.Syntax](TT/CwF/Syntax.agda) Syntax
        * [TT.CwF.Ind](TT/CwF/Ind.agda) Induction principle
        * [TT.CwF.Standard](TT/CwF/Standard.agda) Standard model
    * Type theory using single substitutions (SSC):
        * [TT.SSC.Syntax](TT/SSC/Syntax.agda) Syntax
        * [TT.SSC.Ind](TT/SSC/Ind.agda) Induction principle
        * [TT.SSC.Standard](TT/SSC/Standard.agda) Standard model
        * [TT.SSC.AlphaNorm](TT/SSC/AlphaNorm.agda) Alpha-normalisation
        * [TT.SSC.Path](TT/SSC/Path.agda) Reflexive-transitive closure of single substitutions
        * [TT.SSC.Tel](TT/SSC/Tel.agda) Telescopes
        * [TT.SSC.Lift](TT/SSC/Lift.agda) Lifting the equations for variables to terms and types
        * [TT.SSC.Parallel](TT/SSC/Parallel.agda) Rules of the parallel substitution calculus
    * Translations
        * [TT.SSC-CwF](TT/SSC-CwF.agda) SSC to CwF
        * [TT.CwF-SSC](TT/CwF-SSC.agda) CwF to SSC
        * [TT.CwF-SSC-CwF](TT/CwF-SSC-CwF.agda) Roundtrip CwF -> SSC -> CwF
        * [TT.SSC-CwF-SSC](TT/SSC-CwF-SSC.agda) Roundtrip SSC -> CwF -> SSC
        * [TT.Isomorphism](TT/Isomorphism.agda) Putting the above four together
