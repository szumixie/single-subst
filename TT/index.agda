{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

{-
This is the formalisaton for the paper

  Type theory in type theory with single substitutions

by Ambrus Kaposi and Szumi Xie.

It is available here: https://github.com/szumixie/single-subst

We typechecked it using Agda version 2.7.0.1. No library is needed.
-}

module TT.index where

import TT.CwF.Syntax       -- CwF-based syntax for a theory with Π and Coquand universe
import TT.CwF.Standard     -- its standard model

import TT.SSC.Syntax       -- the single substitution syntax for the same theory
import TT.SSC.Standard     -- its standard model
import TT.SSC.AlphaNorm    -- notion of α-normal forms (terms without explicit substitutions)
import TT.SSC.Lift         -- admissible equations
import TT.SSC.Parallel     -- all the CwF rules hold in the single substitution syntax

import TT.Isomorphism      -- the single substitution and CwF-based syntaxes are isomorphic
