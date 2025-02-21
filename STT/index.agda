{-# OPTIONS --rewriting #-}

{-

This formalisaton of simple type theory is using the techniques in the
paper

  Type theory in type theory with single substitutions

by Ambrus Kaposi and Szumi Xie.

It is available here: https://github.com/szumixie/single-subst

We typechecked it using Agda version 2.7.0.1 with the standard library
version 2.2.

-}

module STT.index where

import STT.SSC
import STT.SSC.SNf
import STT.SSC.Properties
import STT.SSC.StrictSub
import STT.Contextual
