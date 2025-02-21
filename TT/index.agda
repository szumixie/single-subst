{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.index where

import TT.CwF.Syntax
import TT.CwF.Standard

import TT.SSC.Syntax
import TT.SSC.Standard
import TT.SSC.AlphaNorm
import TT.SSC.Lift
import TT.SSC.Parallel

import TT.Isomorphism
