{-# OPTIONS
  --without-K
  --prop
  --rewriting
  --confluence-check
#-}

module TT.SSC.Standard where

open import TT.Lib
open import TT.SSC.Ind

open DM

sorts : Sorts
Conᴹ sorts = {!λ _ → !}
Subᴹ sorts = {!!}
Tyᴹ  sorts = {!!}
Tmᴹ  sorts = {!!}
