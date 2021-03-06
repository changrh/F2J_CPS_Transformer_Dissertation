{- |
Module      :  CPS.LamSrc
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Johnny.Lin
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the continuation passing style of FCore. For
more information, please refer to the paper on wiki.
-}

module CPS.LamSrc where

type Paramter     = String
type TypeVarName  = String
type VarName      = String
type ClassName    = String
type Name         = String
