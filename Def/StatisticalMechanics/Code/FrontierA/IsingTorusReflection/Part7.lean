/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusLowerGradientFeature (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) : Real :=
  isingTorusEmbedLower i u e.1 -
    isingTorusEmbedLower i u (e.1 + isingTorusStep e.2)

def isingTorusUpperGradientFeature (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) : Real :=
  -(isingTorusEmbedUpper i u e.1 -
    isingTorusEmbedUpper i u (e.1 + isingTorusStep e.2))


def isingTorusBoundaryFeature (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) : Real :=
  if isingTorusInLowerHalf i e.1 ↔
      isingTorusInLowerHalf i (e.1 + isingTorusStep e.2)
    then 0 else isingTorusLowerGradientFeature i u e

end StatMech.FrontierA
