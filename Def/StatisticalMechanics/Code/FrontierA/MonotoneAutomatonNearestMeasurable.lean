/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestMeasurable
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairNearestComparisonEvent (x y z x' y' : Site d) :
    Set (PairSiteConfig d) :=
  if l1dist d y z ≤ l1dist d x' y' then Set.univ
  else {omega | x' ∉ pairHighCluster omega x} ∪
    {omega | y' ∉ pairLowInfiniteVertices omega}

end StatMech.FrontierA
