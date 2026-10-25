/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit.Part2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison
open Filter MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation

noncomputable section

def wiredTruncationErrorEvent (d R : Nat) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  wiredTruncatedInfiniteEvent d R x \ clusterInfiniteEvent d x

end
end StatMech.FK
