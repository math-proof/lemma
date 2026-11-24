module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
public import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part5
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

def wiredTruncatedInfiniteEvent (d R : Nat) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | (cluster d (wiredTruncationEdge d R omega) x).Infinite}

end
end StatMech.FK
