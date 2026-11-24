module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
public import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part4
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

def centeredMarkedBoundaryMass (d : Nat) (x : Site d) (n : Nat)
    (p q : Real) : Real :=
  wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
    (boxMarkedVertex d n x)

end
end StatMech.FK
