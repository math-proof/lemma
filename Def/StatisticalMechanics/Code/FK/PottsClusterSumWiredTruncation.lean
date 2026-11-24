module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part9
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

open Lattice Percolation

noncomputable section

def wiredTruncationEdge (d n : Nat)
    (omega : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  extendWiredEdge d n (boxRestrict d n omega)

end
end StatMech.FK
