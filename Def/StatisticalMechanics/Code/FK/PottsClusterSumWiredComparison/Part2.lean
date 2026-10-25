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
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison.Part2
open Filter MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation

noncomputable section

def pottsSpinTruncationDisagreement
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (R : Nat)
    (sites : Finset (Site d)) :
    Set (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
  ⋃ x ∈ (sites : Set (Site d)),
    {input | pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d R input.1) input.2 x ≠
      pottsClusterSumSpin boundaryColor input.1 input.2 x}

end
end StatMech.FK
