/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

noncomputable section

noncomputable def wiredTruncatedPottsClusterSumSpinProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (n : Nat) : ProbabilityMeasure (PottsConfig d q) :=
  (pottsClusterFactorInputProbabilityMeasure edgeMeasure).map
    (measurable_pottsClusterSumSpin_wiredTruncationEdge
      boundaryColor n).aemeasurable


end
end StatMech.FK
